import Solution.SHA256.SHA256Round
import Solution.SHA256.FusedAdders
import Solution.SHA256.PackedCh
import Solution.SHA256.PackedChRow
import Solution.SHA256.PackedMaj
import Solution.SHA256.PackedMajRow
import Solution.SHA256.Ch32Theorems
import Challenge.Instances.SHA256.Interface
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)]

open Utils.Bits (fieldFromBits fieldFromBitsExpr)
open RPShared

variable [Fact (p > 2^76)]

/-! # The round-pair gadget -/
namespace SHA256RoundPair

open RPShared

structure Inputs (F : Type) where
  state : SHA256State F
  k0 : fields 32 F
  w0 : fields 32 F
  k1 : fields 32 F
  w1 : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let a := input.state[0]; let b := input.state[1]; let c := input.state[2]; let d := input.state[3]
  let e := input.state[4]; let f := input.state[5]; let g := input.state[6]; let h := input.state[7]
  let k0 := input.k0; let w0 := input.w0; let k1 := input.k1; let w1 := input.w1
  let sig1_t ← UpperSigma1.circuit e
  let sig0_t ← UpperSigma0.circuit a
  let new_e_t ← witnessVector 32 fun env =>
    RPShared.witBits (evalBitsNat env d + evalBitsNat env h + evalBitsNat env sig1_t
      + Specs.SHA256.Ch (evalBitsNat env e) (evalBitsNat env f) (evalBitsNat env g)
      + evalBitsNat env k0 + evalBitsNat env w0)
  let new_a_t ← witnessVector 32 fun env =>
    RPShared.witBits (evalBitsNat env new_e_t + evalBitsNat env sig0_t
      + Specs.SHA256.Maj (evalBitsNat env a) (evalBitsNat env b) (evalBitsNat env c)
      + (2^32 - 1 - evalBitsNat env d) + 1)
  BoolVec32.circuit new_e_t
  BoolVec32.circuit new_a_t
  let sig1_tp ← UpperSigma1.circuit new_e_t
  let sig0_tp ← UpperSigma0.circuit new_a_t
  let new_e_tp ← witnessVector 32 fun env =>
    RPShared.witBits (evalBitsNat env c + evalBitsNat env g + evalBitsNat env sig1_tp
      + Specs.SHA256.Ch (evalBitsNat env new_e_t) (evalBitsNat env e) (evalBitsNat env f)
      + evalBitsNat env k1 + evalBitsNat env w1)
  let new_a_tp ← witnessVector 32 fun env =>
    RPShared.witBits (evalBitsNat env new_e_tp + evalBitsNat env sig0_tp
      + Specs.SHA256.Maj (evalBitsNat env new_a_t) (evalBitsNat env a) (evalBitsNat env b)
      + (2^32 - 1 - evalBitsNat env c) + 1)
  BoolVec32.circuit new_e_tp
  BoolVec32.circuit new_a_tp
  let zch ← PackedCh.circuit ⟨e, f, g, new_e_t⟩
  let zmaj ← PackedMaj.circuit ⟨a, b, c, new_a_t⟩
  FusedEAdder.circuit ⟨new_e_t, new_e_tp, zch, e, f, g, sig1_t, sig1_tp, d, h, k0, w0, c, k1, w1⟩
  FusedAAdder.circuit ⟨new_a_t, new_a_tp, new_e_t, new_e_tp, sig0_t, sig0_tp, zmaj, a, b, c, d⟩
  return #v[new_a_tp, new_a_t, a, b, new_e_tp, new_e_t, e, f]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
    Normalized input.k0 ∧ Normalized input.w0 ∧ Normalized input.k1 ∧ Normalized input.w1

def specFn (sv : Vector ℕ 8) (k0 w0 k1 w1 : ℕ) : Vector ℕ 8 :=
  Specs.SHA256.sha256Round (Specs.SHA256.sha256Round sv k0 w0) k1 w1

@[simp] lemma specFn_eq (sv : Vector ℕ 8) (k0 w0 k1 w1 : ℕ) :
    specFn sv k0 w0 k1 w1 =
      Specs.SHA256.sha256Round (Specs.SHA256.sha256Round sv k0 w0) k1 w1 := rfl

attribute [irreducible] specFn

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits = specFn (input.state.map valueBits)
      (valueBits input.k0) (valueBits input.w0) (valueBits input.k1) (valueBits input.w1)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

lemma ll_sig1 (x : Var (fields 32) (F p)) : UpperSigma1.circuit.localLength x = 32 := by
  simp only [circuit_norm, UpperSigma1.circuit, UpperSigma1.elaborated]
lemma ll_sig0 (x : Var (fields 32) (F p)) : UpperSigma0.circuit.localLength x = 32 := by
  simp only [circuit_norm, UpperSigma0.circuit, UpperSigma0.elaborated]
lemma ll_packch (x : Var PackedCh.Inputs (F p)) : PackedCh.circuit.localLength x = 32 := by
  simp only [circuit_norm, PackedCh.circuit, PackedCh.elaborated]
lemma ll_packmaj (x : Var PackedMaj.Inputs (F p)) : (PackedMaj.circuit (p := p)).localLength x = 32 := by
  simp only [circuit_norm, PackedMaj.circuit, PackedMaj.elaborated]
lemma ll_bool (x : Var (fields 32) (F p)) : (BoolVec32.circuit (p:=p)).localLength x = 0 := by
  simp only [circuit_norm, BoolVec32.circuit, BoolVec32.main]
lemma ll_fe [Fact (p > 2^76)] (x : Var FusedEAdder.Inputs (F p)) : (FusedEAdder.circuit (p:=p)).localLength x = 5 := by
  simp only [circuit_norm, FusedEAdder.circuit, FusedEAdder.main]
lemma ll_fa [Fact (p > 2^76)] (x : Var FusedAAdder.Inputs (F p)) : (FusedAAdder.circuit (p:=p)).localLength x = 3 := by
  simp only [circuit_norm, FusedAAdder.circuit, FusedAAdder.main]

set_option maxHeartbeats 4000000 in
private lemma spec_value_eq (env : Environment (F p)) (i₀ : ℕ)
    (input_state : SHA256State (F p)) (input_var_state : SHA256State (Expression (F p)))
    (input_k0 input_w0 input_k1 input_w1 : fields 32 (F p))
    (NEt NAt NEtp NAtp : fields 32 (F p))
    (hmNEt : Vector.map (Expression.eval env) (Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + i }) = NEt)
    (hmNAt : Vector.map (Expression.eval env) (Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + 32 + i }) = NAt)
    (hmNEtp : Vector.map (Expression.eval env) (Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + i }) = NEtp)
    (hmNAtp : Vector.map (Expression.eval env) (Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + 32 + i }) = NAtp)
    (hvk : ∀ (k : ℕ) (hk : k < 8), valueBits (Vector.map (Expression.eval env) (input_var_state[k]'hk)) = valueBits (input_state[k]'hk))
    (h_state_norm : ∀ (i : Fin 8), Normalized input_state[↑i])
    (h_eval : ∀ (i : ℕ) (hi : i < 8), Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi)
    (hnet_norm : Normalized NEt) (hnat_norm : Normalized NAt) (hnetp_norm : Normalized NEtp) (hnatp_norm : Normalized NAtp)
    (hne_val : valueBits NEt = _root_.add32 (valueBits (input_state[3]'(by norm_num))) (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num))) (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num))))) (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num))))) (valueBits input_k0)) (valueBits input_w0)))
    (hnat_val : valueBits NAt = _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num))) (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num))))) (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num))))) (valueBits input_k0)) (valueBits input_w0)) (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits (input_state[0]'(by norm_num)))) (Specs.SHA256.Maj (valueBits (input_state[0]'(by norm_num))) (valueBits (input_state[1]'(by norm_num))) (valueBits (input_state[2]'(by norm_num))))))
    (hnetp_val : valueBits NEtp = _root_.add32 (valueBits (input_state[2]'(by norm_num))) (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[6]'(by norm_num))) (Specs.SHA256.upperSigma1 (valueBits NEt))) (Specs.SHA256.Ch (valueBits NEt) (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))))) (valueBits input_k1)) (valueBits input_w1)))
    (hnatp_val : valueBits NAtp = _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[6]'(by norm_num))) (Specs.SHA256.upperSigma1 (valueBits NEt))) (Specs.SHA256.Ch (valueBits NEt) (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))))) (valueBits input_k1)) (valueBits input_w1)) (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits NAt)) (Specs.SHA256.Maj (valueBits NAt) (valueBits (input_state[0]'(by norm_num))) (valueBits (input_state[1]'(by norm_num)))))) :
    Vector.map valueBits (eval env (#v[Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + 32 + i },
        Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + 32 + i }, input_var_state[0], input_var_state[1],
        Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + i },
        Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + i }, input_var_state[4], input_var_state[5]] : SHA256State (Expression (F p))))
      = specFn (Vector.map valueBits input_state)
          (valueBits input_k0) (valueBits input_w0) (valueBits input_k1) (valueBits input_w1)
    ∧ ∀ i : Fin 8, Normalized (eval env (#v[Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + 32 + i },
        Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + 32 + i }, input_var_state[0], input_var_state[1],
        Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + i },
        Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + i }, input_var_state[4], input_var_state[5]] : SHA256State (Expression (F p))))[i.val] := by
  refine ⟨?_, ?_⟩
  · rw [specFn_eq]
    have inner : Specs.SHA256.sha256Round (Vector.map valueBits input_state) (valueBits input_k0) (valueBits input_w0)
        = #v[valueBits NAt, valueBits (input_state[0]'(by norm_num)), valueBits (input_state[1]'(by norm_num)), valueBits (input_state[2]'(by norm_num)),
             valueBits NEt, valueBits (input_state[4]'(by norm_num)), valueBits (input_state[5]'(by norm_num)), valueBits (input_state[6]'(by norm_num))] := by
      simp only [Specs.SHA256.sha256Round, Vector.getElem_map, hnat_val, hne_val]
    rw [inner]
    simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, circuit_norm]
    simp only [Specs.SHA256.sha256Round, Vector.getElem_map, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hmNAtp, hmNAt, hmNEtp, hmNEt, hvk 0 (by norm_num), hvk 1 (by norm_num),
      hvk 4 (by norm_num), hvk 5 (by norm_num)]
    rw [hnatp_val, hnetp_val]
  · intro i
    fin_cases i <;>
      simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
        circuit_norm, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · rw [hmNAtp]; exact hnatp_norm
    · rw [hmNAt]; exact hnat_norm
    · rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
    · rw [h_eval 1 (by norm_num)]; exact h_state_norm 1
    · rw [hmNEtp]; exact hnetp_norm
    · rw [hmNEt]; exact hnet_norm
    · rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
    · rw [h_eval 5 (by norm_num)]; exact h_state_norm 5

variable [Fact (p > 2^76)]

lemma us1_cwr : (UpperSigma1.circuit (p := p)).channelsWithRequirements = [] := rfl
lemma us0_cwr : (UpperSigma0.circuit (p := p)).channelsWithRequirements = [] := rfl
lemma pch_cwr : (PackedCh.circuit (p := p)).channelsWithRequirements = [] := rfl
lemma pmaj_cwr : (PackedMaj.circuit (p := p)).channelsWithRequirements = [] := rfl
lemma bool_cwr : (BoolVec32.circuit (p := p)).channelsWithRequirements = [] := rfl
lemma fe_cwr : (FusedEAdder.circuit (p := p)).channelsWithRequirements = [] := rfl
lemma fa_cwr : (FusedAAdder.circuit (p := p)).channelsWithRequirements = [] := rfl

set_option maxHeartbeats 20000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, UpperSigma1.Spec, UpperSigma1.Assumptions,
    UpperSigma0.Spec, UpperSigma0.Assumptions, PackedMaj.Spec, PackedMaj.Assumptions,
    PackedCh.Spec, PackedCh.Assumptions, BoolVec32.Spec, BoolVec32.Assumptions,
    FusedEAdder.Spec, FusedEAdder.Assumptions, FusedAAdder.Spec, FusedAAdder.Assumptions]
  obtain ⟨h_state_norm, h_k0n, h_w0n, h_k1n, h_w1n⟩ := h_assumptions
  obtain ⟨h_is, h_ik0, h_iw0, h_ik1, h_iw1⟩ := h_input
  simp only [ll_sig1, ll_sig0, ll_packch, ll_packmaj, ll_bool, ll_fe, ll_fa, Nat.mul_zero, Nat.add_zero] at h_holds ⊢
  obtain ⟨c_sig1, c_sig0, c_bnE, c_bnA, c_sig1p, c_sig0p, c_bnEp, c_bnAp, c_packch, c_packmaj, c_fe, c_fa⟩ := h_holds
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_is] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]; exact h
  have n0 : Normalized (Vector.map (Expression.eval env) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
  have n1 : Normalized (Vector.map (Expression.eval env) input_var_state[1]) := by
    rw [h_eval 1 (by norm_num)]; exact h_state_norm 1
  have n2 : Normalized (Vector.map (Expression.eval env) input_var_state[2]) := by
    rw [h_eval 2 (by norm_num)]; exact h_state_norm 2
  have n4 : Normalized (Vector.map (Expression.eval env) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
  have n5 : Normalized (Vector.map (Expression.eval env) input_var_state[5]) := by
    rw [h_eval 5 (by norm_num)]; exact h_state_norm 5
  have n6 : Normalized (Vector.map (Expression.eval env) input_var_state[6]) := by
    rw [h_eval 6 (by norm_num)]; exact h_state_norm 6
  have hmNEt := mapRange_eval env (i₀ + 32 + 32)
  have hmNAt := mapRange_eval env (i₀ + 32 + 32 + 32)
  have hmNEtp := mapRange_eval env (i₀ + 128 + 32 + 32)
  have hmNAtp := mapRange_eval env (i₀ + 128 + 32 + 32 + 32)
  set NEt : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 32 + 32 + i.val) with hNEt
  set NAt : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 32 + 32 + 32 + i.val) with hNAt
  set NEtp : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 128 + 32 + 32 + i.val) with hNEtp
  set NAtp : fields 32 (F p) := Vector.ofFn fun i : Fin 32 => env.get (i₀ + 128 + 32 + 32 + 32 + i.val) with hNAtp
  have hnet_norm : Normalized NEt := by have := c_bnE trivial; rwa [hmNEt] at this
  have hnat_norm : Normalized NAt := by have := c_bnA trivial; rwa [hmNAt] at this
  have hnetp_norm : Normalized NEtp := by have := c_bnEp trivial; rwa [hmNEtp] at this
  have hnatp_norm : Normalized NAtp := by have := c_bnAp trivial; rwa [hmNAtp] at this
  -- subcircuit specs
  have s_sig1 := c_sig1 n4
  have s_sig0 := c_sig0 n0
  have s_sig1p := c_sig1p (by rw [hmNEt]; exact hnet_norm)
  have s_sig0p := c_sig0p (by rw [hmNAt]; exact hnat_norm)
  have s_packch := c_packch ⟨n4, n5, n6, by rw [hmNEt]; exact hnet_norm⟩
  have s_packmaj := c_packmaj ⟨n0, n1, n2, by rw [hmNAt]; exact hnat_norm⟩
  simp only [UpperSigma1.Spec, UpperSigma0.Spec, PackedCh.Spec, PackedMaj.Spec] at s_sig1 s_sig0 s_sig1p s_sig0p s_packch s_packmaj
  have hvk : ∀ (k : ℕ) (hk : k < 8),
      valueBits (Vector.map (Expression.eval env) (input_var_state[k]'hk)) = valueBits (input_state[k]'hk) :=
    fun k hk => congrArg valueBits (h_eval k hk)
  have hvk0 := congrArg valueBits h_ik0
  have hvk1 := congrArg valueBits h_iw0
  have hvk2 := congrArg valueBits h_ik1
  have hvk3 := congrArg valueBits h_iw1
  have hmv_ne : valueBits (Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + i })) = valueBits NEt := congrArg valueBits hmNEt
  have hmv_na : valueBits (Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => var { index := i₀ + 32 + 32 + 32 + i })) = valueBits NAt := congrArg valueBits hmNAt
  have hmv_netp : valueBits (Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + i })) = valueBits NEtp := congrArg valueBits hmNEtp
  have hmv_natp : valueBits (Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => var { index := i₀ + 128 + 32 + 32 + 32 + i })) = valueBits NAtp := congrArg valueBits hmNAtp
  -- FusedEAdder spec
  have s_fe := c_fe ⟨by rw [hmNEt]; exact hnet_norm, by rw [hmNEtp]; exact hnetp_norm,
    n4, n5, n6, s_sig1.2, s_sig1p.2,
    by rw [h_eval 3 (by norm_num)]; exact h_state_norm 3,
    by rw [h_eval 7 (by norm_num)]; exact h_state_norm 7,
    h_k0n, h_w0n,
    by rw [h_eval 2 (by norm_num)]; exact h_state_norm 2,
    h_k1n, h_w1n,
    by intro j; exact s_packch j⟩
  -- FusedAAdder spec (4-term new_a lanes derived from the materialized new_e; the two
  -- rounds' Maj arrive packed in `zmaj`, pinned by the PackedMaj two-row spec `s_packmaj`)
  have s_fa := c_fa ⟨by rw [hmNAt]; exact hnat_norm, by rw [hmNAtp]; exact hnatp_norm,
    by rw [hmNEt]; exact hnet_norm, by rw [hmNEtp]; exact hnetp_norm,
    s_sig0.2, s_sig0p.2,
    n0, n1, n2,
    by rw [h_eval 3 (by norm_num)]; exact h_state_norm 3,
    by intro j; exact s_packmaj j⟩
  simp only [FusedEAdder.circuit, FusedEAdder.Spec, FusedAAdder.circuit, FusedAAdder.Spec] at s_fe s_fa
  have hd3_lt : valueBits (input_state[3]'(by norm_num)) < 2^32 :=
    valueBits_lt_two_pow _ (h_state_norm 3)
  have hd2_lt : valueBits (input_state[2]'(by norm_num)) < 2^32 :=
    valueBits_lt_two_pow _ (h_state_norm 2)
  -- massage into add32 form
  have hne_val : valueBits NEt = _root_.add32 (valueBits (input_state[3]'(by norm_num)))
      (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num)))
        (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
        (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num)))
          (valueBits (input_state[6]'(by norm_num))))) (valueBits input_k0)) (valueBits input_w0)) := by
    rw [← hmv_ne, s_fe.1, s_sig1.1, hvk 3 (by norm_num), hvk 7 (by norm_num), hvk 4 (by norm_num),
      hvk 5 (by norm_num), hvk 6 (by norm_num)]
    exact mod6' _ _ _ _ _ _
  have hnetp_val : valueBits NEtp = _root_.add32 (valueBits (input_state[2]'(by norm_num)))
      (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[6]'(by norm_num)))
        (Specs.SHA256.upperSigma1 (valueBits NEt)))
        (Specs.SHA256.Ch (valueBits NEt) (valueBits (input_state[4]'(by norm_num)))
          (valueBits (input_state[5]'(by norm_num))))) (valueBits input_k1)) (valueBits input_w1)) := by
    rw [← hmv_netp, s_fe.2, s_sig1p.1, hmv_ne, hvk 2 (by norm_num), hvk 6 (by norm_num),
      hvk 4 (by norm_num), hvk 5 (by norm_num)]
    exact mod6' _ _ _ _ _ _
  have hnat_val : valueBits NAt = _root_.add32
      (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num)))
        (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
        (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num)))
          (valueBits (input_state[6]'(by norm_num))))) (valueBits input_k0)) (valueBits input_w0))
      (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits (input_state[0]'(by norm_num))))
        (Specs.SHA256.Maj (valueBits (input_state[0]'(by norm_num))) (valueBits (input_state[1]'(by norm_num)))
          (valueBits (input_state[2]'(by norm_num))))) := by
    rw [← hmv_na, s_fa.1, hmv_ne, hne_val, s_sig0.1,
      hvk 3 (by norm_num), hvk 0 (by norm_num), hvk 1 (by norm_num), hvk 2 (by norm_num)]
    exact modc' _ _ _ _ hd3_lt
  have hnatp_val : valueBits NAtp = _root_.add32
      (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[6]'(by norm_num)))
        (Specs.SHA256.upperSigma1 (valueBits NEt)))
        (Specs.SHA256.Ch (valueBits NEt) (valueBits (input_state[4]'(by norm_num)))
          (valueBits (input_state[5]'(by norm_num))))) (valueBits input_k1)) (valueBits input_w1))
      (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits NAt))
        (Specs.SHA256.Maj (valueBits NAt) (valueBits (input_state[0]'(by norm_num)))
          (valueBits (input_state[1]'(by norm_num))))) := by
    rw [← hmv_natp, s_fa.2, hmv_netp, hnetp_val, s_sig0p.1, hmv_na,
      hvk 2 (by norm_num), hvk 0 (by norm_num), hvk 1 (by norm_num)]
    exact modc' _ _ _ _ hd2_lt
  refine ⟨spec_value_eq env i₀ input_state input_var_state input_k0 input_w0 input_k1 input_w1
      NEt NAt NEtp NAtp hmNEt hmNAt hmNEtp hmNAtp hvk h_state_norm h_eval
      hnet_norm hnat_norm hnetp_norm hnatp_norm hne_val hnat_val hnetp_val hnatp_val,
    Or.inl us1_cwr, Or.inl us0_cwr, Or.inl bool_cwr, Or.inl bool_cwr,
    Or.inl us1_cwr, Or.inl us0_cwr, Or.inl bool_cwr, Or.inl bool_cwr,
    Or.inl pch_cwr, Or.inl pmaj_cwr, Or.inl fe_cwr, Or.inl fa_cwr⟩

-- Honest-witness facts for the `witBits` decomposition column.
lemma witBits_normalized (s : ℕ) : Normalized (RPShared.witBits (p := p) s) := by
  intro i
  simp only [RPShared.witBits, Fin.getElem_fin, Vector.getElem_ofFn]
  rcases Nat.mod_two_eq_zero_or_one (s % 2^32 / 2^i.val) with h | h <;> rw [h]
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)

lemma valueBits_witBits (s : ℕ) : valueBits (RPShared.witBits (p := p) s) = s % 2^32 := by
  have hlt : ∀ i : Fin 32, (s % 2^32) / 2^i.val % 2 < p := by
    intro i
    have h2 : (s % 2^32) / 2^i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hp : (2:ℕ) < p := by have := (Fact.out : p > 2^35); omega
    omega
  unfold valueBits RPShared.witBits
  conv_rhs => rw [← Add32.bit_decomp_sum (s % 2^32) (Nat.mod_lt _ (by norm_num))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Vector.getElem_ofFn, Fin.getElem_fin, ZMod.val_natCast_of_lt (hlt i)]

-- Completeness (honest-prover direction): the honest witnesses (`witBits` of each
-- round sum, `witCarry` of the carries, honest `Ch`/`σ`/`Maj` columns) satisfy every
-- constraint. This composes the completeness of the 6 σ/Maj subcircuits, `PackedCh`,
-- the 4 `BoolVec32` assertions, and `FusedEAdder`/`FusedAAdder` (whose `ProverAssumptions`
-- are `Assumptions ∧ Spec`, so it also requires the honest-value fact
-- `valueBits (witBits s) = s % 2^32`).
set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main, UpperSigma1.Spec, UpperSigma1.Assumptions,
    UpperSigma0.Spec, UpperSigma0.Assumptions, PackedMaj.Spec, PackedMaj.Assumptions,
    PackedCh.Spec, PackedCh.Assumptions, BoolVec32.Spec, BoolVec32.Assumptions,
    FusedEAdder.Spec, FusedEAdder.Assumptions, FusedAAdder.Spec, FusedAAdder.Assumptions]
  obtain ⟨h_state_norm, h_k0n, h_w0n, h_k1n, h_w1n⟩ := h_assumptions
  obtain ⟨h_is, h_ik0, h_iw0, h_ik1, h_iw1⟩ := h_input
  simp only [ll_sig1, ll_sig0, ll_packch, ll_packmaj, ll_bool, ll_fe, ll_fa,
    Nat.mul_zero, Nat.add_zero] at h_env ⊢
  obtain ⟨e_sig1, e_sig0, e_ne, e_na, e_sig1p, e_sig0p, e_nep, e_nap, e_packch, e_packmaj⟩ := h_env
  -- generic `evalBitsNat = valueBits` bridge
  have ev : ∀ (X : Var (fields 32) (F p)),
      evalBitsNat env X = valueBits (Vector.map (Expression.eval env.toEnvironment) X) :=
    fun X => Add32.evalBitsNat_eq_valueBits env X _ rfl
  -- turn an `ExtendsVector` statement into a `Vector.map`-equality
  have conv : ∀ (off : ℕ) (w : Vector (F p) 32),
      (∀ i : Fin 32, env.get (off + i.val) = w[i.val]) →
      Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => var {index := off + i}) = w := by
    intro off w h
    ext i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
    exact h ⟨i, hi⟩
  -- state-register normalization
  have hget : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_is] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]; exact h
  have n0 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[0]) := by
    rw [hget 0 (by norm_num)]; exact h_state_norm 0
  have n1 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[1]) := by
    rw [hget 1 (by norm_num)]; exact h_state_norm 1
  have n2 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[2]) := by
    rw [hget 2 (by norm_num)]; exact h_state_norm 2
  have n3 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[3]) := by
    rw [hget 3 (by norm_num)]; exact h_state_norm 3
  have n4 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[4]) := by
    rw [hget 4 (by norm_num)]; exact h_state_norm 4
  have n5 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[5]) := by
    rw [hget 5 (by norm_num)]; exact h_state_norm 5
  have n6 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[6]) := by
    rw [hget 6 (by norm_num)]; exact h_state_norm 6
  have n7 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[7]) := by
    rw [hget 7 (by norm_num)]; exact h_state_norm 7
  -- honest witness columns
  have hval_ne := conv (i₀ + 32 + 32) _ e_ne
  have hval_na := conv (i₀ + 32 + 32 + 32) _ e_na
  have hval_nep := conv (i₀ + 128 + 32 + 32) _ e_nep
  have hval_nap := conv (i₀ + 128 + 32 + 32 + 32) _ e_nap
  have nne : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 32 fun i => var {index := i₀ + 32 + 32 + i})) := by
    rw [hval_ne]; exact witBits_normalized _
  have nna : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 32 fun i => var {index := i₀ + 32 + 32 + 32 + i})) := by
    rw [hval_na]; exact witBits_normalized _
  have nnep : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 32 fun i => var {index := i₀ + 128 + 32 + 32 + i})) := by
    rw [hval_nep]; exact witBits_normalized _
  have nnap : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (Vector.mapRange 32 fun i => var {index := i₀ + 128 + 32 + 32 + 32 + i})) := by
    rw [hval_nap]; exact witBits_normalized _
  -- σ subcircuit specs + packed-Maj spec (honest witness)
  have ns_sig1 := (e_sig1 n4).2
  have ns_sig0 := (e_sig0 n0).2
  have ns_sig1p := (e_sig1p nne).2
  have ns_sig0p := (e_sig0p nna).2
  have s_packch := e_packch ⟨n4, n5, n6, nne⟩
  have s_packmaj := e_packmaj ⟨n0, n1, n2, nna⟩
  refine ⟨n4, n0, ⟨trivial, nne⟩, ⟨trivial, nna⟩, nne, nna,
    ⟨trivial, nnep⟩, ⟨trivial, nnap⟩, ⟨n4, n5, n6, nne⟩, ⟨n0, n1, n2, nna⟩,
    ⟨⟨nne, nnep, n4, n5, n6, ns_sig1, ns_sig1p, n3, n7, h_k0n, h_w0n, n2, h_k1n, h_w1n, s_packch⟩,
      ?_, ?_⟩,
    ⟨⟨nna, nnap, nne, nnep, ns_sig0, ns_sig0p, n0, n1, n2, n3, s_packmaj⟩, ?_, ?_⟩⟩
  · rw [hval_ne, valueBits_witBits]; simp only [ev, h_ik0, h_iw0]
  · rw [hval_nep, valueBits_witBits]; simp only [ev, h_ik1, h_iw1]
  · rw [hval_na, valueBits_witBits]; simp only [ev]
  · rw [hval_nap, valueBits_witBits]; simp only [ev]

def circuit : FormalCircuit (F p) Inputs SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness
  exposedChannels := fun _ _ => []
  exposedChannels_eq := by
    intro input offset exposed hmem; cases hmem

end SHA256RoundPair
end Solution.SHA256
end
