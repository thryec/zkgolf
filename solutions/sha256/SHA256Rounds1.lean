/-
The block-1 rounds-0-3 constant-fold gadgets in this file are due to gopikannappan,
from their public verified submission 8dfdec3a (cost 166,539).
-/

import Solution.SHA256.Round0Block1
import Solution.SHA256.Round1Block1
import Solution.SHA256.RoundDHK
import Solution.SHA256.SHA256Rounds
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256
namespace SHA256Rounds

/-!
# Block-1 specialized 62-round compression (rounds 0-3 constant folded)

Ported from bufferhe4d's 166,679 submission
(`/Users/simon/Documents/dev/Projects/zk.golf/solutions/sha-bufferhe4d-166679/SHA256Rounds1.lean`),
credit to bufferhe4d.

`circuit62_block1` computes the first 62 SHA-256 rounds for block 1, whose starting
state is the constant IV `H0`. Round 0 is peeled off as the constant-folded gadget
`Round0Block1.circuit`, round 1 as the Ch/Maj affine-folded `Round1Block1.circuit`,
and rounds 2 and 3 — whose state positions 3 and 7 (`d`/`h`) are still IV constants —
as `RoundDHK.circuit` instances (constant `d + h + k` folded into one addend);
rounds `4..61` run as a uniform 58-round `foldlRange`. Input is just the message
schedule (state is `H0`).
-/

/-- Elaboration-time views of the four peeled rounds' outputs. The `RoundDHK`
rounds take the *whole* previous state, so these stay linear in size. -/
abbrev st1x (input : Var SHA256Schedule (F p)) (i₀ : ℕ) : SHA256State (Expression (F p)) :=
  Round0Block1.circuit.output (input[0]'(by norm_num)) i₀
abbrev st2x (input : Var SHA256Schedule (F p)) (i₀ : ℕ) : SHA256State (Expression (F p)) :=
  Round1Block1.circuit.output
    ⟨(st1x input i₀)[0], (st1x input i₀)[4], input[1]'(by norm_num)⟩ (i₀ + 64)
abbrev st3x (input : Var SHA256Schedule (F p)) (i₀ : ℕ) : SHA256State (Expression (F p)) :=
  (RoundDHK.circuit RoundDHK.params2).output
    ⟨st2x input i₀, input[2]'(by norm_num)⟩ (i₀ + 64 + 130)
abbrev st4x (input : Var SHA256Schedule (F p)) (i₀ : ℕ) : SHA256State (Expression (F p)) :=
  (RoundDHK.circuit RoundDHK.params3).output
    ⟨st3x input i₀, input[3]'(by norm_num)⟩ (i₀ + 64 + 130 + 194)

/-- 62-round block-1 compression: folded rounds 0-3, then rounds 4..61. -/
def main62_block1 (input : Var SHA256Schedule (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let st1 ← Round0Block1.circuit (input[0]'(by norm_num))
  let st2 ← Round1Block1.circuit ⟨st1[0], st1[4], input[1]'(by norm_num)⟩
  let st3 ← RoundDHK.circuit RoundDHK.params2 ⟨st2, input[2]'(by norm_num)⟩
  let st4 ← RoundDHK.circuit RoundDHK.params3 ⟨st3, input[3]'(by norm_num)⟩
  Circuit.foldlRange 58 st4 (fun s (i : Fin 58) =>
    SHA256Round.circuit ⟨s, constWord32 (Specs.SHA256.K[i.val+4]'(by omega)).toNat,
      input[i.val+4]'(by omega)⟩)

def Assumptions62_block1 (input : SHA256Schedule (F p)) : Prop :=
  ∀ i : Fin 64, i.val < 62 → Normalized input[i]

def Spec62_block1 (input : SHA256Schedule (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    valStateAfterRound Specs.SHA256.H0 (input.map valueBits) 62
  ∧ ∀ i : Fin 8, Normalized out[i]

/-- The tail-loop analogue of `foldlAcc_eq_stateVar62`: the 58-round fold starting
from the folded-round-3 accumulator, at offset `i₀'`. The output structure of a
round does not depend on `K`/`w`, so this reuses `fin_foldl_eq_stateVar`. -/
lemma foldlAcc_eq_stateVar_tail (i₀' : ℕ)
    (st4v : SHA256State (Expression (F p)))
    (input_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 58) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀' (Vector.finRange 58)
      (fun s (i : Fin 58) => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i.val+4]'(by omega)).toNat,
          w := input_schedule[i.val+4]'(by omega) })
      st4v ⟨k, h⟩ =
        stateVar i₀' st4v k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar _ _ _

/-- Vector eta for 8-element vectors (kernel-cheap: entries stay atoms). -/
lemma vec8_eta {α : Type*} (s : Vector α 8) :
    (#v[s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]] : Vector α 8) = s := by
  apply Vector.ext
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

instance elaborated62_block1 :
    ElaboratedCircuit (F p) SHA256Schedule SHA256State main62_block1 := by
  elaborate_circuit_with {
    output input i₀ :=
      stateVar (i₀ + 64 + 130 + 194 + 194) (st4x input i₀) 58
  } using by
    simp only [circuit_norm]
    intros
    apply fin_foldl_eq_stateVar

set_option maxHeartbeats 8000000 in
theorem soundness62_block1 : Soundness (F p) main62_block1 Assumptions62_block1 Spec62_block1 := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions, main62_block1,
    Spec62_block1, Assumptions62_block1, Round0Block1.Spec,
    Round0Block1.Assumptions, Round1Block1.Spec, Round1Block1.Assumptions,
    RoundDHK.Spec, RoundDHK.Assumptions]
  obtain ⟨h_r0, h_r1, h_r2, h_r3, h_foldl⟩ := h_holds
  -- schedule words are normalized
  have h_wn : ∀ (j : ℕ) (hj : j < 64), j < 62 →
      Normalized (Vector.map (Expression.eval env) (input_var[j]'hj)) := by
    intro j hj hj62
    rw [show Vector.map (Expression.eval env) (input_var[j]'hj)
          = eval env (input_var[j]'hj) from (CircuitType.eval_var_fields env _).symm]
    rw [getElem_eval_vector, h_input]
    exact h_assumptions ⟨j, hj⟩ hj62
  have hLL0 : ∀ x : Var (fields 32) (F p), Round0Block1.circuit.localLength x = 64 :=
    fun x => by simp only [circuit_norm, Round0Block1.circuit, Round0Block1.elaborated]
  have hLL1 : ∀ x : Var Round1Block1.Inputs (F p), Round1Block1.circuit.localLength x = 130 :=
    fun x => by simp only [circuit_norm, Round1Block1.circuit, Round1Block1.elaborated]
  have hLL2 : ∀ (P : RoundDHK.Params) (x : Var RoundDHK.Inputs (F p)),
      (RoundDHK.circuit (p := p) P).localLength x = 194 :=
    fun P x => by simp only [circuit_norm, RoundDHK.circuit, RoundDHK.elaborated]
  -- constant positions of valStateAfterRound 2 and 3 (spec level, pure ℕ)
  have hvs2_3 : (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 2)[3]'(by norm_num)
      = RoundDHK.params2.dC := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 1 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.1,
      valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.1,
      RoundDHK.params2_dC_eq]
    rfl
  have hvs2_7 : (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 2)[7]'(by norm_num)
      = RoundDHK.params2.hC := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 1 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.2,
      valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.1,
      RoundDHK.params2_hC_eq]
    rfl
  have hvs3_3 : (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 3)[3]'(by norm_num)
      = RoundDHK.params3.dC := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 2 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.1,
      valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 1 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.1,
      valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.1,
      RoundDHK.params3_dC_eq]
    rfl
  have hvs3_7 : (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 3)[7]'(by norm_num)
      = RoundDHK.params3.hC := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 2 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.2,
      valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 1 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.1,
      valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num),
      sha256Round_literal, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.1,
      RoundDHK.params3_hC_eq]
    rfl
  -- round-0 spec
  obtain ⟨h_st1_val, h_st1_norm⟩ := h_r0 (h_wn 0 (by norm_num) (by norm_num))
  -- round-1 spec (its inputs are round-0's output words 0 and 4, and schedule word 1)
  obtain ⟨h_st2_val, h_st2_norm⟩ := h_r1
    ⟨by have h := h_st1_norm ⟨0, by norm_num⟩
        rw [Fin.getElem_fin, ← getElem_eval_vector, CircuitType.eval_var_fields] at h; exact h,
     by have h := h_st1_norm ⟨4, by norm_num⟩
        rw [Fin.getElem_fin, ← getElem_eval_vector, CircuitType.eval_var_fields] at h; exact h,
     h_wn 1 (by norm_num) (by norm_num)⟩
  simp only [hLL0] at h_st2_val h_st2_norm
  -- round-2 spec (whole round-1 output state + schedule word 2)
  obtain ⟨h_st3_val, h_st3_norm⟩ := h_r2 ⟨h_st2_norm, h_wn 2 (by norm_num) (by norm_num)⟩
  simp only [hLL0, hLL1] at h_st3_val h_st3_norm
  -- round-3 spec
  obtain ⟨h_st4_val, h_st4_norm⟩ := h_r3 ⟨h_st3_norm, h_wn 3 (by norm_num) (by norm_num)⟩
  simp only [hLL0, hLL1, hLL2] at h_st4_val h_st4_norm
  -- indexing-inside-eval reducer
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  -- schedule-word value bridges
  have hin : ∀ (j : ℕ) (hj : j < 64), input[j]'hj
      = Vector.map (Expression.eval env) (input_var[j]'hj) := by
    intro j hj
    have h := getElem_eval_vector env input_var j hj
    rw [h_input] at h
    rw [← h, CircuitType.eval_var_fields]
  -- st1 = valStateAfterRound H0 (input vals) 1
  have h_base_val1 : Vector.map valueBits (eval env (st1x input_var i₀))
      = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1 := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num),
      show valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 0 = Specs.SHA256.H0 from rfl,
      h_st1_val, Vector.getElem_map, ← hin 0 (by norm_num)]
  have hvb1_0 : valueBits (Vector.map (Expression.eval env) (st1x input_var i₀)[0])
      = (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1)[0]'(by norm_num) := by
    rw [← h_base_val1, Vector.getElem_map, ← getElem_eval_vector, CircuitType.eval_var_fields]
  have hvb1_4 : valueBits (Vector.map (Expression.eval env) (st1x input_var i₀)[4])
      = (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1)[4]'(by norm_num) := by
    rw [← h_base_val1, Vector.getElem_map, ← getElem_eval_vector, CircuitType.eval_var_fields]
  -- st2 = valStateAfterRound H0 (input vals) 2
  have h_base_val2 : Vector.map valueBits (eval env (st2x input_var i₀))
      = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 2 := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 1 (by norm_num)]
    have hvals1 : (Vector.map valueBits input)[1]'(by norm_num)
        = valueBits (Vector.map (Expression.eval env) (input_var[1]'(by norm_num))) := by
      rw [Vector.getElem_map, hin 1 (by norm_num)]
    rw [h_st2_val]
    show Specs.SHA256.sha256Round (Round1Block1.r1state _ _) _ _ = _
    rw [hvb1_0, hvb1_4, hvals1,
      show valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1
        = Specs.SHA256.sha256Round Specs.SHA256.H0 (Specs.SHA256.K[0]).toNat ((Vector.map valueBits input)[0]'(by norm_num)) from by
          rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num)]; rfl]
    rw [Round1Block1.r1state_of_sha256Round_H0]
  -- st3 = valStateAfterRound H0 (input vals) 3
  have h_base_val3 : Vector.map valueBits (eval env (st3x input_var i₀))
      = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 3 := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 2 (by norm_num)]
    rw [h_st3_val, h_base_val2,
      show RoundDHK.stateWithDH (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 2)
          RoundDHK.params2.dC RoundDHK.params2.hC
        = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 2 from by
          rw [RoundDHK.stateWithDH, ← hvs2_3, ← hvs2_7]; exact vec8_eta _,
      show (Specs.SHA256.K[2]).toNat = RoundDHK.params2.kC from RoundDHK.params2_kC_eq.symm,
      show (Vector.map valueBits input)[2]'(by norm_num)
        = valueBits (Vector.map (Expression.eval env) (input_var[2]'(by norm_num))) from by
          rw [Vector.getElem_map, hin 2 (by norm_num)]]
  -- st4 = valStateAfterRound H0 (input vals) 4
  have h_base_val4 : Vector.map valueBits (eval env (st4x input_var i₀))
      = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 4 := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 3 (by norm_num)]
    rw [h_st4_val, h_base_val3,
      show RoundDHK.stateWithDH (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 3)
          RoundDHK.params3.dC RoundDHK.params3.hC
        = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 3 from by
          rw [RoundDHK.stateWithDH, ← hvs3_3, ← hvs3_7]; exact vec8_eta _,
      show (Specs.SHA256.K[3]).toNat = RoundDHK.params3.kC from RoundDHK.params3_kC_eq.symm,
      show (Vector.map valueBits input)[3]'(by norm_num)
        = valueBits (Vector.map (Expression.eval env) (input_var[3]'(by norm_num))) from by
          rw [Vector.getElem_map, hin 3 (by norm_num)]]
  -- inductive invariant over the 58 tail rounds
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 58),
      Vector.map valueBits (eval env (stateVar (i₀+64+130+194+194) (st4x input_var i₀) k)) =
        valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) (k+4) ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((stateVar (i₀+64+130+194+194) (st4x input_var i₀) k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨h_base_val4, ?_⟩
      intro j hj
      simp only [stateVar]
      rw [getElem_eval_vector]
      exact h_st4_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 58 := by omega
      have hk'' : k < 58 := by omega
      have hk64 : k + 4 < 64 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_foldl ⟨k, hk''⟩
      simp only [hLL0, hLL1, hLL2] at h_foldl
      rw [foldlAcc_eq_stateVar_tail (i₀+64+130+194+194) (st4x input_var i₀) input_var k hk''] at h_foldl
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_foldl
      have h2 : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[k+4]'hk64).toNat)) := normalized_constWord32 env _
      have h3 : Normalized (Vector.map (Expression.eval env) (input_var[k+4]'hk64)) :=
        h_wn (k+4) hk64 (by omega)
      have h_spec := h_foldl ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [stateVar, valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) (k+4) hk64]
      refine ⟨?_, ?_⟩
      · rw [h_value, ih_val,
          valueBits_constWord32_of_lt env (Specs.SHA256.K[k+4]'hk64).toNat_lt,
          show Vector.map (Expression.eval env) (input_var[k+4]'hk64)
            = eval env (input_var[k+4]'hk64) from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, h_input,
          show (Vector.map valueBits input)[k+4]'hk64
            = valueBits (input[k+4]'hk64) from Vector.getElem_map _ _]
      · intro j hj
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_58, h_norm_58⟩ := h_inv 58 (le_refl 58)
  refine ⟨⟨h_val_58, ?_⟩, ?_⟩
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_58 i.val i.isLt
  · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, fun _ => Or.inl rfl⟩

set_option maxHeartbeats 8000000 in
theorem completeness62_block1 : Completeness (F p) main62_block1 Assumptions62_block1 := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions, main62_block1,
    Assumptions62_block1, Round0Block1.Spec, Round0Block1.Assumptions,
    Round1Block1.Spec, Round1Block1.Assumptions, RoundDHK.Spec, RoundDHK.Assumptions]
  obtain ⟨h_r0, h_r1, h_r2, h_r3, h_foldl⟩ := h_env
  have hLL0 : ∀ x : Var (fields 32) (F p), Round0Block1.circuit.localLength x = 64 :=
    fun x => by simp only [circuit_norm, Round0Block1.circuit, Round0Block1.elaborated]
  have hLL1 : ∀ x : Var Round1Block1.Inputs (F p), Round1Block1.circuit.localLength x = 130 :=
    fun x => by simp only [circuit_norm, Round1Block1.circuit, Round1Block1.elaborated]
  have hLL2 : ∀ (P : RoundDHK.Params) (x : Var RoundDHK.Inputs (F p)),
      (RoundDHK.circuit (p := p) P).localLength x = 194 :=
    fun P x => by simp only [circuit_norm, RoundDHK.circuit, RoundDHK.elaborated]
  have h_wn : ∀ (j : ℕ) (hj : j < 64), j < 62 →
      Normalized (Vector.map (Expression.eval env.toEnvironment) (input_var[j]'hj)) := by
    intro j hj hj62
    rw [show Vector.map (Expression.eval env.toEnvironment) (input_var[j]'hj)
          = eval env.toEnvironment (input_var[j]'hj) from (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input]
    exact h_assumptions ⟨j, hj⟩ hj62
  obtain ⟨_, h_st1_norm⟩ := h_r0 (h_wn 0 (by norm_num) (by norm_num))
  have na0 : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (st1x input_var i₀)[0]) := by
    have h := h_st1_norm ⟨0, by norm_num⟩
    rw [Fin.getElem_fin, ← getElem_eval_vector, CircuitType.eval_var_fields] at h; exact h
  have na4 : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (st1x input_var i₀)[4]) := by
    have h := h_st1_norm ⟨4, by norm_num⟩
    rw [Fin.getElem_fin, ← getElem_eval_vector, CircuitType.eval_var_fields] at h; exact h
  obtain ⟨_, h_st2_norm⟩ := h_r1 ⟨na0, na4, h_wn 1 (by norm_num) (by norm_num)⟩
  simp only [hLL0] at h_st2_norm
  obtain ⟨_, h_st3_norm⟩ := h_r2 ⟨h_st2_norm, h_wn 2 (by norm_num) (by norm_num)⟩
  simp only [hLL0, hLL1] at h_st3_norm
  obtain ⟨_, h_st4_norm⟩ := h_r3 ⟨h_st3_norm, h_wn 3 (by norm_num) (by norm_num)⟩
  simp only [hLL0, hLL1, hLL2] at h_st4_norm
  -- inductive invariant: every tail-round input state is normalized
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 58),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((stateVar (i₀+64+130+194+194)
          (st4x input_var i₀) k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [stateVar]
      rw [getElem_eval_vector]
      exact h_st4_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 58 := by omega
      have hk'' : k < 58 := by omega
      have hk64 : k + 4 < 64 := by omega
      specialize h_foldl ⟨k, hk''⟩
      simp only [hLL0, hLL1, hLL2] at h_foldl
      rw [foldlAcc_eq_stateVar_tail (i₀+64+130+194+194) (st4x input_var i₀) input_var k hk''] at h_foldl
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_foldl
      have h2 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[k+4]'hk64).toNat)) := normalized_constWord32 _ _
      have h3 : Normalized (Vector.map (Expression.eval env.toEnvironment) (input_var[k+4]'hk64)) :=
        h_wn (k+4) hk64 (by omega)
      have h_spec := h_foldl ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [stateVar]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  -- discharge the five witnessed subcircuits' assumptions
  refine ⟨h_wn 0 (by norm_num) (by norm_num), ⟨na0, na4, h_wn 1 (by norm_num) (by norm_num)⟩,
    ⟨h_st2_norm, h_wn 2 (by norm_num) (by norm_num)⟩,
    ⟨h_st3_norm, h_wn 3 (by norm_num) (by norm_num)⟩, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp only [hLL0, hLL1, hLL2]
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← foldlAcc_eq_stateVar_tail (i₀+64+130+194+194) (st4x input_var i₀) input_var i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 58) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact normalized_constWord32 _ _
  · have hi64 : i.val + 4 < 64 := by omega
    exact h_wn (i.val+4) hi64 (by omega)

def circuit62_block1 : FormalCircuit (F p) SHA256Schedule SHA256State := {
  main := main62_block1, elaborated := elaborated62_block1,
  Assumptions := Assumptions62_block1, Spec := Spec62_block1
  soundness := soundness62_block1
  completeness := by simp only [completeness62_block1]
}

/-!
## Block-1 paired variant: rounds 0-1 folded, rounds 2-61 as 30 cross-round pairs

Identical `Assumptions62_block1` / `Spec62_block1` to `circuit62_block1`; the tail
loop is realised as 30 `SHA256RoundPair` steps (each advancing two rounds), consuming
rounds 2..61 directly after the two peeled folded rounds. Reuses
`SHA256Rounds63.stateVarPaired` and `SHA256Rounds63.fin_foldl_eq_stateVarPaired` for
the paired witness layout.
-/

section Paired
variable [Fact (p > 2^76)]

/-- Pure bridge: reconstructing round-1's `r1state` from the round-0 output state
and advancing one round recovers `valStateAfterRound H0 w 2`. -/
lemma valState2_bridge (wvals : Vector ℕ 64) :
    Specs.SHA256.sha256Round
      (Round1Block1.r1state
        ((valStateAfterRound Specs.SHA256.H0 wvals 1)[0]'(by norm_num))
        ((valStateAfterRound Specs.SHA256.H0 wvals 1)[4]'(by norm_num)))
      (Specs.SHA256.K[1]'(by norm_num)).toNat (wvals[1]'(by norm_num))
    = valStateAfterRound Specs.SHA256.H0 wvals 2 := by
  have hS1 : valStateAfterRound Specs.SHA256.H0 wvals 1
      = Specs.SHA256.sha256Round Specs.SHA256.H0 (Specs.SHA256.K[0]'(by norm_num)).toNat
          (wvals[0]'(by norm_num)) := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 wvals 0 (by norm_num),
      show valStateAfterRound Specs.SHA256.H0 wvals 0 = Specs.SHA256.H0 from rfl]
  have hbridge : Round1Block1.r1state
        ((valStateAfterRound Specs.SHA256.H0 wvals 1)[0]'(by norm_num))
        ((valStateAfterRound Specs.SHA256.H0 wvals 1)[4]'(by norm_num))
      = valStateAfterRound Specs.SHA256.H0 wvals 1 := by
    rw [hS1]; exact Round1Block1.r1state_of_sha256Round_H0 _ _
  rw [hbridge, ← valStateAfterRound_succ Specs.SHA256.H0 wvals 1 (by norm_num)]

/-- 62-round block-1 compression: folded round 0, folded round 1, then rounds 2..61
as 30 pairs. -/
def main62_block1_paired (input : Var SHA256Schedule (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let st1 ← Round0Block1.circuit (input[0]'(by norm_num))
  let st2 ← Round1Block1.circuit ⟨st1[0]'(by norm_num), st1[4]'(by norm_num), input[1]'(by norm_num)⟩
  Circuit.foldlRange 30 st2 (fun s (i : Fin 30) =>
    SHA256RoundPair.circuit ⟨s,
      constWord32 (Specs.SHA256.K[2*i.val+2]'(by omega)).toNat, input[2*i.val+2]'(by omega),
      constWord32 (Specs.SHA256.K[2*i.val+3]'(by omega)).toNat, input[2*i.val+3]'(by omega)⟩)

/-- The paired tail-loop analogue: the 30-pair fold starting from the folded round-1
accumulator (pair `k` consumes rounds `2k+2`, `2k+3`). The pair output shape is
`K`/`w`-independent, so this reuses `fin_foldl_eq_stateVarPaired`. -/
lemma foldlAcc_eq_stateVarPaired_block1' (i₀' : ℕ)
    (base : SHA256State (Expression (F p)))
    (input_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 30) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀' (Vector.finRange 30)
      (fun s (i : Fin 30) => subcircuit SHA256RoundPair.circuit
        { state := s,
          k0 := constWord32 (Specs.SHA256.K[2*i.val+2]'(by omega)).toNat,
          w0 := input_schedule[2*i.val+2]'(by omega),
          k1 := constWord32 (Specs.SHA256.K[2*i.val+3]'(by omega)).toNat,
          w1 := input_schedule[2*i.val+3]'(by omega) })
      base ⟨k, h⟩ =
        SHA256Rounds63.stateVarPaired i₀' base k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact SHA256Rounds63.fin_foldl_eq_stateVarPaired _ _ _

instance elaborated62_block1_paired :
    ElaboratedCircuit (F p) SHA256Schedule SHA256State main62_block1_paired := by
  elaborate_circuit_with {
    output input i₀ :=
      SHA256Rounds63.stateVarPaired (i₀ + 64 + 130)
        (Round1Block1.circuit.output
          ⟨(Round0Block1.circuit.output (input[0]'(by norm_num)) i₀)[0]'(by norm_num),
           (Round0Block1.circuit.output (input[0]'(by norm_num)) i₀)[4]'(by norm_num),
           input[1]'(by norm_num)⟩
          (i₀ + 64)) 30
  } using by
    simp only [circuit_norm]
    intros
    apply SHA256Rounds63.fin_foldl_eq_stateVarPaired

set_option maxHeartbeats 8000000 in
theorem soundness62_block1_paired :
    Soundness (F p) main62_block1_paired Assumptions62_block1 Spec62_block1 := by
  circuit_proof_start [SHA256RoundPair.Spec, SHA256RoundPair.Assumptions, main62_block1_paired,
    Spec62_block1, Assumptions62_block1, Round0Block1.Spec, Round0Block1.Assumptions,
    Round1Block1.Spec, Round1Block1.Assumptions]
  obtain ⟨h_r0, h_r1, h_foldl⟩ := h_holds
  have hwn : ∀ (j : ℕ) (hj : j < 62),
      Normalized (Vector.map (Expression.eval env) (input_var[j]'(by omega))) := by
    intro j hj
    rw [show Vector.map (Expression.eval env) (input_var[j]'(by omega))
          = eval env (input_var[j]'(by omega)) from (CircuitType.eval_var_fields env _).symm]
    rw [getElem_eval_vector, h_input]
    exact h_assumptions ⟨j, by omega⟩ hj
  obtain ⟨h_st1_val, h_st1_norm⟩ := h_r0 (hwn 0 (by norm_num))
  have hLL0 : ∀ x : Var (fields 32) (F p), Round0Block1.circuit.localLength x = 64 :=
    fun x => by simp only [circuit_norm, Round0Block1.circuit, Round0Block1.elaborated]
  have hLL1 : ∀ x : Var Round1Block1.Inputs (F p), Round1Block1.circuit.localLength x = 130 :=
    fun x => by simp only [circuit_norm, Round1Block1.circuit, Round1Block1.elaborated]
  have hin0 : input[0]'(by norm_num) = Vector.map (Expression.eval env) (input_var[0]'(by norm_num)) := by
    have h := getElem_eval_vector env input_var 0 (by norm_num)
    rw [h_input] at h
    rw [← h, CircuitType.eval_var_fields]
  have h_base1_val : Vector.map valueBits (eval env (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀))
      = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1 := by
    rw [valStateAfterRound_succ Specs.SHA256.H0 (Vector.map valueBits input) 0 (by norm_num),
      show valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 0 = Specs.SHA256.H0 from rfl,
      h_st1_val, Vector.getElem_map, ← hin0]
  have hr1_a : Normalized (Vector.map (Expression.eval env)
      ((Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num))) := by
    rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact h_st1_norm ⟨0, by norm_num⟩
  have hr1_e : Normalized (Vector.map (Expression.eval env)
      ((Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num))) := by
    rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact h_st1_norm ⟨4, by norm_num⟩
  obtain ⟨h_st2_val, h_st2_norm⟩ := h_r1 ⟨hr1_a, hr1_e, hwn 1 (by norm_num)⟩
  simp only [hLL0] at h_st2_val h_st2_norm
  have hva : valueBits (Vector.map (Expression.eval env)
        ((Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num)))
      = (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1)[0]'(by norm_num) := by
    rw [← CircuitType.eval_var_fields, ← h_base1_val, Vector.getElem_map, getElem_eval_vector]
  have hve : valueBits (Vector.map (Expression.eval env)
        ((Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num)))
      = (valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 1)[4]'(by norm_num) := by
    rw [← CircuitType.eval_var_fields, ← h_base1_val, Vector.getElem_map, getElem_eval_vector]
  have hw1 : valueBits (Vector.map (Expression.eval env) (input_var[1]'(by norm_num)))
      = (Vector.map valueBits input)[1]'(by norm_num) := by
    rw [← CircuitType.eval_var_fields, getElem_eval_vector, h_input, Vector.getElem_map]
  have h_base2_val : Vector.map valueBits (eval env (Round1Block1.circuit.output
        ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
         (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
         input_var[1]'(by norm_num)⟩ (i₀ + 64)))
      = valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) 2 := by
    rw [h_st2_val, hva, hve, hw1]
    exact valState2_bridge (Vector.map valueBits input)
  -- inductive invariant over the 30 paired tail steps (rounds 2..61)
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 30),
      Vector.map valueBits (eval env (SHA256Rounds63.stateVarPaired (i₀ + 64 + 130)
          (Round1Block1.circuit.output
            ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
             (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
             input_var[1]'(by norm_num)⟩ (i₀ + 64)) k)) =
        valStateAfterRound Specs.SHA256.H0 (Vector.map valueBits input) (2 + 2 * k) ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((SHA256Rounds63.stateVarPaired (i₀ + 64 + 130)
          (Round1Block1.circuit.output
            ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
             (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
             input_var[1]'(by norm_num)⟩ (i₀ + 64)) k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simpa only [SHA256Rounds63.stateVarPaired, Nat.mul_zero, Nat.add_zero] using h_base2_val
      · intro j hj
        simp only [SHA256Rounds63.stateVarPaired]
        rw [getElem_eval_vector]
        exact h_st2_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 30 := by omega
      have hk'' : k < 30 := by omega
      have hk2 : 2 * k + 2 < 64 := by omega
      have hk2' : 2 * k + 3 < 64 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_foldl ⟨k, hk''⟩
      simp only [hLL0, hLL1] at h_foldl
      rw [foldlAcc_eq_stateVarPaired_block1' (i₀ + 64 + 130)
        (Round1Block1.circuit.output
          ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
           (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
           input_var[1]'(by norm_num)⟩ (i₀ + 64)) input_var k hk''] at h_foldl
      simp only [circuit_norm, SHA256RoundPair.circuit, SHA256RoundPair.elaborated,
        SHA256RoundPair.Spec, SHA256RoundPair.Assumptions] at h_foldl
      have h2a : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k+2]'hk2).toNat)) := normalized_constWord32 env _
      have h2b : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k+3]'hk2').toNat)) := normalized_constWord32 env _
      have h_spec := h_foldl ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2a, hwn (2*k+2) (by omega), h2b, hwn (2*k+3) (by omega)⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [SHA256Rounds63.stateVarPaired]
      refine ⟨?_, ?_⟩
      · rw [h_value, SHA256RoundPair.specFn_eq, ih_val,
          show 2 + 2 * (k + 1) = (2 * k + 2 + 1) + 1 from by ring,
          valStateAfterRound_succ _ _ (2*k+3) hk2', valStateAfterRound_succ _ _ (2*k+2) hk2,
          show 2 + 2 * k = 2 * k + 2 from by ring,
          valueBits_constWord32_of_lt env (Specs.SHA256.K[2*k+2]'hk2).toNat_lt,
          valueBits_constWord32_of_lt env (Specs.SHA256.K[2*k+3]'hk2').toNat_lt,
          show Vector.map (Expression.eval env) (input_var[2*k+2]'hk2)
            = eval env (input_var[2*k+2]'hk2) from (CircuitType.eval_var_fields env _).symm,
          show Vector.map (Expression.eval env) (input_var[2*k+3]'hk2')
            = eval env (input_var[2*k+3]'hk2') from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, getElem_eval_vector, h_input,
          show (Vector.map valueBits input)[2*k+2]'hk2
            = valueBits (input[2*k+2]'hk2) from Vector.getElem_map _ _,
          show (Vector.map valueBits input)[2*k+3]'hk2'
            = valueBits (input[2*k+3]'hk2') from Vector.getElem_map _ _]
      · intro j hj
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_62, h_norm_62⟩ := h_inv 30 (le_refl 30)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact h_val_62
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_62 i.val i.isLt
  · exact ⟨Or.inl rfl, Or.inl rfl, fun _ => Or.inl rfl⟩

set_option maxHeartbeats 8000000 in
theorem completeness62_block1_paired :
    Completeness (F p) main62_block1_paired Assumptions62_block1 := by
  circuit_proof_start [SHA256RoundPair.Spec, SHA256RoundPair.Assumptions, main62_block1_paired,
    Assumptions62_block1, Round0Block1.Spec, Round0Block1.Assumptions,
    Round1Block1.Spec, Round1Block1.Assumptions]
  obtain ⟨h_r0, h_r1, h_foldl⟩ := h_env
  have hwn : ∀ (j : ℕ) (hj : j < 62),
      Normalized (Vector.map (Expression.eval env.toEnvironment) (input_var[j]'(by omega))) := by
    intro j hj
    rw [show Vector.map (Expression.eval env.toEnvironment) (input_var[j]'(by omega))
          = eval env.toEnvironment (input_var[j]'(by omega)) from (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input]
    exact h_assumptions ⟨j, by omega⟩ hj
  obtain ⟨_, h_st1_norm⟩ := h_r0 (hwn 0 (by norm_num))
  have hLL0 : ∀ x : Var (fields 32) (F p), Round0Block1.circuit.localLength x = 64 :=
    fun x => by simp only [circuit_norm, Round0Block1.circuit, Round0Block1.elaborated]
  have hLL1 : ∀ x : Var Round1Block1.Inputs (F p), Round1Block1.circuit.localLength x = 130 :=
    fun x => by simp only [circuit_norm, Round1Block1.circuit, Round1Block1.elaborated]
  have hr1_a : Normalized (Vector.map (Expression.eval env.toEnvironment)
      ((Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num))) := by
    rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact h_st1_norm ⟨0, by norm_num⟩
  have hr1_e : Normalized (Vector.map (Expression.eval env.toEnvironment)
      ((Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num))) := by
    rw [← CircuitType.eval_var_fields, getElem_eval_vector]; exact h_st1_norm ⟨4, by norm_num⟩
  obtain ⟨_, h_st2_norm⟩ := h_r1 ⟨hr1_a, hr1_e, hwn 1 (by norm_num)⟩
  simp only [hLL0] at h_st2_norm
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 30),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((SHA256Rounds63.stateVarPaired (i₀ + 64 + 130)
          (Round1Block1.circuit.output
            ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
             (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
             input_var[1]'(by norm_num)⟩ (i₀ + 64)) k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [SHA256Rounds63.stateVarPaired]
      rw [getElem_eval_vector]
      exact h_st2_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 30 := by omega
      have hk'' : k < 30 := by omega
      have hk2 : 2 * k + 2 < 64 := by omega
      have hk2' : 2 * k + 3 < 64 := by omega
      specialize h_foldl ⟨k, hk''⟩
      simp only [hLL0, hLL1] at h_foldl
      rw [foldlAcc_eq_stateVarPaired_block1' (i₀ + 64 + 130)
        (Round1Block1.circuit.output
          ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
           (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
           input_var[1]'(by norm_num)⟩ (i₀ + 64)) input_var k hk''] at h_foldl
      simp only [circuit_norm, SHA256RoundPair.circuit, SHA256RoundPair.elaborated,
        SHA256RoundPair.Spec, SHA256RoundPair.Assumptions] at h_foldl
      have h2a : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k+2]'hk2).toNat)) := normalized_constWord32 _ _
      have h2b : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k+3]'hk2').toNat)) := normalized_constWord32 _ _
      have h_spec := h_foldl ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2a, hwn (2*k+2) (by omega), h2b, hwn (2*k+3) (by omega)⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [SHA256Rounds63.stateVarPaired]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  refine ⟨hwn 0 (by norm_num), ⟨hr1_a, hr1_e, hwn 1 (by norm_num)⟩, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [hLL0, hLL1]
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← foldlAcc_eq_stateVarPaired_block1' (i₀ + 64 + 130)
      (Round1Block1.circuit.output
        ⟨(Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[0]'(by norm_num),
         (Round0Block1.circuit.output (input_var[0]'(by norm_num)) i₀)[4]'(by norm_num),
         input_var[1]'(by norm_num)⟩ (i₀ + 64)) input_var i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 30) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact normalized_constWord32 _ _
  · exact hwn (2*i.val+2) (by omega)
  · exact normalized_constWord32 _ _
  · exact hwn (2*i.val+3) (by omega)

def circuit62_block1_paired : FormalCircuit (F p) SHA256Schedule SHA256State := {
  main := main62_block1_paired, elaborated := elaborated62_block1_paired,
  Assumptions := Assumptions62_block1, Spec := Spec62_block1
  soundness := soundness62_block1_paired
  completeness := by simp only [completeness62_block1_paired]
}

end Paired

end SHA256Rounds
end Solution.SHA256
end
