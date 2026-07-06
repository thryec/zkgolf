import Solution.SHA256.AddMany
import Solution.SHA256.SigmaSum
import Challenge.Instances.SHA256.Interface
import Challenge.Utils.CostR1CS

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Fused multi-word + wide-affine modular addition for SHA-256

Adds `n ≤ 7` normalized 32-bit words (as `fields 32` bit vectors, LSB first)
**plus** one extra "wide" affine addend, given as a single field element whose
ℕ value is `< 2^34`, all modulo `2^32` — via a **single** bit-decomposition of
the whole sum.

R1CS structure (per call): the sum `S` of `n ≤ 7` words each `< 2^32` plus the
wide addend `< 2^34` is `< 7·2^32 + 2^34 < 2^36`, so the carry `S / 2^32 ≤ 10`
fits in one low bit + 3 high carry bits (weights 2, 4, 8). We witness:
- 32 witnesses for the output word `z[0..31]`
- 3  witnesses for the high carry bits `cv[0..2]` (bit j has weight `2^(j+1)`)
and assert:
- 32 boolean constraints `z[i]·(z[i]−1) = 0`
- 3  boolean constraints on the high carry bits
- 1  boolean constraint on the affine low-carry expression
     `2^-32·(Σⱼ fromBits(word j) + wide − fromBits(z)) − Σⱼ 2^(j+1)·cv[j]`
  which doubles as the sum recomposition constraint.

Total: 35 witnesses, 36 rows.

Soundness requires `p > 2^37` so the carry identity lifts to ℕ
(the recomposed side is `< 2^32 + 2^32·15 = 2^36` and the sum side `< 2^36`).
-/

open Challenge.Instances.SHA256.Interface (circomPrime) in
/-- The concrete SHA-256 challenge prime exceeds `2^37`, as required by the
`AddManyWide` gadget (callers carrying only `Fact (p > 2^35)` cannot derive
this, so the gadget's stronger fact is discharged here once and for all). -/
instance (priority := 100) factCircomPrimeGt2pow37 : Fact (circomPrime > 2^37) :=
  ⟨by norm_num [circomPrime]⟩

namespace AddManyWide

variable {n : ℕ}

/-! ## Definitions -/

/-- Inputs: `n` bit-decomposed 32-bit words plus one wide field addend. -/
structure Inputs (n : ℕ) (F : Type) where
  words : ProvableVector (fields 32) n F
  wide : field F
deriving ProvableStruct

/-- The natural-number value of all addends (words + wide) under a prover
environment. -/
def sumEvalNat (env : ProverEnvironment (F p))
    (words : Var (ProvableVector (fields 32) n) (F p)) (wide : Var field (F p)) : ℕ :=
  AddMany.sumEvalNat env words + (env wide).val

set_option linter.unusedVariables false in
/-- Fused adder over `n ≤ 7` normalized 32-bit words plus one wide affine addend
(value `< 2^34`): 3 witnessed high carry bits plus a fused low-carry/recomposition
row. The `hn` proof is not used computationally; it documents the arity bound
required by soundness (`circuit` threads it through `Fact (n ≤ 7)`). -/
def addManyWide (hn : n ≤ 7) (words : Var (ProvableVector (fields 32) n) (F p))
    (wide : Var field (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- Witness the low 32 bits of the sum
  let z ← witnessVector 32 fun env =>
    let s := sumEvalNat env words wide
    Vector.ofFn fun (i : Fin 32) => ((s % 2^32 / 2^i.val % 2 : ℕ) : F p)
  -- Witness the 3 high carry bits (bit j has weight 2^(j+1))
  let cv ← witnessVector 3 fun env =>
    let s := sumEvalNat env words wide
    Vector.ofFn fun (j : Fin 3) => ((s / 2^32 / 2^(j.val+1) % 2 : ℕ) : F p)
  -- Boolean constraints on output bits
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  -- Boolean constraints on high carry bits
  Circuit.forEach (Vector.finRange 3) fun j =>
    assertZero (cv[j] * (cv[j] - 1))
  -- Fused low-carry booleanity + sum recomposition row
  let e0 := ((2^32 : F p)⁻¹ : F p) * (AddMany.sumExpr words + wide - fromBitsExpr z)
    - AddMany.highExpr cv
  assertZero (e0 * (e0 - 1))
  return z

def Assumptions (input : Inputs n (F p)) : Prop :=
  (∀ i : Fin n, Normalized input.words[i]) ∧ input.wide.val < 2^34

def Spec (input : Inputs n (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = ((∑ i : Fin n, valueBits input.words[i]) + input.wide.val) % 2^32 ∧
  Normalized z

/-! ## Helper lemmas -/

/-- The ℕ sum of `n ≤ 7` normalized words plus a wide addend `< 2^34` is `< 2^36`. -/
lemma sum_lt (words : ProvableVector (fields 32) n (F p))
    (hnorm : ∀ i : Fin n, Normalized words[i]) (hn : n ≤ 7) {w : ℕ} (hw : w < 2^34) :
    (∑ i : Fin n, valueBits words[i]) + w < 2^36 := by
  have hbound : ∀ i : Fin n, valueBits words[i] ≤ 2^32 - 1 := fun i => by
    have := valueBits_lt_two_pow words[i] (hnorm i); omega
  have hle : (∑ i : Fin n, valueBits words[i]) ≤ n * (2^32 - 1) := by
    calc ∑ i : Fin n, valueBits words[i] ≤ ∑ _i : Fin n, (2^32 - 1) :=
          Finset.sum_le_sum (fun i _ => hbound i)
      _ = n * (2^32 - 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have : n * (2^32 - 1) ≤ 7 * (2^32 - 1) := Nat.mul_le_mul_right _ hn
  omega

section
variable [Fact (n ≤ 7)]

def main (input : Var (Inputs n) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  addManyWide (Fact.out : n ≤ 7) input.words input.wide

instance elaborated : ElaboratedCircuit (F p) (Inputs n) (fields 32) main := by
  elaborate_circuit

section
variable [Fact (p > 2^37)]

set_option maxHeartbeats 1000000 in
theorem soundness :
    Soundness (F p) (Input := Inputs n) main Assumptions Spec := by
  circuit_proof_start [addManyWide, main]
  obtain ⟨h_z_bool, h_cv_bool, h_e0_bool⟩ := h_holds
  obtain ⟨h_norm, h_wide_lt⟩ := h_assumptions
  have h_words_eq : eval env input_var.words = input.words := by rw [← h_input]
  have h_wide_eq : Expression.eval env input_var.wide = input.wide := by rw [← h_input]
  have hn : n ≤ 7 := Fact.out
  have hp_big : (2:ℕ)^37 < p := Fact.out
  have hp32 : (2:ℕ)^32 < p :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hp_big
  rw [Add32.z_var_eval env i₀]
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    Add32.normalized_of_bool_holds env i₀ h_z_bool
  have h_cv_le : ∀ j : Fin 3, (env.get (i₀ + 32 + j.val)).val ≤ 1 := by
    intro j
    rcases IsBool.val_of_IsBool (Add32.isbool_of_bool_constraint (h_cv_bool j)) with hh | hh <;> omega
  refine ⟨?_, h_z_norm⟩
  set vz := valueBits (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) with hvz_def
  set SV := ∑ i : Fin n, valueBits input.words[i] with hSV_def
  set hi := ∑ j : Fin 3, (env.get (i₀ + 32 + j.val)).val * 2^(j.val+1) with hhi_def
  have hvz_lt : vz < 2^32 := valueBits_lt_two_pow _ h_z_norm
  have hS_lt : SV + input.wide.val < 2^36 := sum_lt input.words h_norm hn h_wide_lt
  have hS_lt_p : SV + input.wide.val < p :=
    lt_trans hS_lt (lt_trans (by norm_num) hp_big)
  have h_hi_le : hi ≤ 14 := by
    have hle : hi ≤ ∑ j : Fin 3, 1 * 2^(j.val+1) := by
      rw [hhi_def]
      exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (h_cv_le j)
    have h2 : (∑ j : Fin 3, 1 * 2^(j.val+1)) = 14 := by norm_num [Fin.sum_univ_succ]
    omega
  -- field evaluations
  have h_sum_eval : Expression.eval env (AddMany.sumExpr input_var.words) = ((SV : ℕ) : F p) :=
    AddMany.sumExpr_eval env input_var.words input.words h_words_eq
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
      Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := Add32.z_var_eval env i₀
  have h_fz : Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
      ((vz : ℕ) : F p) :=
    Add32.fromBitsExpr_eval_normalized env _ _ h_z_eval
  have h_high_eval : Expression.eval env (AddMany.highExpr
      (Vector.mapRange 3 fun j => (var {index := i₀ + 32 + j} : Expression (F p)))) =
      ((hi : ℕ) : F p) := by
    rw [AddMany.eval_highExpr]
    have hterm : ∀ j : Fin 3,
        Expression.eval env ((Vector.mapRange 3 fun j =>
            (var {index := i₀ + 32 + j} : Expression (F p)))[j.val]'j.isLt) *
          ((2^(j.val+1) : ℕ) : F p)
        = (((env.get (i₀ + 32 + j.val)).val * 2^(j.val+1) : ℕ) : F p) := by
      intro j
      rw [Vector.getElem_mapRange]
      show env.get (i₀ + 32 + j.val) * _ = _
      conv_lhs => rw [← ZMod.natCast_rightInverse (env.get (i₀ + 32 + j.val))]
      rw [← Nat.cast_mul]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Nat.cast_sum]
  have h_wide_eval : Expression.eval env input_var.wide = ((input.wide.val : ℕ) : F p) := by
    rw [h_wide_eq]; exact (ZMod.natCast_rightInverse input.wide).symm
  have h_pow32_ne : (2^32 : F p) ≠ 0 := by
    intro hz
    have hval : (2^32 : F p).val = 2^32 := by
      rw [show (2^32 : F p) = ((2^32 : ℕ) : F p) from by push_cast; ring,
        ZMod.val_natCast_of_lt hp32]
    rw [hz, ZMod.val_zero] at hval
    norm_num at hval
  -- case split on the low carry bit
  rcases mul_eq_zero.mp h_e0_bool with h0 | h1
  · -- e₀ = 0: SV + wide = vz + 2^32·hi
    have hmul : (2^32 : F p) * ((2^32 : F p)⁻¹ *
        (Expression.eval env (AddMany.sumExpr input_var.words) +
          Expression.eval env input_var.wide -
          Expression.eval env (fromBitsExpr
            (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))))) =
        (2^32 : F p) * Expression.eval env (AddMany.highExpr
          (Vector.mapRange 3 fun j => (var {index := i₀ + 32 + j} : Expression (F p)))) := by
      rw [show (2^32 : F p)⁻¹ *
        (Expression.eval env (AddMany.sumExpr input_var.words) +
          Expression.eval env input_var.wide -
          Expression.eval env (fromBitsExpr
            (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))))) =
        Expression.eval env (AddMany.highExpr
          (Vector.mapRange 3 fun j => (var {index := i₀ + 32 + j} : Expression (F p)))) from by
        linear_combination h0]
    rw [← mul_assoc, mul_inv_cancel₀ h_pow32_ne, one_mul] at hmul
    rw [h_sum_eval, h_fz, h_high_eval, h_wide_eval] at hmul
    have hlin : ((SV + input.wide.val : ℕ) : F p) = ((vz + 2^32 * hi : ℕ) : F p) := by
      push_cast
      linear_combination hmul
    have h_rhs_lt_p : vz + 2^32 * hi < p := by omega
    have h_nat_eq : SV + input.wide.val = vz + 2^32 * hi := by
      have hv := congr_arg ZMod.val hlin
      rwa [ZMod.val_natCast_of_lt hS_lt_p, ZMod.val_natCast_of_lt h_rhs_lt_p] at hv
    rw [hSV_def] at h_nat_eq
    simp only [Fin.getElem_fin] at h_nat_eq ⊢
    omega
  · -- e₀ = 1: SV + wide = vz + 2^32·(1 + hi)
    have hmul : (2^32 : F p) * ((2^32 : F p)⁻¹ *
        (Expression.eval env (AddMany.sumExpr input_var.words) +
          Expression.eval env input_var.wide -
          Expression.eval env (fromBitsExpr
            (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))))) =
        (2^32 : F p) * (1 + Expression.eval env (AddMany.highExpr
          (Vector.mapRange 3 fun j => (var {index := i₀ + 32 + j} : Expression (F p))))) := by
      rw [show (2^32 : F p)⁻¹ *
        (Expression.eval env (AddMany.sumExpr input_var.words) +
          Expression.eval env input_var.wide -
          Expression.eval env (fromBitsExpr
            (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))))) =
        1 + Expression.eval env (AddMany.highExpr
          (Vector.mapRange 3 fun j => (var {index := i₀ + 32 + j} : Expression (F p)))) from by
        linear_combination h1]
    rw [← mul_assoc, mul_inv_cancel₀ h_pow32_ne, one_mul] at hmul
    rw [h_sum_eval, h_fz, h_high_eval, h_wide_eval] at hmul
    have hlin : ((SV + input.wide.val : ℕ) : F p) = ((vz + 2^32 * (1 + hi) : ℕ) : F p) := by
      push_cast
      linear_combination hmul
    have h_rhs_lt_p : vz + 2^32 * (1 + hi) < p := by omega
    have h_nat_eq : SV + input.wide.val = vz + 2^32 * (1 + hi) := by
      have hv := congr_arg ZMod.val hlin
      rwa [ZMod.val_natCast_of_lt hS_lt_p, ZMod.val_natCast_of_lt h_rhs_lt_p] at hv
    rw [hSV_def] at h_nat_eq
    simp only [Fin.getElem_fin] at h_nat_eq ⊢
    omega

set_option maxHeartbeats 1000000 in
theorem completeness :
    Completeness (F p) (Input := Inputs n) main Assumptions := by
  circuit_proof_start [addManyWide, main]
  obtain ⟨h_env_z, h_env_cv, -⟩ := h_env
  obtain ⟨h_norm, h_wide_lt⟩ := h_assumptions
  have h_words_eq : eval env.toEnvironment input_var.words = input.words := by rw [← h_input]
  have h_wide_eq : Expression.eval env.toEnvironment input_var.wide = input.wide := by
    rw [← h_input]
  have hn : n ≤ 7 := Fact.out
  have hp_big : (2:ℕ)^37 < p := Fact.out
  have hp32 : (2:ℕ)^32 < p :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hp_big
  set S := sumEvalNat env input_var.words input_var.wide with hS_def
  -- input_var.words[i] evaluates to input.words[i]
  have h_eval_i : ∀ (i : ℕ) (hi : i < n),
      Vector.map (Expression.eval env.toEnvironment) (input_var.words[i]'hi) =
        input.words[i]'hi := by
    intro i hi
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var.words[i]'hi)]
    rw [getElem_eval_vector env.toEnvironment input_var.words i hi, h_words_eq]
  have hsum : (∑ i : Fin n, valueBits input.words[i]) =
      AddMany.sumEvalNat env input_var.words := by
    rw [AddMany.sumEvalNat]
    exact Finset.sum_congr rfl fun i _ =>
      (Add32.evalBitsNat_eq_valueBits env _ _ (h_eval_i i.val i.isLt)).symm
  have h_wide_val : (env input_var.wide).val = input.wide.val := by
    show (Expression.eval env.toEnvironment input_var.wide).val = _
    rw [h_wide_eq]
  -- S equals the ℕ sum of valueBits plus the wide value
  have hSval : (∑ i : Fin n, valueBits input.words[i]) + input.wide.val = S := by
    rw [hS_def, sumEvalNat, hsum, h_wide_val]
  have hSbound : S < 2^36 := by
    rw [← hSval]; exact sum_lt input.words h_norm hn h_wide_lt
  have h_div_lt : S / 2^32 < 2^4 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)]
    calc S < 2^36 := hSbound
      _ = 2^4 * 2^32 := by norm_num
  refine ⟨fun i => ?_, fun j => ?_, ?_⟩
  · -- z boolean
    have h := h_env_z i
    simp only [Vector.getElem_ofFn] at h
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one (S % 2^32 / 2^i.val) with h0 | h0 <;>
      rw [h0] <;> push_cast <;> ring
  · -- high carry boolean
    have h := h_env_cv j
    simp only [Vector.getElem_ofFn] at h
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32 / 2^(j.val+1)) with h0 | h0 <;>
      rw [h0] <;> push_cast <;> ring
  · -- boolean constraint on the affine low-carry expression
    have h_fsumw : Expression.eval env.toEnvironment (AddMany.sumExpr input_var.words) +
        Expression.eval env.toEnvironment input_var.wide = ((S : ℕ) : F p) := by
      rw [AddMany.sumExpr_eval env.toEnvironment input_var.words input.words h_words_eq,
        h_wide_eq,
        show input.wide = ((input.wide.val : ℕ) : F p) from
          (ZMod.natCast_rightInverse input.wide).symm,
        ← Nat.cast_add, hSval]
    have h_S_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [Add32.z_var_eval env.toEnvironment i₀]
      ext i hh
      simp only [Vector.getElem_ofFn]
      have := h_env_z ⟨i, hh⟩
      simp only [Vector.getElem_ofFn] at this
      exact this
    have h_fz : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact fieldFromBits_bitdecomp_gen (S % 2^32) 32 h_S_mod_lt
    have h_hisum : (∑ j : Fin 3, S / 2^32 / 2^(j.val+1) % 2 * 2^(j.val+1))
        = S / 2^32 - S / 2^32 % 2 := by
      have hbd := bit_decomp_high (S / 2^32) 3
      rw [Nat.mod_eq_of_lt h_div_lt] at hbd
      omega
    have h_high_eval : Expression.eval env.toEnvironment (AddMany.highExpr
        (Vector.mapRange 3 fun j => (var {index := i₀ + 32 + j} : Expression (F p)))) =
        ((S / 2^32 - S / 2^32 % 2 : ℕ) : F p) := by
      rw [AddMany.eval_highExpr]
      have hterm : ∀ j : Fin 3,
          Expression.eval env.toEnvironment ((Vector.mapRange 3 fun j =>
              (var {index := i₀ + 32 + j} : Expression (F p)))[j.val]'j.isLt) *
            ((2^(j.val+1) : ℕ) : F p)
          = ((S / 2^32 / 2^(j.val+1) % 2 * 2^(j.val+1) : ℕ) : F p) := by
        intro j
        rw [Vector.getElem_mapRange]
        have henv_j := h_env_cv j
        simp only [Vector.getElem_ofFn] at henv_j
        show env.get (i₀ + 32 + j.val) * _ = _
        rw [henv_j, ← Nat.cast_mul]
      rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Nat.cast_sum, h_hisum]
    have h_pow32_ne : (2^32 : F p) ≠ 0 := by
      intro hz
      have hval : (2^32 : F p).val = 2^32 := by
        rw [show (2^32 : F p) = ((2^32 : ℕ) : F p) from by push_cast; ring,
          ZMod.val_natCast_of_lt hp32]
      rw [hz, ZMod.val_zero] at hval
      norm_num at hval
    rw [h_fsumw, h_fz, h_high_eval]
    -- E = 2^-32·(S − S%2^32) − (q − q%2) = q%2, where q := S / 2^32
    have hq_id : S % 2^32 + 2^32 * (S / 2^32) = S := Nat.mod_add_div S (2^32)
    have hdiff : ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) =
        (2^32 : F p) * ((S / 2^32 : ℕ) : F p) := by
      have hc := congr_arg (Nat.cast : ℕ → F p) hq_id
      rw [Nat.cast_add, Nat.cast_mul,
        show ((2^32 : ℕ) : F p) = (2^32 : F p) from by push_cast; ring] at hc
      linear_combination -hc
    have hinv : (2^32 : F p)⁻¹ * (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) =
        ((S / 2^32 : ℕ) : F p) := by
      rw [hdiff, ← mul_assoc, inv_mul_cancel₀ h_pow32_ne, one_mul]
    have hmod2 : S / 2^32 % 2 + (S / 2^32 - S / 2^32 % 2) = S / 2^32 := by omega
    have hE : (2^32 : F p)⁻¹ * (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) +
        -((S / 2^32 - S / 2^32 % 2 : ℕ) : F p) = ((S / 2^32 % 2 : ℕ) : F p) := by
      have hc := congr_arg (Nat.cast : ℕ → F p) hmod2
      rw [Nat.cast_add] at hc
      have hsub : (2^32 : F p)⁻¹ * (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) =
          (2^32 : F p)⁻¹ * (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) := by ring
      rw [hsub, hinv]
      linear_combination -hc
    rw [show ((2^32 : F p)⁻¹ * (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) +
        -((S / 2^32 - S / 2^32 % 2 : ℕ) : F p)) = ((S / 2^32 % 2 : ℕ) : F p) from hE]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32) with hb | hb <;> rw [hb] <;> norm_num

end
end

def circuit (hn : n ≤ 7) [Fact (p > 2^37)] :
    FormalCircuit (F p) (Inputs n) (fields 32) :=
  haveI : Fact (n ≤ 7) := ⟨hn⟩
  { main := main
    elaborated := elaborated
    Assumptions := Assumptions
    Spec := Spec
    soundness := soundness
    completeness := completeness }

/-! ## Cost certificate

Offset-independent operation count of the raw gadget, in the house style of
`Solution/SHA256/Cost.lean` (`costIs_addMany`): 32 + 3 = 35 witnesses,
32 + 3 + 1 = 36 constraint rows. Stated for a generic prime so it specializes
to `circomPrime` at the composition site. -/

section Cost
open Challenge.CostR1CS

theorem costIs_addManyWide (hn : n ≤ 7)
    (words : Var (ProvableVector (fields 32) n) (F p)) (wide : Var field (F p)) :
    CostIs (addManyWide hn words wide) ⟨35, 36⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
  CostIs.bind (CostIs.witnessVector 3 _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

end Cost

end AddManyWide
end Solution.SHA256
end
