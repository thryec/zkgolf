import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Add32Theorems

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^33)]

namespace Solution.SHA256

/-!
# 32-bit Modular Addition for SHA-256

Adds two 32-bit words (as `fields 32` bit vectors, LSB first) modulo 2^32.

R1CS structure (per call):
- 32 witnesses for output bits z[0..31]
- 32 boolean constraints: z[i] · (z[i] − 1) = 0
- 1  boolean constraint on the affine carry-out

Soundness requires the prime p to exceed 2^33 so that the linear constraint
can distinguish the intended ℕ-level relation from field wraparound.
-/

namespace Add32

/-- Add two 32-bit words mod 2^32.
    Both inputs are assumed to have boolean values in each bit position. -/
def add32 (a b : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- Witness the lower 32 bits of the sum
  let z ← witnessVector 32 fun env =>
    let s := (evalBitsNat env a + evalBitsNat env b) % 2^32
    Vector.ofFn fun (i : Fin 32) => ((s / 2^i.val % 2 : ℕ) : F p)
  -- Boolean constraints on output bits
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  -- Boolean constraint on affine carry-out.
  let carry := ((2^32 : F p)⁻¹ : F p) * (fromBitsExpr a + fromBitsExpr b - fromBitsExpr z)
  assertZero (carry * (carry - 1))
  return z

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  add32 input.a input.b

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = (valueBits input.a + valueBits input.b) % 2^32 ∧ Normalized z

/-!
## Helper lemmas

Gadget-private lemmas (and the `evalBitsNat` helper used by `add32`) live in
`Add32Theorems`. Shared lemmas live in `Theorems`.
-/

/-!
## Soundness
Soundness requires p > 2^33 so the field linear constraint can be lifted to ℕ.
-/

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [add32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  obtain ⟨h_z_bool, h_carry_bool⟩ := h_holds
  rw [z_var_eval env i₀]
  -- Boolean properties
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    normalized_of_bool_holds env i₀ h_z_bool
  refine ⟨?_, h_z_norm⟩
  -- Numeric setup
  have h_p_large := h_large.elim
  have h33 : (2:ℕ)^33 = 2^32 + 2^32 := by norm_num
  have hp32 : (2:ℕ)^32 < p := by omega
  -- Abbreviations
  set vz := valueBits (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) with hvz_def
  have hva_lt : valueBits input_a < 2^32 := valueBits_lt_two_pow input_a ha
  have hvb_lt : valueBits input_b < 2^32 := valueBits_lt_two_pow input_b hb
  have hvz_lt : vz < 2^32 := valueBits_lt_two_pow _ h_z_norm
  -- Field evaluations
  have h_fa : (Expression.eval env (fromBitsExpr input_var_a)).val = valueBits input_a :=
    fromBitsExpr_val_eq env input_var_a input_a h_input_a ha hp32
  have h_fb : (Expression.eval env (fromBitsExpr input_var_b)).val = valueBits input_b :=
    fromBitsExpr_val_eq env input_var_b input_b h_input_b hb hp32
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
      Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := z_var_eval env i₀
  have h_fz : (Expression.eval env (fromBitsExpr
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))))).val = vz :=
    fromBitsExpr_val_eq env _ _ h_z_eval h_z_norm hp32
  -- (2^32 : F p).val = 2^32
  have h_pow32_val : (2^32 : F p).val = 2^32 := by
    have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
    rw [← hcast, ZMod.val_natCast_of_lt hp32]
  have h_pow32_ne : (2^32 : F p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    rw [h_pow32_val, ZMod.val_zero] at hv
    norm_num at hv
  set fsum := Expression.eval env (fromBitsExpr input_var_a) +
    Expression.eval env (fromBitsExpr input_var_b) with hfsum_def
  set fz := Expression.eval env (fromBitsExpr
    (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) with hfz_def
  set carryF := ((2^32 : F p)⁻¹ : F p) * (fsum - fz) with hcarryF_def
  have h_carry_isbool : IsBool carryF := by
    apply isbool_of_bool_constraint
    simpa [carryF, fsum, fz, sub_eq_add_neg] using h_carry_bool
  have h_lin' : fsum = fz + (2^32 : F p) * carryF := by
    rw [hcarryF_def]
    have hmul : (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum - fz)) = fsum - fz := by
      rw [← mul_assoc, mul_inv_cancel₀ h_pow32_ne, one_mul]
    calc
      fsum = fz + (fsum - fz) := by ring
      _ = fz + (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum - fz)) := by rw [hmul]
  set carryVal := carryF.val with hcarryVal_def
  have hcarry_le : carryVal ≤ 1 := by
    rcases IsBool.val_of_IsBool h_carry_isbool with h | h <;> omega
  have h_sum_lt_p : valueBits input_a + valueBits input_b < p := by linarith
  have h_lhs_val : fsum.val = valueBits input_a + valueBits input_b := by
    rw [hfsum_def]
    rw [ZMod.val_add, h_fa, h_fb]
    exact Nat.mod_eq_of_lt h_sum_lt_p
  have h_mul_le : 2^32 * carryVal ≤ 2^32 := by
    calc 2^32 * carryVal ≤ 2^32 * 1 := Nat.mul_le_mul_left _ hcarry_le
      _ = 2^32 := Nat.mul_one _
  have h_mul_lt : 2^32 * carryVal < p := by linarith
  have h_total_lt : vz + 2^32 * carryVal < p := by linarith
  have h_mul_val : ((2^32 : F p) * carryF).val = 2^32 * carryVal := by
    rw [ZMod.val_mul, h_pow32_val, hcarryVal_def]
    rw [Nat.mod_eq_of_lt h_mul_lt]
  have h_rhs_val : (fz + (2^32 : F p) * carryF).val = vz + 2^32 * carryVal := by
    rw [hfz_def]
    rw [ZMod.val_add, h_fz, h_mul_val]
    rw [Nat.mod_eq_of_lt h_total_lt]
  have h_nat_eq : valueBits input_a + valueBits input_b = vz + 2^32 * carryVal := by
    have := congr_arg ZMod.val h_lin'
    rw [h_lhs_val, h_rhs_val] at this
    exact this
  -- Conclude: vz = (valueBits a + valueBits b) % 2^32
  rcases IsBool.val_of_IsBool h_carry_isbool with hc0 | hc1
  · rw [show carryVal = 0 from hc0, Nat.mul_zero, Nat.add_zero] at h_nat_eq
    rw [← h_nat_eq]
    exact (Nat.mod_eq_of_lt (h_nat_eq ▸ hvz_lt)).symm
  · rw [show carryVal = 1 from hc1, Nat.mul_one] at h_nat_eq
    omega

/-!
## Completeness
-/

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [add32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  let h_env_z := h_env
  set S := evalBitsNat env input_var_a + evalBitsNat env input_var_b with hS_def
  have h_p_large := h_large.elim
  have h33 : (2:ℕ)^33 = 2^32 + 2^32 := by norm_num
  have hp32 : (2:ℕ)^32 < p := by linarith
  refine ⟨fun i => ?_, ?_⟩
  · -- Boolean constraint for z[i]: z[i] * (z[i] + -1) = 0
    have henv_i := h_env_z i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S % 2^32 / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · -- Boolean constraint for affine carry.
    -- We prove evalBitsNat env a = valueBits input_a, similarly for b
    have h_evalBits_a : evalBitsNat env input_var_a = valueBits input_a :=
      evalBitsNat_eq_valueBits env input_var_a input_a h_input_a
    have h_evalBits_b : evalBitsNat env input_var_b = valueBits input_b :=
      evalBitsNat_eq_valueBits env input_var_b input_b h_input_b
    have hS_eq : S = valueBits input_a + valueBits input_b := by
      rw [hS_def, h_evalBits_a, h_evalBits_b]
    -- valueBits bounds
    have hva_lt : valueBits input_a < 2^32 := valueBits_lt_two_pow input_a ha
    have hvb_lt : valueBits input_b < 2^32 := valueBits_lt_two_pow input_b hb
    have hS_lt_33 : S < 2^33 := by rw [hS_eq]; linarith
    -- Bit decomposition of S % 2^32: S % 2^32 = ∑ i, (S%2^32 / 2^i % 2) * 2^i
    have h_S_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    -- S / 2^32 ∈ {0, 1} since S < 2^33
    have h_div_le : S / 2^32 ≤ 1 := by
      have hbd : S < 2 * 2^32 := by linarith
      have : S / 2^32 < 2 := (Nat.div_lt_iff_lt_mul (by norm_num)).mpr hbd
      omega
    set q := S / 2^32 with hq_def
    have hq_le : q ≤ 1 := by
      rw [hq_def]
      exact h_div_le
    -- FA = (valueBits input_a : F p)
    have h_FA : Expression.eval env.toEnvironment (fromBitsExpr input_var_a) =
        ((valueBits input_a : ℕ) : F p) :=
      fromBitsExpr_eval_normalized env.toEnvironment input_var_a input_a h_input_a
    have h_FB : Expression.eval env.toEnvironment (fromBitsExpr input_var_b) =
        ((valueBits input_b : ℕ) : F p) :=
      fromBitsExpr_eval_normalized env.toEnvironment input_var_b input_b h_input_b
    -- For FZ, compute via fieldFromBits_eval
    have h_z_eval : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) :=
      z_var_eval env.toEnvironment i₀
    -- z's evaluated bits equal Vector.ofFn (fun i => ((S%2^32/2^i%2 : ℕ) : F p))
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [h_z_eval]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have := h_env_z ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at this
      exact this
    -- Compute FZ using the helper
    have h_FZ : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact fieldFromBits_bit_decomp (S % 2^32) h_S_mod_lt hp32
    have h_pow32_val : (2^32 : F p).val = 2^32 := by
      have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
      rw [← hcast, ZMod.val_natCast_of_lt hp32]
    have h_pow32_ne : (2^32 : F p) ≠ 0 := by
      intro h
      have hv := congrArg ZMod.val h
      rw [h_pow32_val, ZMod.val_zero] at hv
      norm_num at hv
    have hS_decomp : S = S % 2^32 + 2^32 * q := by
      rw [hq_def]
      exact (Nat.mod_add_div S (2^32)).symm
    have h_sub : ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) =
        (2^32 : F p) * ((q : ℕ) : F p) := by
      have hS_decompF : ((S : ℕ) : F p) =
          ((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((q : ℕ) : F p) := by
        calc
          ((S : ℕ) : F p) = ((S % 2^32 + 2^32 * q : ℕ) : F p) := by
            conv_lhs => rw [hS_decomp]
          _ = ((S % 2^32 : ℕ) : F p) + ((2^32 * q : ℕ) : F p) := by
            rw [Nat.cast_add]
          _ = ((S % 2^32 : ℕ) : F p) + ((2^32 : ℕ) : F p) * ((q : ℕ) : F p) := by
            rw [Nat.cast_mul]
          _ = ((S % 2^32 : ℕ) : F p) + (2^32 : F p) * ((q : ℕ) : F p) := by
            rw [show ((2^32 : ℕ) : F p) = (2^32 : F p) from by push_cast; ring]
      rw [hS_decompF]
      ring
    have h_inv : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      rw [h_sub]
      rw [← mul_assoc, inv_mul_cancel₀ h_pow32_ne, one_mul]
    have hS_cast : ((valueBits input_a : ℕ) : F p) + ((valueBits input_b : ℕ) : F p) =
        ((S : ℕ) : F p) := by
      rw [hS_eq, Nat.cast_add]
    rw [h_FA, h_FB, h_FZ, hS_cast]
    rw [show ((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p) =
        ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) by ring]
    rw [h_inv]
    rcases (by omega : q = 0 ∨ q = 1) with hq | hq <;>
      rw [hq] <;> push_cast <;> ring

def circuit [Fact (p > 2^33)] : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Add32
end Solution.SHA256
end
