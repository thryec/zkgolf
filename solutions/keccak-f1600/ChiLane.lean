import Solution.KeccakF1600.BitwiseOps
import Solution.KeccakF1600.Theorems
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 3)]

namespace Solution.KeccakF1600

namespace ChiLane

/-!
# χ step, one R1CS row per bit

Per bit: `z = a XOR ((NOT b) AND c)`. For boolean `a, b, c` the single row

  `(4a + 2b) − (z + 3a − b − c)·(4a + b + c − 3) = 0`

pins `z` uniquely: the multiplier `4a + b + c − 3` takes values `±1, ±2, ±3`
(never `0` when `p > 3`), so no separate booleanity row is needed.
-/

/-- Field encoding of `a XOR ((NOT b) AND c)` for boolean field elements. -/
def fieldChi (a b c : F p) : F p := a + (1 - b) * c - 2 * a * ((1 - b) * c)

omit [Fact (p > 3)] in
lemma one_sub_is_bool {b : F p} (hb : IsBool b) : IsBool (1 - b) := by
  rcases hb with hb | hb <;> simp [hb, IsBool]

omit [Fact (p > 3)] in
lemma one_sub_val {b : F p} (hb : IsBool b) : (1 - b).val = 1 - b.val := by
  rcases hb with hb | hb <;> simp [hb, ZMod.val_one, ZMod.val_zero]

omit [Fact (p > 3)] in
lemma natCast_ne_zero_of_pos_lt {n : ℕ} (h0 : 0 < n) (hp : n < p) :
    ((n : ℕ) : F p) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hp, ZMod.val_zero] at hv
  omega

omit [Fact (p > 3)] in
lemma fieldChi_is_bool {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (fieldChi a b c) :=
  IsBool.xor_is_bool ha (IsBool.and_is_bool (one_sub_is_bool hb) hc)

omit [Fact (p > 3)] in
lemma fieldChi_val {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (fieldChi a b c).val = a.val ^^^ ((1 - b.val) &&& c.val) := by
  unfold fieldChi
  rw [IsBool.xor_eq_val_xor ha (IsBool.and_is_bool (one_sub_is_bool hb) hc),
      IsBool.and_eq_val_and (one_sub_is_bool hb) hc, one_sub_val hb]

omit [Fact (p > 3)] in
/-- The nat computation cast into the field equals `fieldChi`. -/
lemma fieldChi_val_cast_eq {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (((a.val ^^^ ((1 - b.val) &&& c.val) : ℕ) : F p)) = fieldChi a b c := by
  rw [← fieldChi_val ha hb hc, ZMod.natCast_val]
  exact ZMod.cast_id p _

omit [Fact (p > 3)] in
lemma chi_row_of_bool {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (4*a + 2*b) - (fieldChi a b c + 3*a - b - c) * (4*a + b + c - 3) = 0 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    simp only [fieldChi, ha, hb, hc] <;> ring

lemma chi_unique {a b c z : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c)
    (h : (4*a + 2*b) - (z + 3*a - b - c) * (4*a + b + c - 3) = 0) :
    z = fieldChi a b c := by
  have hp : (3 : ℕ) < p := Fact.out
  have h1 : (1 : F p) ≠ 0 := one_ne_zero
  have h2 : (2 : F p) ≠ 0 := by
    have := natCast_ne_zero_of_pos_lt (p := p) (n := 2) (by norm_num) (by omega)
    exact_mod_cast this
  have h3 : (3 : F p) ≠ 0 := by
    have := natCast_ne_zero_of_pos_lt (p := p) (n := 3) (by norm_num) (by omega)
    exact_mod_cast this
  have key : ∀ x : F p, (x = 3 ∨ x = 2 ∨ x = 1 ∨ x = -1 ∨ x = -2 ∨ x = -3) → x ≠ 0 := by
    rintro x (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact h3
    · exact h2
    · exact h1
    · exact neg_ne_zero.mpr h1
    · exact neg_ne_zero.mpr h2
    · exact neg_ne_zero.mpr h3
  have hM : (4*a + b + c - 3 : F p) ≠ 0 := by
    apply key
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      rw [ha, hb, hc]
    · right; right; right; right; right; ring
    · right; right; right; right; left; ring
    · right; right; right; right; left; ring
    · right; right; right; left; ring
    · right; right; left; ring
    · right; left; ring
    · right; left; ring
    · left; ring
  have hrow := chi_row_of_bool ha hb hc
  have factored : (z - fieldChi a b c) * (4*a + b + c - 3) = 0 := by
    linear_combination hrow - h
  exact sub_eq_zero.mp ((mul_eq_zero.mp factored).resolve_right hM)

/-- χ of a 64-bit lane, one R1CS row per output bit. -/
def chiLane (a b c : Var (fields 64) (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let z ← witnessVector 64 fun env =>
    Vector.ofFn fun (i : Fin 64) =>
      (((env a[i]).val ^^^ ((1 - (env b[i]).val) &&& (env c[i]).val) : ℕ) : F p)
  Circuit.forEach (Vector.finRange 64) fun i =>
    assertZero ((4*a[i] + 2*b[i]) - (z[i] + 3*a[i] - b[i] - c[i]) * (4*a[i] + b[i] + c[i] - 3))
  return z

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
  c : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) :=
  chiLane input.a input.b input.c

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z =
    (valueBits input.a ^^^
      (Specs.Keccak.notLane 64 (valueBits input.b) &&& valueBits input.c))
  ∧ Normalized z

omit [Fact (p > 3)] in
lemma spec_of_constraint
    (input_a input_b input_c z : fields 64 (F p))
    (ha : Normalized input_a) (hb : Normalized input_b) (hc : Normalized input_c)
    (h_eq : ∀ i : Fin 64, z[i] = fieldChi input_a[i] input_b[i] input_c[i]) :
    valueBits z =
      (valueBits input_a ^^^
        (Specs.Keccak.notLane 64 (valueBits input_b) &&& valueBits input_c))
    ∧ Normalized z := by
  have hnb : Normalized (notBits input_b) := Normalized_notBits input_b hb
  have h_norm : Normalized z := by
    intro i; rw [h_eq i]; exact fieldChi_is_bool (ha i) (hb i) (hc i)
  have hnbi : ∀ i : Fin 64, (notBits input_b)[i].val = 1 - input_b[i].val := by
    intro i
    rw [show (notBits input_b)[i] = 1 - input_b[i] from by simp [notBits, Vector.getElem_map]]
    exact one_sub_val (hb i)
  have hz_val : ∀ i : Fin 64,
      z[i].val = input_a[i].val ^^^ ((notBits input_b)[i].val &&& input_c[i].val) := by
    intro i
    rw [h_eq i, fieldChi_val (ha i) (hb i) (hc i), hnbi i]
  refine ⟨?_, h_norm⟩
  have key1 := bool_finsum_xor_eq 64
    (fun i => input_a[i].val)
    (fun i => (notBits input_b)[i].val &&& input_c[i].val)
    (fun i => ha.val_bool i)
    (fun i => IsBool.land_inherit_left _ _ (hnb.val_bool i))
  have key2 := bool_finsum_and 64
    (fun i => (notBits input_b)[i].val)
    (fun i => input_c[i].val)
    (fun i => hnb.val_bool i)
    (fun i => hc.val_bool i)
  calc valueBits z
      = ∑ i : Fin 64, z[i].val * 2^i.val := rfl
    _ = ∑ i : Fin 64,
          (input_a[i].val ^^^ ((notBits input_b)[i].val &&& input_c[i].val)) * 2^i.val := by
          apply Finset.sum_congr rfl; intro i _; rw [hz_val i]
    _ = (∑ i : Fin 64, input_a[i].val * 2^i.val) ^^^
          (∑ i : Fin 64, ((notBits input_b)[i].val &&& input_c[i].val) * 2^i.val) := key1
    _ = valueBits input_a ^^^ (valueBits (notBits input_b) &&& valueBits input_c) := by
          rw [← key2]; rfl
    _ = valueBits input_a ^^^
          (Specs.Keccak.notLane 64 (valueBits input_b) &&& valueBits input_c) := by
          rw [valueBits_notBits input_b hb]

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [chiLane]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 64, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this
    exact this
  have h_bi : ∀ i : Fin 64, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this
    exact this
  have h_ci : ∀ i : Fin 64, Expression.eval env input_var_c[i.val] = input_c[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_c i i.isLt
    simp [Vector.getElem_map] at this
    exact this
  have h_eq : ∀ i : Fin 64, env.get (i₀ + i.val) =
      fieldChi input_a[i] input_b[i] input_c[i] := by
    intro i
    have h := h_holds i
    rw [h_ai i, h_bi i, h_ci i] at h
    refine chi_unique (ha i) (hb i) (hc i) ?_
    linear_combination h
  set z : fields 64 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 64 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_z : ∀ i : Fin 64, z[i] = env.get (i₀ + i.val) := by
    intro i
    simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_eq' : ∀ i : Fin 64, z[i] = fieldChi input_a[i] input_b[i] input_c[i] := by
    intro i; rw [h_z i]; exact h_eq i
  exact spec_of_constraint input_a input_b input_c z ha hb hc h_eq'

omit [Fact (p > 3)] in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [chiLane]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this
    exact this
  have h_bi : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this
    exact this
  have h_ci : ∀ i : Fin 64, Expression.eval env.toEnvironment input_var_c[i.val] = input_c[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_c i i.isLt
    simp [Vector.getElem_map] at this
    exact this
  intro i
  have henv := h_env i
  simp only [Vector.getElem_ofFn] at henv
  rw [h_ai i, h_bi i, h_ci i] at henv
  rw [henv, h_ai i, h_bi i, h_ci i]
  rw [fieldChi_val_cast_eq (ha i) (hb i) (hc i)]
  linear_combination chi_row_of_bool (ha i) (hb i) (hc i)

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ChiLane
end Solution.KeccakF1600
end
