import Solution.KeccakF1600.BitwiseOps
import Solution.KeccakF1600.Theorems
import Challenge.Utils.CostR1CS

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 3)]

namespace Solution.KeccakF1600

namespace Xor3Lane

open Challenge.CostR1CS

/-!
# 3-input 64-bit bitwise XOR for Keccak θ

Per bit: one R1CS row pins `z = a XOR b XOR c`, assuming boolean inputs.

  `(6a + 6b − 24c) − (z + 2a + 2b + 7c)·(a + b − 4c + 1) = 0`

The multiplier `a + b − 4c + 1` takes values `±1, ±2, ±3` (never `0` when `p > 3`),
so no separate booleanity row is needed.
-/

/-- Field encoding of `(a XOR b) XOR c` for boolean field elements. -/
def fieldXor3 (a b c : F p) : F p :=
  a + b - 2 * a * b + c - 2 * (a + b - 2 * a * b) * c

/-- 3-input bitwise XOR of 64-bit words, with one R1CS row per output bit. -/
def xor3 (a b c : Var (fields 64) (F p)) : Circuit (F p) (Var (fields 64) (F p)) := do
  let z ← witnessVector 64 fun env =>
    Vector.ofFn fun (i : Fin 64) =>
      (((env a[i]).val ^^^ (env b[i]).val ^^^ (env c[i]).val : ℕ) : F p)
  Circuit.forEach (Vector.finRange 64) fun i =>
    assertZero (6 * a[i] + 6 * b[i] - 24 * c[i]
      - (z[i] + 2 * a[i] + 2 * b[i] + 7 * c[i]) * (a[i] + b[i] - 4 * c[i] + 1))
  return z

structure Inputs (F : Type) where
  a : fields 64 F
  b : fields 64 F
  c : fields 64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 64) (F p)) :=
  xor3 input.a input.b input.c

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 64 (F p)) : Prop :=
  valueBits z = valueBits input.a ^^^ valueBits input.b ^^^ valueBits input.c ∧ Normalized z

omit [Fact (p > 3)] in
lemma natCast_ne_zero_of_pos_lt {n : ℕ} (h0 : 0 < n) (hp : n < p) :
    ((n : ℕ) : F p) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hp, ZMod.val_zero] at hv
  omega

omit [Fact (p > 3)] in
lemma eq_zero_of_mul_eq_zero {k x : F p} (hk : k ≠ 0) (h : k * x = 0) : x = 0 := by
  exact (mul_eq_zero.mp h).resolve_left hk

omit [Fact (p > 3)] in
lemma eq_one_of_mul_sub_eq_zero {k x : F p} (hk : k ≠ 0) (h : k * (x - 1) = 0) :
    x = 1 := by
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hk)

lemma xor3_unique {a b c o : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c)
    (h : (o + 2 * a + 2 * b + 7 * c) * (a + b - 4 * c + 1) -
      (6 * a + 6 * b - 24 * c) = 0) :
    o = fieldXor3 a b c := by
  have hp : (3 : ℕ) < p := Fact.out
  have h1 : (1 : F p) ≠ 0 := one_ne_zero
  have h2 : (2 : F p) ≠ 0 := by
    have := natCast_ne_zero_of_pos_lt (p := p) (n := 2) (by norm_num) (by omega)
    exact_mod_cast this
  have h3 : (3 : F p) ≠ 0 := by
    have := natCast_ne_zero_of_pos_lt (p := p) (n := 3) (by norm_num) (by omega)
    exact_mod_cast this
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  all_goals
    rw [ha, hb, hc] at h ⊢
    norm_num [fieldXor3] at h ⊢
  · exact h
  · apply eq_one_of_mul_sub_eq_zero h3
    have hneg := congrArg Neg.neg h
    ring_nf at hneg ⊢
    exact hneg
  · apply eq_one_of_mul_sub_eq_zero h2
    ring_nf at h ⊢
    exact h
  · apply eq_zero_of_mul_eq_zero h2
    have hneg := congrArg Neg.neg h
    ring_nf at hneg ⊢
    exact hneg
  · apply eq_one_of_mul_sub_eq_zero h2
    ring_nf at h ⊢
    exact h
  · apply eq_zero_of_mul_eq_zero h2
    have hneg := congrArg Neg.neg h
    ring_nf at hneg ⊢
    exact hneg
  · apply eq_zero_of_mul_eq_zero h3
    ring_nf at h ⊢
    exact h
  · apply eq_one_of_mul_sub_eq_zero h1
    have hneg := congrArg Neg.neg h
    ring_nf at hneg ⊢
    exact hneg

omit [Fact (p > 3)] in
lemma fieldXor3_is_bool {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (fieldXor3 a b c) := by
  unfold fieldXor3
  exact IsBool.xor_is_bool (IsBool.xor_is_bool ha hb) hc

omit [Fact (p > 3)] in
lemma fieldXor3_val {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (fieldXor3 a b c).val = a.val ^^^ b.val ^^^ c.val := by
  unfold fieldXor3
  rw [IsBool.xor_eq_val_xor (IsBool.xor_is_bool ha hb) hc, IsBool.xor_eq_val_xor ha hb]

omit [Fact (p > 3)] in
lemma xor3_val_cast_eq {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (((a.val ^^^ b.val ^^^ c.val : ℕ) : F p)) = fieldXor3 a b c := by
  rw [← IsBool.xor_eq_val_xor ha hb]
  rw [← IsBool.xor_eq_val_xor (IsBool.xor_is_bool ha hb) hc]
  change (((fieldXor3 a b c).val : ℕ) : F p) = fieldXor3 a b c
  rw [ZMod.natCast_val]
  exact ZMod.cast_id p _

omit [Fact (p > 3)] in
lemma xor3_row_of_bool {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    6 * a + 6 * b - 24 * c -
      (fieldXor3 a b c + 2 * a + 2 * b + 7 * c) * (a + b - 4 * c + 1) = 0 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  all_goals
    norm_num [fieldXor3, ha, hb, hc]

lemma bool_finsum_xor3_eq (n : ℕ) (f g k : Fin n → ℕ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) (hg : ∀ i, g i = 0 ∨ g i = 1)
    (hk : ∀ i, k i = 0 ∨ k i = 1) :
    ∑ i : Fin n, (f i ^^^ g i ^^^ k i) * 2^i.val =
    (∑ i : Fin n, f i * 2^i.val) ^^^ (∑ i : Fin n, g i * 2^i.val) ^^^
    (∑ i : Fin n, k i * 2^i.val) := by
  have hfg : ∀ i : Fin n, (f i ^^^ g i) = 0 ∨ (f i ^^^ g i) = 1 := by
    intro i
    rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
  calc
    ∑ i : Fin n, (f i ^^^ g i ^^^ k i) * 2^i.val =
        (∑ i : Fin n, (f i ^^^ g i) * 2^i.val) ^^^
          (∑ i : Fin n, k i * 2^i.val) := bool_finsum_xor_eq n (fun i => f i ^^^ g i) k hfg hk
    _ = (∑ i : Fin n, f i * 2^i.val) ^^^ (∑ i : Fin n, g i * 2^i.val) ^^^
          (∑ i : Fin n, k i * 2^i.val) := by
        rw [bool_finsum_xor_eq n f g hf hg]

omit [Fact (p > 3)] in
lemma spec_of_constraint
    (input_a input_b input_c z : fields 64 (F p))
    (ha : Normalized input_a) (hb : Normalized input_b) (hc : Normalized input_c)
    (h_eq : ∀ i : Fin 64, z[i] = fieldXor3 input_a[i] input_b[i] input_c[i]) :
    valueBits z = valueBits input_a ^^^ valueBits input_b ^^^ valueBits input_c ∧
    Normalized z := by
  have h_norm : Normalized z := by
    intro i
    rw [h_eq i]
    exact fieldXor3_is_bool (ha i) (hb i) (hc i)
  have ha_val : ∀ i : Fin 64, (input_a[i] : F p).val = 0 ∨ (input_a[i] : F p).val = 1 :=
    fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hb_val : ∀ i : Fin 64, (input_b[i] : F p).val = 0 ∨ (input_b[i] : F p).val = 1 :=
    fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc_val : ∀ i : Fin 64, (input_c[i] : F p).val = 0 ∨ (input_c[i] : F p).val = 1 :=
    fun i => by rcases hc i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_bit_eq : ∀ i : Fin 64, (z[i] : F p).val =
      (input_a[i] : F p).val ^^^ (input_b[i] : F p).val ^^^ (input_c[i] : F p).val := by
    intro i
    rw [h_eq i]
    exact fieldXor3_val (ha i) (hb i) (hc i)
  refine ⟨?_, h_norm⟩
  calc
    valueBits z = ∑ i : Fin 64, (z[i] : F p).val * 2^i.val := rfl
    _ = ∑ i : Fin 64,
          ((input_a[i] : F p).val ^^^ (input_b[i] : F p).val ^^^
            (input_c[i] : F p).val) * 2^i.val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [h_bit_eq i]
    _ = valueBits input_a ^^^ valueBits input_b ^^^ valueBits input_c :=
        bool_finsum_xor3_eq 64
          (fun i => (input_a[i] : F p).val)
          (fun i => (input_b[i] : F p).val)
          (fun i => (input_c[i] : F p).val)
          ha_val hb_val hc_val

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 64) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [xor3]
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
      fieldXor3 input_a[i] input_b[i] input_c[i] := by
    intro i
    have h := h_holds i
    rw [h_ai i, h_bi i, h_ci i] at h
    apply xor3_unique (ha i) (hb i) (hc i)
    have hneg := congrArg Neg.neg h
    ring_nf at hneg ⊢
    exact hneg
  set z : fields 64 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 64 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_z : ∀ i : Fin 64, z[i] = env.get (i₀ + i.val) := by
    intro i
    simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_eq' : ∀ i : Fin 64, z[i] = fieldXor3 input_a[i] input_b[i] input_c[i] := by
    intro i
    rw [h_z i]
    exact h_eq i
  exact spec_of_constraint input_a input_b input_c z ha hb hc h_eq'

omit [Fact (p > 3)] in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [xor3]
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
  rw [xor3_val_cast_eq (ha i) (hb i) (hc i)]
  have hrow := xor3_row_of_bool (ha i) (hb i) (hc i)
  ring_nf at hrow ⊢
  exact hrow

def circuit : FormalCircuit (F p) Inputs (fields 64) where
  main; elaborated; Assumptions; Spec; soundness; completeness

omit [Fact (p > 3)] in
theorem costIs_xor3 (a b c : Var (fields 64) (F p)) :
    CostIs (xor3 a b c) ⟨64, 64⟩ :=
  CostIs.bind (CostIs.witnessVector 64 _) fun z =>
    CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ => CostIs.pure z

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

omit [Fact (p > 3)] in
theorem r1cs_xor3 (a b c : Var (fields 64) (F p))
    (ha : AffineW a) (hb : AffineW b) (hc : AffineW c) :
    IsR1CSCirc (xor3 a b c) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 64 _) fun n =>
    IsR1CSCirc.bind
      (IsR1CSCirc.forEach fun j m =>
        IsR1CSCirc.assertZero
          (isR1CSRow_sub_mul
            (Affine.sub
              (Affine.add (Affine.fconst_mul 6 (ha j.val j.isLt))
                (Affine.fconst_mul 6 (hb j.val j.isLt)))
              (Affine.fconst_mul 24 (hc j.val j.isLt)))
            (Affine.add
              (Affine.add
                (Affine.add (affineW_witnessVector_output 64 _ n j.val j.isLt)
                  (Affine.fconst_mul 2 (ha j.val j.isLt)))
                (Affine.fconst_mul 2 (hb j.val j.isLt)))
              (Affine.fconst_mul 7 (hc j.val j.isLt)))
            (Affine.add
              (Affine.sub
                (Affine.add (ha j.val j.isLt) (hb j.val j.isLt))
                (Affine.fconst_mul 4 (hc j.val j.isLt)))
              (Affine.const 1))) m)
      (fun _ => IsR1CSCirc.pure _)

end Xor3Lane
end Solution.KeccakF1600
end
