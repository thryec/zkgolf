import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Challenge.Specs.SHA256
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256
namespace Maj32

/-!
# Helper lemmas for `Maj32`

Gadget-private lemmas for the majority function `Maj(a, b, c)`. Shared lemmas
(`sum_bool_lt_two_pow`, `testBit_binary_sum`, ...) live in `Theorems`.
-/

/-- For boolean field elements a, b, c: the field expression t + c*(a+b-2t) where t=a*b
    has val equal to the bitwise Nat majority of a.val, b.val, c.val -/
lemma maj_eq_val_maj {p : ℕ} [Fact p.Prime]
    {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (a * b + c * (a + b - 2 * (a * b))).val = (a.val &&& b.val) ^^^ (a.val &&& c.val) ^^^ (b.val &&& c.val) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    norm_num [ha, hb, hc, ZMod.val_zero, ZMod.val_one]

/-- For boolean field elements a, b, c: the field expression t + c*(a+b-2t) where t=a*b
    is boolean -/
lemma maj_is_bool {α : Type*} [Ring α] {a b c : α} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (a * b + c * (a + b - 2 * (a * b))) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    simp [ha, hb, hc] <;> norm_num <;> first | exact IsBool.zero | exact IsBool.one

omit [Fact (p > 2^35)] in
/-- A boolean constraint `x·(x + −1) = 0` witnesses that `x` is boolean. -/
lemma isbool_of_constraint {x : F p} (h : x * (x + -1) = 0) : IsBool x :=
  IsBool.iff_mul_sub_one.mpr (by rw [show x - 1 = x + -1 from by ring]; exact h)

/-- Single-witness decomposition recovery: if `a, b, c, z` are boolean and the
    parity constraint `(a + b + c − 2z)·(a + b + c − 2z − 1) = 0` holds, then `z`
    equals the standard majority value `a·b + c·(a + b − 2·a·b)`. This needs the
    field characteristic to exceed 6 (guaranteed by `p > 2^35`). -/
lemma maj_of_decomp {a b c z : F p}
    (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) (hz : IsBool z)
    (hd : (a + b + c - 2 * z) * (a + b + c - 2 * z - 1) = 0) :
    z = a * b + c * (a + b - 2 * (a * b)) := by
  have small_ne : ∀ k : ℕ, 0 < k → k ≤ 6 → ((k : ℕ) : F p) ≠ 0 := by
    intro k hk0 hk6 h
    have hkp : k < p := lt_of_le_of_lt hk6 (lt_trans (by norm_num : (6 : ℕ) < 2 ^ 35) Fact.out)
    have hval : ((k : ℕ) : F p).val = k := ZMod.val_natCast_of_lt hkp
    rw [h, ZMod.val_zero] at hval
    omega
  have h2 : (2 : F p) ≠ 0 := by
    have h := small_ne 2 (by norm_num) (by norm_num); rwa [Nat.cast_ofNat] at h
  have h6 : (6 : F p) ≠ 0 := by
    have h := small_ne 6 (by norm_num) (by norm_num); rwa [Nat.cast_ofNat] at h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hz with rfl | rfl
  all_goals try ring1
  all_goals (exfalso; norm_num at hd; first | exact h2 hd | exact h6 hd)

/-- Single-constraint majority (from Verified-zkEVM/clean#395): from the one R1CS row
    `(o + a + b − 9c + 3)·(a + b + 6c − 4) + 12 = 0` with `a, b, c` boolean, the
    witnessed output `o` is *uniquely* pinned to the majority `a·b + c·(a + b − 2·a·b)`
    (no separate booleanity row needed). The multiplier `a + b + 6c − 4` only takes the
    values `±2, ±3, ±4` on the boolean cube, so it never vanishes for `p > 2^35`. -/
lemma maj3_unique {a b c o : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c)
    (h : (o + a + b - 9 * c + 3) * (a + b + 6 * c - 4) + 12 = 0) :
    o = a * b + c * (a + b - 2 * (a * b)) := by
  have ha' : a * (a - 1) = 0 := by rcases ha with h | h <;> rw [h] <;> ring
  have hb' : b * (b - 1) = 0 := by rcases hb with h | h <;> rw [h] <;> ring
  have hc' : c * (c - 1) = 0 := by rcases hc with h | h <;> rw [h] <;> ring
  -- The constraint factors as `(o − maj) · (a + b + 6c − 4)` modulo the boolean relations.
  have key : (o - (a * b + c * (a + b - 2 * (a * b)))) * (a + b + 6 * c - 4) = 0 := by
    linear_combination h - (-2 * b * c + b + c + 1) * ha'
      - (-2 * a * c + a + c + 1) * hb' - (-12 * a * b + 6 * a + 6 * b - 54) * hc'
  -- The multiplier is nonzero (its boolean values are `±2, ±3, ±4`).
  have hp : 2 ^ 35 < p := Fact.out
  have hval : ∀ k : ℕ, 0 < k → k < p → ((k : ℕ) : F p) ≠ 0 := by
    intro k hk hkp hcon
    have := congrArg ZMod.val hcon
    rw [ZMod.val_natCast_of_lt hkp, ZMod.val_zero] at this; omega
  have h2 : (2 : F p) ≠ 0 := by have := hval 2 (by norm_num) (by omega); simpa using this
  have h3 : (3 : F p) ≠ 0 := by have := hval 3 (by norm_num) (by omega); simpa using this
  have h4 : (4 : F p) ≠ 0 := by have := hval 4 (by norm_num) (by omega); simpa using this
  have hM : (a + b + 6 * c - 4 : F p) ≠ 0 := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
      intro hcon <;>
      first
        | exact h2 (by linear_combination hcon)
        | exact h2 (by linear_combination -hcon)
        | exact h3 (by linear_combination hcon)
        | exact h3 (by linear_combination -hcon)
        | exact h4 (by linear_combination hcon)
        | exact h4 (by linear_combination -hcon)
  rcases mul_eq_zero.mp key with h1 | h1
  · linear_combination h1
  · exact absurd h1 hM

lemma bool_finsum_maj (n : ℕ) (f g k : Fin n → ℕ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) (hg : ∀ i, g i = 0 ∨ g i = 1) (hk : ∀ i, k i = 0 ∨ k i = 1) :
    ((∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val)) ^^^
    ((∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val)) ^^^
    ((∑ i : Fin n, g i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val))
    = ∑ i : Fin n, ((f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i)) * 2^i.val := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i &&& g i) = 0 ∨ (f i &&& g i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    have hfk : ∀ i : Fin n, (f i &&& k i) = 0 ∨ (f i &&& k i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hk i with hki | hki <;> simp [hfi, hki]
    have hgk : ∀ i : Fin n, (g i &&& k i) = 0 ∨ (g i &&& k i) = 1 := fun i => by
      rcases hg i with hgi | hgi <;> rcases hk i with hki | hki <;> simp [hgi, hki]
    have hmaj : ∀ i : Fin n, (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i) = 0 ∨
        (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> rcases hk i with hki | hki <;>
        simp [hfi, hgi, hki]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
        testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
        testBit_binary_sum n k hk ⟨j, hj⟩,
        testBit_binary_sum n _ hmaj ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;>
      rcases hk ⟨j, hj⟩ with hki | hki <;> simp [hfi, hgi, hki]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hfS := sum_bool_lt_two_pow n f (fun i => by rcases hf i with hx | hx <;> simp [hx])
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with hx | hx <;> simp [hx])
    have hkS := sum_bool_lt_two_pow n k (fun i => by rcases hk i with hx | hx <;> simp [hx])
    have hmajS := sum_bool_lt_two_pow n (fun i => (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i))
        (fun i => by
          have hfi := hf i; have hgi := hg i; have hki := hk i
          rcases hfi with hfi | hfi <;> rcases hgi with hgi | hgi <;> rcases hki with hki | hki <;>
            simp [hfi, hgi, hki])
    have hand1 : (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hfS
    have hand2 : (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hfS
    have hand3 : (∑ i : Fin n, g i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hgS
    have hxor12 := Nat.xor_lt_two_pow hand1 hand2
    have hxor_all := Nat.xor_lt_two_pow hxor12 hand3
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hxor_all pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hmajS pow_le)]

omit [Fact (p > 2^35)] in
/-- Spec holds for any vector `z` whose bits satisfy the per-bit constraint. -/
lemma spec_of_constraint
    (input_a input_b input_c z : fields 32 (F p))
    (ha : Normalized input_a) (hb : Normalized input_b) (hc : Normalized input_c)
    (h_eq : ∀ i : Fin 32, z[i] =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i]))) :
    valueBits z = Specs.SHA256.Maj (valueBits input_a) (valueBits input_b) (valueBits input_c) ∧
    Normalized z := by
  have ha_b : ∀ i : Fin 32, IsBool input_a[i] := fun i => ha i
  have hb_b : ∀ i : Fin 32, IsBool input_b[i] := fun i => hb i
  have hc_b : ∀ i : Fin 32, IsBool input_c[i] := fun i => hc i
  have h_norm : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := by
    intro i; rw [h_eq i]; exact maj_is_bool (ha_b i) (hb_b i) (hc_b i)
  have ha_val : ∀ i : Fin 32, (input_a[i] : F p).val = 0 ∨ (input_a[i] : F p).val = 1 :=
    fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hb_val : ∀ i : Fin 32, (input_b[i] : F p).val = 0 ∨ (input_b[i] : F p).val = 1 :=
    fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc_val : ∀ i : Fin 32, (input_c[i] : F p).val = 0 ∨ (input_c[i] : F p).val = 1 :=
    fun i => by rcases hc i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_bit_eq : ∀ i : Fin 32, (z[i] : F p).val =
      ((input_a[i] : F p).val &&& (input_b[i] : F p).val) ^^^
      ((input_a[i] : F p).val &&& (input_c[i] : F p).val) ^^^
      ((input_b[i] : F p).val &&& (input_c[i] : F p).val) := by
    intro i; rw [h_eq i]; exact maj_eq_val_maj (ha_b i) (hb_b i) (hc_b i)
  have key' : ((∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val)) ^^^
      ((∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val)) ^^^
      ((∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val)) =
      ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := by
    rw [bool_finsum_maj 32 _ _ _ ha_val hb_val hc_val]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_bit_eq i]
  have Maj_def : ∀ a b c : ℕ, Specs.SHA256.Maj a b c = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) :=
    fun _ _ _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  have ha_eq : valueBits input_a = ∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val := rfl
  have hb_eq : valueBits input_b = ∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val := rfl
  have hc_eq : valueBits input_c = ∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_norm⟩
  rw [Maj_def, ha_eq, hb_eq, hc_eq, h_z_eq]
  exact key'.symm

end Maj32
end Solution.SHA256
end
