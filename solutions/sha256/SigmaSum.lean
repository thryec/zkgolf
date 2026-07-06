import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Xor3
import Solution.SHA256.AddMany
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-! ## Generic bit-decomposition helpers (arbitrary bit length) -/

omit [Fact (Nat.Prime p)] [Fact (p > 2^35)] in
/-- Bit decomposition: `∑ i, (m / 2^i % 2) * 2^i = m` for `m < 2^len`. -/
lemma bit_decomp_sum_gen (m len : ℕ) (h_lt : m < 2^len) :
    ∑ i : Fin len, m / 2^i.val % 2 * 2^i.val = m := by
  conv_rhs => rw [← Utils.Bits.fromBits_toBits h_lt]
  unfold Utils.Bits.fromBits Utils.Bits.toBits
  rw [Fin.foldl_to_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_mapRange, Add32.testBit_ite_eq]

omit [Fact (p > 2^35)] in
/-- `fieldFromBits` of the bit decomposition of `m < 2^len` equals `(m : F p)`. -/
lemma fieldFromBits_bitdecomp_gen (m len : ℕ) (h_lt : m < 2^len) :
    Utils.Bits.fieldFromBits (Vector.ofFn fun i : Fin len => ((m / 2^i.val % 2 : ℕ) : F p)) =
      ((m : ℕ) : F p) := by
  simp only [Utils.Bits.fieldFromBits, Utils.Bits.fromBits, Fin.foldl_to_sum]
  have h_val_eq : ∀ i : Fin len, ((Vector.ofFn fun j : Fin len =>
      ((m / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] = m / 2^i.val % 2 := by
    intro i
    simp only [Vector.getElem_map, Vector.getElem_ofFn]
    have hbit_lt : m / 2^i.val % 2 < p := by
      have : m / 2^i.val % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
      omega
    exact ZMod.val_natCast_of_lt hbit_lt
  have h_sum_eq : ∑ i : Fin len, ((Vector.ofFn fun j : Fin len =>
        ((m / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] * 2^i.val = m := by
    calc ∑ i : Fin len, ((Vector.ofFn fun j : Fin len =>
            ((m / 2^j.val % 2 : ℕ) : F p)).map ZMod.val)[i.val] * 2^i.val
        = ∑ i : Fin len, m / 2^i.val % 2 * 2^i.val := by
          apply Finset.sum_congr rfl
          intro i _; rw [h_val_eq i]
      _ = m := bit_decomp_sum_gen m len h_lt
  rw [h_sum_eq]

/-!
# Helpers for the σ-paired schedule step (`ScheduleStep`)

The fused schedule step computes both lower sigmas and the 4-word modular
addition in one monolithic gadget (91 witnesses / 92 rows instead of 97/98).
The saving comes from pairing the 13 two-input XOR lanes (σ₀ lanes 29–31 have
no `shr3` bit, σ₁ lanes 22–31 no `shr10` bit) two-at-a-time into a single
witness and a single determined R1CS row via the identity (for boolean
`a b c d` and `λ = 4^m`, `m ∈ {0,1}`):

  xor2(a,b) + λ·xor2(c,d)
    = (2a − 2b + 2λ(c+d) − 1) − (2^m(c+d) − (1−a+b))·(2^m(c+d) + (1−a+b)).

This file holds the generic ingredients:
* cast-form value lemmas for the XOR3 parity row, the plain 2-input row and
  the two pair rows (`parity_cast`, `xor2_cast`, `pair_val4`, `pair_val1`);
* `bitsFn`/range-sum bridges for `valueBits` and the 3-input XOR of bit sums;
* the weighted-sum regrouping lemma `regroup_sum` that redistributes the
  paired lanes back onto the two σ bit-columns;
* the packed linear-combination vector `tVec` (the `t_i` column entries of the
  fused adder row) with its per-entry `getElem` lemmas;
* the ℕ-level witness-generator helpers `lane0`/`lane1`/`schedSumNat`.
-/

namespace SigmaSum

/-! ## Small-value casts and boolean XOR bounds -/

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma isBool_nat_le_one {n : ℕ} (h : IsBool n) : n ≤ 1 := by
  rcases h with rfl | rfl <;> omega

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma xor_le_one {x y : ℕ} (hx : x ≤ 1) (hy : y ≤ 1) : x ^^^ y ≤ 1 := by
  have hx' : x = 0 ∨ x = 1 := by omega
  have hy' : y = 0 ∨ y = 1 := by omega
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> simp

/-- Casting a small (`< 2^35`) natural to `F p` is injective on values. -/
lemma val_cast_small (m : ℕ) (hm : m < 2^35) : ((m : ℕ) : F p).val = m :=
  ZMod.val_natCast_of_lt (lt_trans hm Fact.out)

/-! ## Cast-form row value lemmas -/

omit [Fact (p > 2^35)] in
/-- The XOR3 parity expression of three boolean bits *is* the cast of the
bitwise XOR of their values (cast form of `Xor3.parity_val`). -/
lemma parity_cast {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    a + b - 2 * a * b + c - 2 * (a + b - 2 * a * b) * c
      = ((a.val ^^^ b.val ^^^ c.val : ℕ) : F p) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    norm_num [ZMod.val_zero, ZMod.val_one]

omit [Fact (p > 2^35)] in
/-- The 2-input XOR expression of two boolean bits is the cast of the XOR of
their values. -/
lemma xor2_cast {a b : F p} (ha : IsBool a) (hb : IsBool b) :
    a + b - 2 * a * b = ((a.val ^^^ b.val : ℕ) : F p) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    norm_num [ZMod.val_zero, ZMod.val_one]

omit [Fact (p > 2^35)] in
/-- Weight-4 pair row (`λ = 4`, `m = 1`): the determined row value equals
`xor2(a,b) + 4·xor2(c,d)` in cast form. -/
lemma pair_val4 {a b c d : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) (hd : IsBool d) :
    2 * a - 2 * b + 8 * (c + d) - 1
      - (2 * (c + d) - (1 - a + b)) * (2 * (c + d) + (1 - a + b))
      = (((a.val ^^^ b.val) + 4 * (c.val ^^^ d.val) : ℕ) : F p) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> norm_num [ZMod.val_zero, ZMod.val_one]

omit [Fact (p > 2^35)] in
/-- Weight-1 pair row (`λ = 1`, `m = 0`): the determined row value equals
`xor2(a,b) + xor2(c,d)` in cast form. -/
lemma pair_val1 {a b c d : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) (hd : IsBool d) :
    2 * a - 2 * b + 2 * (c + d) - 1
      - ((c + d) - (1 - a + b)) * ((c + d) + (1 - a + b))
      = (((a.val ^^^ b.val) + (c.val ^^^ d.val) : ℕ) : F p) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> norm_num [ZMod.val_zero, ZMod.val_one]

/-! ## `valueBits` as a `Finset.range` sum -/

/-- Total bit-value function of a 32-bit word (0 outside the range). -/
def bitsFn (w : Vector (F p) 32) (j : ℕ) : ℕ :=
  if h : j < 32 then (w[j]'h).val else 0

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma bitsFn_lt {w : Vector (F p) 32} {j : ℕ} (hj : j < 32) : bitsFn w j = (w[j]'hj).val :=
  dif_pos hj

omit [Fact (p > 2^35)] in
lemma bitsFn_le_one {w : Vector (F p) 32} (hw : Normalized w) (j : ℕ) : bitsFn w j ≤ 1 := by
  unfold bitsFn
  split
  · next h =>
    rcases hw ⟨j, h⟩ with h0 | h0 <;>
      simp only [Fin.getElem_fin] at h0 <;> rw [h0] <;>
      simp [ZMod.val_zero, ZMod.val_one]
  · omega

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma valueBits_eq_range (w : Vector (F p) 32) :
    valueBits w = ∑ j ∈ Finset.range 32, bitsFn w j * 2^j := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => bitsFn w j * 2^j) 32]
  unfold valueBits
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bitsFn_lt i.isLt]
  rfl

omit [Fact (p > 2^35)] in
/-- The weighted range sum of a per-lane 3-input XOR of bit values is the XOR of
the three words' values. -/
lemma range_xor3_sum (a b c : Vector (F p) 32)
    (ha : Normalized a) (hb : Normalized b) (hc : Normalized c) :
    ∑ j ∈ Finset.range 32, (bitsFn a j ^^^ bitsFn b j ^^^ bitsFn c j) * 2^j
      = valueBits a ^^^ valueBits b ^^^ valueBits c := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => (bitsFn a j ^^^ bitsFn b j ^^^ bitsFn c j) * 2^j) 32]
  have hval : ∀ (w : Vector (F p) 32),
      valueBits w = ∑ i : Fin 32, bitsFn w i.val * 2^i.val := fun w =>
    Finset.sum_congr rfl fun i _ => by rw [bitsFn_lt i.isLt]; rfl
  rw [hval a, hval b, hval c]
  exact Xor3.bool_finsum_xor3_eq 32 _ _ _
    (fun i => by have := bitsFn_le_one ha i.val; omega)
    (fun i => by have := bitsFn_le_one hb i.val; omega)
    (fun i => by have := bitsFn_le_one hc i.val; omega)

omit [Fact p.Prime] [Fact (p > 2^35)] in
/-- A boolean-weighted range sum over 32 lanes is `< 2^32`. -/
lemma range_sum_bool_lt (f : ℕ → ℕ) (hf : ∀ j, j < 32 → f j ≤ 1) :
    ∑ j ∈ Finset.range 32, f j * 2^j < 2^32 := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => f j * 2^j) 32]
  exact sum_bool_lt_two_pow 32 (fun i => f i.val) (fun i => hf i.val i.isLt)

/-! ## Range-sum splitting and the σ-pair regrouping -/

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma sum_range32_split (g : ℕ → ℕ) :
    ∑ j ∈ Finset.range 32, g j =
      (∑ j ∈ Finset.range 22, g j) + g 22 + g 23 + g 24 + g 25 + g 26 + g 27
        + g 28 + g 29 + g 30 + g 31 := by
  rw [Finset.sum_range_succ g 31, Finset.sum_range_succ g 30, Finset.sum_range_succ g 29,
    Finset.sum_range_succ g 28, Finset.sum_range_succ g 27, Finset.sum_range_succ g 26,
    Finset.sum_range_succ g 25, Finset.sum_range_succ g 24, Finset.sum_range_succ g 23,
    Finset.sum_range_succ g 22]

omit [Fact p.Prime] [Fact (p > 2^35)] in
/-- Regrouping the paired lanes: if the packed column values `m` agree with
`x0 + x1` on the 3-input lanes and carry the pairs (weight 4 within a slot two
lanes lower) on the tail, the weighted sum of `m` splits into the two σ
bit-columns. -/
lemma regroup_sum (m x0 x1 : ℕ → ℕ)
    (hlow : ∀ j, j < 22 → m j = x0 j + x1 j)
    (h22 : m 22 = x0 22 + (x1 22 + 4 * x1 24))
    (h23 : m 23 = x0 23 + (x1 23 + 4 * x1 25))
    (h24 : m 24 = x0 24)
    (h25 : m 25 = x0 25)
    (h26 : m 26 = x0 26 + (x1 26 + 4 * x1 28))
    (h27 : m 27 = x0 27 + (x1 27 + 4 * x1 29))
    (h28 : m 28 = x0 28)
    (h29 : m 29 = x0 29)
    (h30 : m 30 = x1 30 + x0 30)
    (h31 : m 31 = x1 31 + x0 31) :
    ∑ j ∈ Finset.range 32, m j * 2^j
      = (∑ j ∈ Finset.range 32, x0 j * 2^j) + (∑ j ∈ Finset.range 32, x1 j * 2^j) := by
  rw [sum_range32_split (fun j => m j * 2^j), sum_range32_split (fun j => x0 j * 2^j),
    sum_range32_split (fun j => x1 j * 2^j)]
  have hl : ∑ j ∈ Finset.range 22, m j * 2^j
      = ∑ j ∈ Finset.range 22, (x0 j * 2^j + x1 j * 2^j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hlow j (Finset.mem_range.mp hj)]
    ring
  rw [hl, Finset.sum_add_distrib, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31]
  ring

/-! ## The packed column vector `tVec` -/

/-- The 32 packed column entries of the fused adder row: lanes 0–21 add the two
σ witnesses, the tail lanes carry the pair witnesses at their base positions. -/
def tVec (s0 : Var (fields 29) (F p)) (s1 : Var (fields 22) (F p))
    (u : Var (fields 6) (F p)) (v : Expression (F p)) : Var (fields 32) (F p) :=
  (Vector.ofFn fun i : Fin 22 => s0[i.val]'(by omega) + s1[i.val]'(by omega)) ++
  #v[s0[22]'(by norm_num) + u[0]'(by norm_num),
     s0[23]'(by norm_num) + u[1]'(by norm_num),
     s0[24]'(by norm_num),
     s0[25]'(by norm_num),
     s0[26]'(by norm_num) + u[2]'(by norm_num),
     s0[27]'(by norm_num) + u[3]'(by norm_num),
     s0[28]'(by norm_num),
     v,
     u[4]'(by norm_num),
     u[5]'(by norm_num)]

section TVecGet
variable (s0 : Var (fields 29) (F p)) (s1 : Var (fields 22) (F p))
  (u : Var (fields 6) (F p)) (v : Expression (F p))

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_low (j : ℕ) (hj : j < 22) :
    (tVec s0 s1 u v)[j]'(by omega) = s0[j]'(by omega) + s1[j]'hj := by
  unfold tVec
  rw [Vector.getElem_append_left hj, Vector.getElem_ofFn]

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_hi (j : ℕ) (h1 : 22 ≤ j) (h2 : j < 32) :
    (tVec s0 s1 u v)[j]'h2 =
      (#v[s0[22]'(by norm_num) + u[0]'(by norm_num),
          s0[23]'(by norm_num) + u[1]'(by norm_num),
          s0[24]'(by norm_num),
          s0[25]'(by norm_num),
          s0[26]'(by norm_num) + u[2]'(by norm_num),
          s0[27]'(by norm_num) + u[3]'(by norm_num),
          s0[28]'(by norm_num),
          v,
          u[4]'(by norm_num),
          u[5]'(by norm_num)] : Vector (Expression (F p)) 10)[j - 22]'(by omega) := by
  unfold tVec
  exact Vector.getElem_append_right (by omega) h1

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_22 : (tVec s0 s1 u v)[22]'(by norm_num)
    = s0[22]'(by norm_num) + u[0]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 22 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_23 : (tVec s0 s1 u v)[23]'(by norm_num)
    = s0[23]'(by norm_num) + u[1]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 23 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_24 : (tVec s0 s1 u v)[24]'(by norm_num) = s0[24]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 24 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_25 : (tVec s0 s1 u v)[25]'(by norm_num) = s0[25]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 25 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_26 : (tVec s0 s1 u v)[26]'(by norm_num)
    = s0[26]'(by norm_num) + u[2]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 26 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_27 : (tVec s0 s1 u v)[27]'(by norm_num)
    = s0[27]'(by norm_num) + u[3]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 27 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_28 : (tVec s0 s1 u v)[28]'(by norm_num) = s0[28]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 28 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_29 : (tVec s0 s1 u v)[29]'(by norm_num) = v := by
  rw [tVec_get_hi s0 s1 u v 29 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_30 : (tVec s0 s1 u v)[30]'(by norm_num) = u[4]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 30 (by norm_num) (by norm_num)]
  rfl

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma tVec_get_31 : (tVec s0 s1 u v)[31]'(by norm_num) = u[5]'(by norm_num) := by
  rw [tVec_get_hi s0 s1 u v 31 (by norm_num) (by norm_num)]
  rfl

end TVecGet

/-! ## ℕ-level witness generator helpers -/

/-- σ₀ lane value under a prover environment: the 3-input XOR of the
`rotr7`/`rotr18`/`shr3` bits of the word (the `shr3` bit is the constant 0 on
lanes 29–31). -/
def lane0 (env : ProverEnvironment (F p)) (w : Var (fields 32) (F p)) (j : ℕ) : ℕ :=
  if h : j < 32 then
    (Expression.eval env.toEnvironment ((rotr32 7 w)[j]'h)).val
      ^^^ (Expression.eval env.toEnvironment ((rotr32 18 w)[j]'h)).val
      ^^^ (Expression.eval env.toEnvironment ((shr32 3 w)[j]'h)).val
  else 0

/-- σ₁ lane value under a prover environment (`rotr17`/`rotr19`/`shr10`). -/
def lane1 (env : ProverEnvironment (F p)) (w : Var (fields 32) (F p)) (j : ℕ) : ℕ :=
  if h : j < 32 then
    (Expression.eval env.toEnvironment ((rotr32 17 w)[j]'h)).val
      ^^^ (Expression.eval env.toEnvironment ((rotr32 19 w)[j]'h)).val
      ^^^ (Expression.eval env.toEnvironment ((shr32 10 w)[j]'h)).val
  else 0

omit [Fact (p > 2^35)] in
/-- On the shifted-out lanes (`j ≥ 29`) the σ₀ lane value is a 2-input XOR. -/
lemma lane0_hi (env : ProverEnvironment (F p)) (w : Var (fields 32) (F p))
    (j : ℕ) (h1 : 29 ≤ j) (h2 : j < 32) :
    lane0 env w j = (Expression.eval env.toEnvironment ((rotr32 7 w)[j]'h2)).val
      ^^^ (Expression.eval env.toEnvironment ((rotr32 18 w)[j]'h2)).val := by
  unfold lane0
  rw [dif_pos h2]
  have hz : (shr32 3 w)[j]'h2 = 0 := by
    unfold shr32
    rw [Vector.getElem_ofFn]
    exact dif_neg (by show ¬(j + (3 : Fin 32).val < 32); omega)
  rw [hz]
  simp [Expression.eval, ZMod.val_zero]

omit [Fact (p > 2^35)] in
/-- On the shifted-out lanes (`j ≥ 22`) the σ₁ lane value is a 2-input XOR. -/
lemma lane1_hi (env : ProverEnvironment (F p)) (w : Var (fields 32) (F p))
    (j : ℕ) (h1 : 22 ≤ j) (h2 : j < 32) :
    lane1 env w j = (Expression.eval env.toEnvironment ((rotr32 17 w)[j]'h2)).val
      ^^^ (Expression.eval env.toEnvironment ((rotr32 19 w)[j]'h2)).val := by
  unfold lane1
  rw [dif_pos h2]
  have hz : (shr32 10 w)[j]'h2 = 0 := by
    unfold shr32
    rw [Vector.getElem_ofFn]
    exact dif_neg (by show ¬(j + (10 : Fin 32).val < 32); omega)
  rw [hz]
  simp [Expression.eval, ZMod.val_zero]

omit [Fact (p > 2^35)] in
/-- A σ₀ lane value of a normalized word is boolean. -/
lemma lane0_le_one (env : ProverEnvironment (F p)) {w_var : Var (fields 32) (F p)}
    {w : fields 32 (F p)}
    (h_eval : Vector.map (Expression.eval env.toEnvironment) w_var = w)
    (hw : Normalized w) (j : ℕ) : lane0 env w_var j ≤ 1 := by
  unfold lane0
  split
  · next h =>
    have b7 := IsBool.val_of_IsBool (by
      have := (Normalized_eval_rotr32 env.toEnvironment w_var w h_eval hw 7) ⟨j, h⟩
      rwa [Fin.getElem_fin, Vector.getElem_map] at this)
    have b18 := IsBool.val_of_IsBool (by
      have := (Normalized_eval_rotr32 env.toEnvironment w_var w h_eval hw 18) ⟨j, h⟩
      rwa [Fin.getElem_fin, Vector.getElem_map] at this)
    have b3 := IsBool.val_of_IsBool (by
      have := (Normalized_eval_shr32 env.toEnvironment w_var w h_eval hw 3) ⟨j, h⟩
      rwa [Fin.getElem_fin, Vector.getElem_map] at this)
    exact xor_le_one (xor_le_one (isBool_nat_le_one b7) (isBool_nat_le_one b18))
      (isBool_nat_le_one b3)
  · omega

omit [Fact (p > 2^35)] in
/-- A σ₁ lane value of a normalized word is boolean. -/
lemma lane1_le_one (env : ProverEnvironment (F p)) {w_var : Var (fields 32) (F p)}
    {w : fields 32 (F p)}
    (h_eval : Vector.map (Expression.eval env.toEnvironment) w_var = w)
    (hw : Normalized w) (j : ℕ) : lane1 env w_var j ≤ 1 := by
  unfold lane1
  split
  · next h =>
    have b17 := IsBool.val_of_IsBool (by
      have := (Normalized_eval_rotr32 env.toEnvironment w_var w h_eval hw 17) ⟨j, h⟩
      rwa [Fin.getElem_fin, Vector.getElem_map] at this)
    have b19 := IsBool.val_of_IsBool (by
      have := (Normalized_eval_rotr32 env.toEnvironment w_var w h_eval hw 19) ⟨j, h⟩
      rwa [Fin.getElem_fin, Vector.getElem_map] at this)
    have b10 := IsBool.val_of_IsBool (by
      have := (Normalized_eval_shr32 env.toEnvironment w_var w h_eval hw 10) ⟨j, h⟩
      rwa [Fin.getElem_fin, Vector.getElem_map] at this)
    exact xor_le_one (xor_le_one (isBool_nat_le_one b17) (isBool_nat_le_one b19))
      (isBool_nat_le_one b10)
  · omega

/-- The full ℕ sum computed by one schedule step:
`σ₁(wm2) + wm7 + σ₀(wm15) + wm16` under a prover environment. -/
def schedSumNat (env : ProverEnvironment (F p))
    (wm2 wm7 wm15 wm16 : Var (fields 32) (F p)) : ℕ :=
  (∑ j ∈ Finset.range 32, lane1 env wm2 j * 2^j) + evalBitsNat env wm7
    + (∑ j ∈ Finset.range 32, lane0 env wm15 j * 2^j) + evalBitsNat env wm16

end SigmaSum
end Solution.SHA256
end
