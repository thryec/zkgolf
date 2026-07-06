import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesLemmas

/-!
# Lemmas for the byte-split affine limb packing (`Bytes.packLimbsSplit`)

Proof layer connecting the split-based packing of `Bytes.lean` to
`BigInt.Normalized` / `BigInt.value` / `os2ip`, replacing the bit-level
`packLimbs` route. The interface is the `SplitPieces` predicate: for every
straddling boundary `k`, the `lo`/`hi` expressions are bounded by their widths
and recompose the straddled byte. Given `SplitPieces` and byteness of the input
bytes, `packLimbsSplit` is normalized and denotes the base-256 value of the
byte string.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace BytesSplitLemmas

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open BytesLemmas
open Specs.RSASSAPKCS1v15

/-! ## Index arithmetic for the split boundaries -/

theorem splitIdx_splitBoundary (s : ℕ) (hs : s < 29) : splitIdx (splitBoundary s) = s := by
  simp only [splitBoundary, splitIdx]
  omega

theorem splitBoundary_splitIdx (k : ℕ) (h1 : 1 ≤ k) (h2 : k < 34) (h3 : 121 * k % 8 ≠ 0) :
    splitBoundary (splitIdx k) = k := by
  simp only [splitBoundary, splitIdx]
  interval_cases k <;> omega

theorem splitIdx_lt (k : ℕ) (h2 : k < 34) : splitIdx k < 29 := by
  simp only [splitIdx]
  omega

theorem splitBoundary_lt (s : ℕ) (hs : s < 29) : splitBoundary s < 34 := by
  simp only [splitBoundary]
  omega

theorem splitBoundary_straddles (s : ℕ) (hs : s < 29) : 121 * splitBoundary s % 8 ≠ 0 := by
  simp only [splitBoundary]
  omega

/-! ## `eval` distributes over `+` / `*` (definitional). -/

theorem eval_add' (env : Environment (F circomPrime)) (a b : Expression (F circomPrime)) :
    Expression.eval env (a + b) = Expression.eval env a + Expression.eval env b := rfl

theorem eval_mul' (env : Environment (F circomPrime)) (a b : Expression (F circomPrime)) :
    Expression.eval env (a * b) = Expression.eval env a * Expression.eval env b := rfl

theorem eval_const' (env : Environment (F circomPrime)) (c : F circomPrime) :
    Expression.eval env (Expression.const c) = c := rfl

/-- `Expression.eval` distributes over subtraction (without unfolding either
operand). -/
theorem eval_sub' (env : Environment (F circomPrime)) (a b : Expression (F circomPrime)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b := by
  show Expression.eval env (Expression.add a (Expression.mul (Expression.const (-1)) b))
      = Expression.eval env a - Expression.eval env b
  rw [eval_add, eval_mul]
  show Expression.eval env a + (-1) * Expression.eval env b = _
  ring

/-! ## Totalized bit / byte values -/

/-- The (totalized) value of witnessed bit `j`. -/
def bitVal {nb : ℕ} (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) nb) (j : ℕ) : ℕ :=
  if h : j < nb then (Expression.eval env (bits[j]'h)).val else 0

/-- The value of the little-endian byte `je` (i.e. big-endian byte `511 − je`). -/
def byteVal (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512) (je : ℕ) : ℕ :=
  (Expression.eval env (bytes[511 - je]'(by omega))).val

/-! ## Truncation / shift helpers for guarded `range` sums -/

theorem sum_range_guard_lt {t n : ℕ} (h : t ≤ n) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, if i < t then f i else 0) = ∑ i ∈ Finset.range t, f i := by
  rw [← Finset.sum_subset
    (show Finset.range t ⊆ Finset.range n from by
      intro x hx; rw [Finset.mem_range] at *; omega)
    (fun x _ hx => by rw [if_neg (by simpa using hx)])]
  apply Finset.sum_congr rfl
  intro i hi
  rw [if_pos (Finset.mem_range.mp hi)]

theorem sum_range_guard_ge {t n : ℕ} (h : t ≤ n) (g : ℕ → ℕ) :
    (∑ i ∈ Finset.range n, if t ≤ i then g i else 0) = ∑ j ∈ Finset.range (n - t), g (t + j) := by
  have hrange : Finset.range n = Finset.Ico 0 n := by rw [Finset.range_eq_Ico]
  rw [hrange, ← Finset.sum_Ico_consecutive _ (Nat.zero_le t) h]
  have hleft : (∑ i ∈ Finset.Ico 0 t, if t ≤ i then g i else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := (Finset.mem_Ico.mp hi).2; omega)]
  have hright : (∑ i ∈ Finset.Ico t n, if t ≤ i then g i else 0)
      = ∑ i ∈ Finset.Ico t n, g i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_Ico.mp hi).1]
  rw [hleft, hright, Nat.zero_add, Finset.sum_Ico_eq_sum_range]

/-- `sum_lt_pow` over `Finset.range`. -/
theorem sum_range_lt_pow {B n : ℕ} (f : ℕ → ℕ) (hf : ∀ i, i < n → f i < 2 ^ B) :
    ∑ i ∈ Finset.range n, f i * 2 ^ (B * i) < 2 ^ (B * n) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => f i * 2 ^ (B * i)) n]
  exact sum_lt_pow (fun i : Fin n => f i.val) (fun i => hf i.val i.isLt)

/-- Base-2 version of `sum_range_lt_pow`. -/
theorem sum_range_lt_pow_one {n : ℕ} (f : ℕ → ℕ) (hf : ∀ i, i < n → f i < 2) :
    ∑ i ∈ Finset.range n, f i * 2 ^ i < 2 ^ n := by
  have := sum_range_lt_pow (B := 1) (n := n) f (fun i hi => by simpa using hf i hi)
  simpa using this

/-! ## Evaluation of the split expressions -/

/-- `eval` of `splitLowSum` is the nat bit-sum, as a field cast. -/
theorem eval_splitLowSum {nb : ℕ} (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) nb) (s : ℕ) :
    Expression.eval env (splitLowSum bits s)
      = ((∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i : ℕ) : F circomPrime) := by
  unfold splitLowSum
  rw [eval_foldl_add, ← Fin.sum_univ_eq_sum_range
    (fun i => bitVal env bits (7 * s + i) * 2 ^ i) 7, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold bitVal
  by_cases h : 7 * s + i.val < nb
  · rw [dif_pos h, dif_pos h]
    simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [ZMod.natCast_zmod_val]
  · rw [dif_neg h, dif_neg h]
    simp [Expression.eval]

/-- `eval` of `splitLoExpr` at boundary `k = splitBoundary s`. -/
theorem eval_splitLoExpr {nb : ℕ} (env : Environment (F circomPrime))
    (bits : Vector (Expression (F circomPrime)) nb) (k : ℕ) :
    Expression.eval env (splitLoExpr bits k)
      = ((∑ i ∈ Finset.range 7,
            if i < 121 * k % 8 then bitVal env bits (7 * splitIdx k + i) * 2 ^ i else 0 :
            ℕ) : F circomPrime) := by
  unfold splitLoExpr
  rw [eval_foldl_add, ← Fin.sum_univ_eq_sum_range
    (fun i => if i < 121 * k % 8 then bitVal env bits (7 * splitIdx k + i) * 2 ^ i else 0) 7,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hlt : i.val < 121 * k % 8
  · by_cases h : 7 * splitIdx k + i.val < nb
    · rw [dif_pos ⟨hlt, h⟩, if_pos hlt]
      unfold bitVal
      rw [dif_pos h]
      simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [ZMod.natCast_zmod_val]
    · rw [dif_neg (by tauto), if_pos hlt]
      unfold bitVal
      rw [dif_neg h]
      simp [Expression.eval]
  · rw [dif_neg (by tauto), if_neg hlt]
    simp [Expression.eval]

/-- `eval` of the guarded high-bit fold inside `splitHiExpr`. -/
theorem eval_splitHiExpr {nb : ℕ} (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb) (k : ℕ) :
    Expression.eval env (splitHiExpr bytes bits k)
      = ((∑ i ∈ Finset.range 7,
            if 121 * k % 8 ≤ i then bitVal env bits (7 * splitIdx k + i) * 2 ^ (i - 121 * k % 8)
            else 0 : ℕ) : F circomPrime)
        + Expression.eval env (splitTop bytes bits (splitIdx k))
            * ((2 ^ (7 - 121 * k % 8) : ℕ) : F circomPrime) := by
  unfold splitHiExpr
  rw [eval_add', eval_mul', eval_const']
  congr 1
  · rw [eval_foldl_add, ← Fin.sum_univ_eq_sum_range
      (fun i => if 121 * k % 8 ≤ i then bitVal env bits (7 * splitIdx k + i) * 2 ^ (i - 121 * k % 8) else 0) 7,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hge : 121 * k % 8 ≤ i.val
    · by_cases h : 7 * splitIdx k + i.val < nb
      · rw [dif_pos ⟨hge, h⟩, if_pos hge]
        unfold bitVal
        rw [dif_pos h]
        simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [ZMod.natCast_zmod_val]
      · rw [dif_neg (by tauto), if_pos hge]
        unfold bitVal
        rw [dif_neg h]
        simp [Expression.eval]
    · rw [dif_neg (by tauto), if_neg hge]
      simp [Expression.eval]

/-! ## Soundness of one byte split -/

/-- `.val` of a nat-cast below `circomPrime` is the nat itself. -/
theorem val_natCast_lt' {n : ℕ} (h : n < circomPrime) : ((n : F circomPrime)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem two_pow_7_lt_circomPrime : (2 : ℕ) ^ 7 < circomPrime :=
  lt_trans (by norm_num) two_pow_256_lt_circomPrime

theorem pow7_ne_zero : (((2 ^ 7 : ℕ) : F circomPrime)) ≠ 0 := by
  intro h
  have hval : (((2 ^ 7 : ℕ) : F circomPrime)).val = 2 ^ 7 :=
    val_natCast_lt' two_pow_7_lt_circomPrime
  rw [h, ZMod.val_zero] at hval
  norm_num at hval

/-- `eval` of `splitTop` in terms of the byte and low-bit-sum values. -/
theorem eval_splitTop {nb : ℕ} (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb) (s : ℕ) :
    Expression.eval env (splitTop bytes bits s)
      = (((2 ^ 7 : ℕ) : F circomPrime))⁻¹
          * (((byteVal env bytes (splitByteLE (splitBoundary s)) : ℕ) : F circomPrime)
            - ((∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i : ℕ) : F circomPrime)) := by
  unfold splitTop
  rw [eval_mul', eval_const', eval_sub', eval_splitLowSum]
  congr 2
  unfold byteVal
  rw [ZMod.natCast_zmod_val]

/-- Pure-arithmetic core of one byte split: bounds and recomposition of the
`lo`/`hi` piece values from boolean bits `b` and top bit `tv`, at split point
`t ∈ [1,7]`. -/
theorem split_core (t : ℕ) (ht1 : 1 ≤ t) (ht7 : t ≤ 7) (b : ℕ → ℕ)
    (hb : ∀ i, i < 7 → b i < 2) (tv : ℕ) (htv : tv < 2) :
    (∑ i ∈ Finset.range t, b i * 2 ^ i) < 2 ^ t ∧
    ((∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ j) + tv * 2 ^ (7 - t)) < 2 ^ (8 - t) ∧
    (∑ i ∈ Finset.range t, b i * 2 ^ i)
      + ((∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ j) + tv * 2 ^ (7 - t)) * 2 ^ t
      = (∑ i ∈ Finset.range 7, b i * 2 ^ i) + tv * 2 ^ 7 := by
  have hS1 : (∑ i ∈ Finset.range t, b i * 2 ^ i) < 2 ^ t :=
    sum_range_lt_pow_one b (fun i hi => hb i (by omega))
  have hS2 : (∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ j) < 2 ^ (7 - t) :=
    sum_range_lt_pow_one (fun j => b (t + j)) (fun j hj => hb (t + j) (by omega))
  have hHi : ((∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ j) + tv * 2 ^ (7 - t))
      < 2 ^ (8 - t) := by
    have h8t : 8 - t = (7 - t) + 1 := by omega
    rw [h8t, pow_succ]
    rcases (show tv = 0 ∨ tv = 1 from by omega) with h | h <;> subst h <;> omega
  refine ⟨hS1, hHi, ?_⟩
  -- split the full 7-bit sum at `t`
  have h7 : (7 : ℕ) = t + (7 - t) := by omega
  have hsplit : (∑ i ∈ Finset.range 7, b i * 2 ^ i)
      = (∑ i ∈ Finset.range t, b i * 2 ^ i)
        + ∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ (t + j) := by
    rw [show Finset.range 7 = Finset.range (t + (7 - t)) from by rw [← h7],
      Finset.sum_range_add]
  have hshift : (∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ (t + j))
      = (∑ j ∈ Finset.range (7 - t), b (t + j) * 2 ^ j) * 2 ^ t := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have hpow7 : 2 ^ (7 - t) * 2 ^ t = 2 ^ 7 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit, hshift, Nat.add_mul, mul_assoc, hpow7]
  ring

/-- **Soundness of one split.** Given booleanity of split `s`'s seven witnessed
bits and of its implicit top bit, the `lo`/`hi` pieces at boundary
`k = splitBoundary s` are bounded by their widths and recompose the straddled
byte. (This also re-derives `byte < 256`, but byteness is anyway trusted.) -/
theorem split_sound {nb : ℕ} (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb)
    (s : ℕ) (hs : s < 29)
    (hbool : ∀ (i : ℕ), i < 7 → bitVal env bits (7 * s + i) < 2)
    (htop : Expression.eval env (splitTop bytes bits s)
        * (Expression.eval env (splitTop bytes bits s) - 1) = 0) :
    (Expression.eval env (splitLoExpr bits (splitBoundary s))).val
        < 2 ^ (121 * splitBoundary s % 8) ∧
    (Expression.eval env (splitHiExpr bytes bits (splitBoundary s))).val
        < 2 ^ (8 - 121 * splitBoundary s % 8) ∧
    byteVal env bytes (splitByteLE (splitBoundary s))
      = (Expression.eval env (splitLoExpr bits (splitBoundary s))).val
        + (Expression.eval env (splitHiExpr bytes bits (splitBoundary s))).val
            * 2 ^ (121 * splitBoundary s % 8) := by
  have hidx : splitIdx (splitBoundary s) = s := splitIdx_splitBoundary s hs
  have ht1 : 1 ≤ 121 * splitBoundary s % 8 := by
    have := splitBoundary_straddles s hs
    omega
  have ht7 : 121 * splitBoundary s % 8 ≤ 7 := by omega
  -- the top bit is boolean: `top = tv` for some `tv < 2`
  obtain ⟨tv, htv2, htveq⟩ : ∃ tv : ℕ, tv < 2 ∧
      Expression.eval env (splitTop bytes bits s) = ((tv : ℕ) : F circomPrime) := by
    rcases mul_eq_zero.mp htop with h | h
    · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
    · refine ⟨1, by norm_num, ?_⟩
      rw [show Expression.eval env (splitTop bytes bits s) = 1 from by linear_combination h]
      norm_num
  -- the low 7-bit sum
  have hp7 : (2 : ℕ) ^ 7 = 128 := by norm_num
  have hLlt : (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i) < 2 ^ 7 :=
    sum_range_lt_pow_one _ (fun i hi => hbool i hi)
  -- field-level recomposition of the straddled byte from `L` and the top bit
  have hyL : ((byteVal env bytes (splitByteLE (splitBoundary s)) : ℕ) : F circomPrime)
      = (((∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i)
          + tv * 2 ^ 7 : ℕ) : F circomPrime) := by
    have hstep : Expression.eval env (splitTop bytes bits s) * ((2 ^ 7 : ℕ) : F circomPrime)
        = ((byteVal env bytes (splitByteLE (splitBoundary s)) : ℕ) : F circomPrime)
          - ((∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i : ℕ) : F circomPrime) := by
      rw [eval_splitTop, mul_right_comm, inv_mul_cancel₀ pow7_ne_zero, one_mul]
    rw [htveq] at hstep
    push_cast at hstep ⊢
    linear_combination -hstep
  -- nat-level byte recomposition
  have hyval : byteVal env bytes (splitByteLE (splitBoundary s))
      = (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i) + tv * 2 ^ 7 := by
    have h1 : (((byteVal env bytes (splitByteLE (splitBoundary s)) : ℕ) : F circomPrime)).val
        = byteVal env bytes (splitByteLE (splitBoundary s)) :=
      val_natCast_lt' (ZMod.val_lt _)
    have h2 : ((((∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i)
          + tv * 2 ^ 7 : ℕ) : F circomPrime)).val
        = (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i) + tv * 2 ^ 7 :=
      val_natCast_lt' (lt_trans (show _ < 256 from by
        have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
        rcases (show tv = 0 ∨ tv = 1 from by omega) with h | h <;> subst h <;> omega)
        two_pow_256_lt_circomPrime)
    rw [← h1, hyL, h2]
  -- core arithmetic facts
  obtain ⟨hcore1, hcore2, hcore3⟩ :=
    split_core (121 * splitBoundary s % 8) ht1 ht7
      (fun i => bitVal env bits (7 * s + i)) (fun i hi => hbool i hi) tv htv2
  -- evaluate the `lo` piece
  have hloE : Expression.eval env (splitLoExpr bits (splitBoundary s))
      = ((∑ i ∈ Finset.range (121 * splitBoundary s % 8),
            bitVal env bits (7 * s + i) * 2 ^ i : ℕ) : F circomPrime) := by
    rw [eval_splitLoExpr, hidx]
    congr 1
    exact sum_range_guard_lt ht7 (fun i => bitVal env bits (7 * s + i) * 2 ^ i)
  have hloV : (Expression.eval env (splitLoExpr bits (splitBoundary s))).val
      = ∑ i ∈ Finset.range (121 * splitBoundary s % 8),
          bitVal env bits (7 * s + i) * 2 ^ i := by
    rw [hloE]
    have hb : (2 : ℕ) ^ (121 * splitBoundary s % 8) ≤ 256 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : 121 * splitBoundary s % 8 ≤ 8))
        (by norm_num)
    exact val_natCast_lt' (lt_of_lt_of_le hcore1
      (le_trans hb (le_of_lt two_pow_256_lt_circomPrime)))
  -- evaluate the `hi` piece
  have hhiE : Expression.eval env (splitHiExpr bytes bits (splitBoundary s))
      = (((∑ j ∈ Finset.range (7 - 121 * splitBoundary s % 8),
            bitVal env bits (7 * s + (121 * splitBoundary s % 8 + j)) * 2 ^ j)
          + tv * 2 ^ (7 - 121 * splitBoundary s % 8) : ℕ) : F circomPrime) := by
    rw [eval_splitHiExpr, hidx, htveq]
    have hguard : (∑ i ∈ Finset.range 7,
          if 121 * splitBoundary s % 8 ≤ i then
            bitVal env bits (7 * s + i) * 2 ^ (i - 121 * splitBoundary s % 8)
          else 0)
        = ∑ j ∈ Finset.range (7 - 121 * splitBoundary s % 8),
            bitVal env bits (7 * s + (121 * splitBoundary s % 8 + j)) * 2 ^ j := by
      rw [sum_range_guard_ge ht7
        (fun i => bitVal env bits (7 * s + i) * 2 ^ (i - 121 * splitBoundary s % 8))]
      apply Finset.sum_congr rfl
      intro j _
      rw [show 121 * splitBoundary s % 8 + j - 121 * splitBoundary s % 8 = j from by omega]
    rw [hguard]
    push_cast
    ring
  have hhiV : (Expression.eval env (splitHiExpr bytes bits (splitBoundary s))).val
      = (∑ j ∈ Finset.range (7 - 121 * splitBoundary s % 8),
            bitVal env bits (7 * s + (121 * splitBoundary s % 8 + j)) * 2 ^ j)
          + tv * 2 ^ (7 - 121 * splitBoundary s % 8) := by
    rw [hhiE]
    have hb : (2 : ℕ) ^ (8 - 121 * splitBoundary s % 8) ≤ 256 :=
      le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : 8 - 121 * splitBoundary s % 8 ≤ 8))
        (by norm_num)
    exact val_natCast_lt' (lt_of_lt_of_le hcore2
      (le_trans hb (le_of_lt two_pow_256_lt_circomPrime)))
  refine ⟨?_, ?_, ?_⟩
  · rw [hloV]; exact hcore1
  · rw [hhiV]; exact hcore2
  · rw [hloV, hhiV, hyval, hcore3]

/-! ## The `SplitPieces` interface and the `packLimbsSplit` theorems -/

/-- Interface between a packing's `lo`/`hi` split expressions and the byte
vector: at every straddling boundary `k < 34`, the pieces are width-bounded and
recompose the straddled byte. -/
def SplitPieces (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime)) : Prop :=
  ∀ k : ℕ, k < 34 → 121 * k % 8 ≠ 0 →
    (Expression.eval env (splitLo k)).val < 2 ^ (121 * k % 8) ∧
    (Expression.eval env (splitHi k)).val < 2 ^ (8 - 121 * k % 8) ∧
    byteVal env bytes (splitByteLE k)
      = (Expression.eval env (splitLo k)).val
        + (Expression.eval env (splitHi k)).val * 2 ^ (121 * k % 8)

/-- Nat model of limb `k`'s `hi` piece. -/
def hiT (env : Environment (F circomPrime))
    (splitHi : ℕ → Expression (F circomPrime)) (k : ℕ) : ℕ :=
  if 121 * k % 8 ≠ 0 then (Expression.eval env (splitHi k)).val else 0

/-- Nat model of limb `k`'s whole-byte terms. -/
def midT (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512) (k : ℕ) : ℕ :=
  ∑ d ∈ Finset.range 16,
    if 8 * (startByte k + d) + 8 ≤ min (121 * (k + 1)) 4096 then
      byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
    else 0

/-- Nat model of limb `k`'s `lo` piece (of boundary `k+1`). -/
def loT (env : Environment (F circomPrime))
    (splitLo : ℕ → Expression (F circomPrime)) (k : ℕ) : ℕ :=
  if 121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < 34 then
    (Expression.eval env (splitLo (k + 1))).val * 2 ^ (121 - 121 * (k + 1) % 8)
  else 0

/-- The number of whole-byte terms of limb `k`. -/
@[reducible] def midCnt (k : ℕ) : ℕ := min (121 * (k + 1)) 4096 / 8 - startByte k

/-- The whole-byte guard of limb `k` selects exactly the first `midCnt k`
positions. -/
theorem mid_guard_iff (k d : ℕ) :
    (8 * (startByte k + d) + 8 ≤ min (121 * (k + 1)) 4096) ↔ d < midCnt k := by
  simp only [startByte, midCnt]
  omega

theorem midCnt_le_16 (k : ℕ) : midCnt k ≤ 16 := by
  simp only [startByte, midCnt]
  omega

theorem mid_exp_split (k d : ℕ) (hd : d < midCnt k) :
    8 * (startByte k + d) - 121 * k = 8 * d + (8 * startByte k - 121 * k) := by
  simp only [midCnt, startByte] at hd ⊢
  omega

theorem mid_byte_lt (k d : ℕ) (hd : d < midCnt k) : startByte k + d < 512 := by
  simp only [midCnt, startByte] at hd ⊢
  omega

theorem straddle_ofs0 (k : ℕ) (h : 121 * k % 8 ≠ 0) :
    8 * startByte k - 121 * k = 8 - 121 * k % 8 := by
  simp only [startByte]
  omega

theorem exp_straddle (k : ℕ) (h : 121 * (k + 1) % 8 ≠ 0) (hk : k + 1 < 34) :
    8 * startByte k - 121 * k + 8 * midCnt k = 121 - 121 * (k + 1) % 8 := by
  simp only [startByte, midCnt]
  omega

theorem exp_aligned (k : ℕ) (hk : k < 34) :
    8 * startByte k - 121 * k + 8 * midCnt k ≤ 121 := by
  simp only [startByte, midCnt]
  omega

theorem tmod_le_121 (k : ℕ) : 121 - 121 * (k + 1) % 8 ≤ 121 := by omega

theorem ofs0_le_7 (k : ℕ) : 8 * startByte k - 121 * k ≤ 7 := by
  simp only [startByte]
  omega

theorem pow_sub_mul_pow (t : ℕ) (ht : t ≤ 121) :
    (2 ^ t - 1) * 2 ^ (121 - t) = 2 ^ 121 - 2 ^ (121 - t) := by
  rw [Nat.sub_mul, one_mul, ← pow_add, show t + (121 - t) = 121 from by omega]

/-- The pieces of limb `k` sum to `< 2^121`. -/
theorem limb_pieces_lt (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (hsplit : SplitPieces env bytes splitLo splitHi)
    (k : ℕ) (hk : k < 34) :
    hiT env splitHi k + midT env bytes k + loT env splitLo k < 2 ^ 121 := by
  -- the mid sum, truncated and factored
  have hguard : midT env bytes k
      = ∑ d ∈ Finset.range (midCnt k),
          byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k) := by
    unfold midT
    rw [show (∑ d ∈ Finset.range 16,
          if 8 * (startByte k + d) + 8 ≤ min (121 * (k + 1)) 4096 then
            byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
          else 0)
        = ∑ d ∈ Finset.range 16,
          if d < midCnt k then
            byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
          else 0 from
      Finset.sum_congr rfl (fun d _ => by rw [if_congr (mid_guard_iff k d) rfl rfl])]
    exact sum_range_guard_lt (midCnt_le_16 k) _
  have hmid : midT env bytes k
      ≤ 2 ^ (8 * startByte k - 121 * k) * (2 ^ (8 * midCnt k) - 1) := by
    rw [hguard]
    have hterm : ∀ d ∈ Finset.range (midCnt k),
        byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
          = byteVal env bytes (startByte k + d) * 2 ^ (8 * d)
              * 2 ^ (8 * startByte k - 121 * k) := by
      intro d hd
      rw [mid_exp_split k d (Finset.mem_range.mp hd), pow_add, ← mul_assoc]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, mul_comm]
    have hsum : (∑ d ∈ Finset.range (midCnt k),
          byteVal env bytes (startByte k + d) * 2 ^ (8 * d)) < 2 ^ (8 * midCnt k) := by
      apply sum_range_lt_pow (B := 8)
      intro d hd
      exact hbytes (startByte k + d) (mid_byte_lt k d hd)
    have hpos : 0 < (2 : ℕ) ^ (8 * startByte k - 121 * k) := Nat.two_pow_pos _
    exact Nat.mul_le_mul_left _ (by omega)
  -- the hi piece is `< 2^(8·sb − 121·k)`
  have hhi : hiT env splitHi k < 2 ^ (8 * startByte k - 121 * k) := by
    unfold hiT
    by_cases hstr : 121 * k % 8 ≠ 0
    · rw [if_pos hstr, straddle_ofs0 k hstr]
      exact (hsplit k hk hstr).2.1
    · rw [if_neg hstr]
      exact Nat.two_pow_pos _
  -- powers bookkeeping: eliminate the product form
  have hA1 : 1 ≤ (2 : ℕ) ^ (8 * startByte k - 121 * k) := Nat.one_le_two_pow
  replace hmid : midT env bytes k
      ≤ 2 ^ (8 * startByte k - 121 * k + 8 * midCnt k)
        - 2 ^ (8 * startByte k - 121 * k) :=
    hmid.trans (le_of_eq (by rw [Nat.mul_sub, mul_one, pow_add]))
  by_cases hlo : 121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < 34
  · -- straddling next boundary: `ofs0 + 8·mcnt = 121 − t'`
    rw [exp_straddle k hlo.1 hlo.2] at hmid
    have hloB : loT env splitLo k
        ≤ 2 ^ 121 - 2 ^ (121 - 121 * (k + 1) % 8) := by
      unfold loT
      rw [if_pos hlo]
      have h := (hsplit (k + 1) hlo.2 hlo.1).1
      have hmul := pow_sub_mul_pow (121 * (k + 1) % 8) (by omega)
      calc (Expression.eval env (splitLo (k + 1))).val * 2 ^ (121 - 121 * (k + 1) % 8)
          ≤ (2 ^ (121 * (k + 1) % 8) - 1) * 2 ^ (121 - 121 * (k + 1) % 8) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 2 ^ 121 - 2 ^ (121 - 121 * (k + 1) % 8) := hmul
    have hle121 : (2 : ℕ) ^ (121 - 121 * (k + 1) % 8) ≤ 2 ^ 121 :=
      Nat.pow_le_pow_right (by norm_num) (tmod_le_121 k)
    have hofs_le : (2 : ℕ) ^ (8 * startByte k - 121 * k) ≤ 2 ^ (121 - 121 * (k + 1) % 8) :=
      Nat.pow_le_pow_right (by norm_num) (by have := ofs0_le_7 k; omega)
    omega
  · -- aligned next boundary (or top limb): `ofs0 + 8·mcnt ≤ 121`, no `lo`
    have hloZ : loT env splitLo k = 0 := by
      unfold loT
      rw [if_neg hlo]
    have hle : (2 : ℕ) ^ (8 * startByte k - 121 * k + 8 * midCnt k) ≤ 2 ^ 121 :=
      Nat.pow_le_pow_right (by norm_num) (exp_aligned k hk)
    have hofs_le : (2 : ℕ) ^ (8 * startByte k - 121 * k)
        ≤ 2 ^ (8 * startByte k - 121 * k + 8 * midCnt k) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
    have h121 : (1 : ℕ) ≤ 2 ^ 121 := Nat.one_le_two_pow
    omega

/-- Per-limb evaluation of `packLimbsSplit`: limb `k` denotes the sum of its
nat-model pieces. -/
theorem packLimbsSplit_limb_eval (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (hsplit : SplitPieces env bytes splitLo splitHi)
    (k : ℕ) (hk : k < 34) :
    (Expression.eval env ((packLimbsSplit bytes splitLo splitHi)[k]'hk)).val
      = hiT env splitHi k + midT env bytes k + loT env splitLo k := by
  unfold packLimbsSplit
  rw [Vector.getElem_ofFn]
  rw [eval_add', eval_add']
  -- hi piece
  have hHi : Expression.eval env
        (if 121 * (⟨k, hk⟩ : Fin numLimbs).val % 8 ≠ 0 then splitHi (⟨k, hk⟩ : Fin numLimbs).val else 0)
      = ((hiT env splitHi k : ℕ) : F circomPrime) := by
    show Expression.eval env (if 121 * k % 8 ≠ 0 then splitHi k else 0) = _
    unfold hiT
    by_cases h : 121 * k % 8 ≠ 0
    · rw [if_pos h, if_pos h, ZMod.natCast_zmod_val]
    · rw [if_neg h, if_neg h]
      norm_num
      rfl
  -- mid fold
  have hMid : Expression.eval env
        (Fin.foldl 16 (fun acc d =>
          acc + (if 8 * (startByte (⟨k, hk⟩ : Fin numLimbs).val + d.val) + 8
                    ≤ min (121 * ((⟨k, hk⟩ : Fin numLimbs).val + 1)) 4096 then
              bytes[511 - (startByte (⟨k, hk⟩ : Fin numLimbs).val + d.val)]'(by omega)
                * (((2 ^ (8 * (startByte (⟨k, hk⟩ : Fin numLimbs).val + d.val)
                      - 121 * (⟨k, hk⟩ : Fin numLimbs).val) : ℕ) : F circomPrime) :
                    Expression (F circomPrime))
            else 0)) 0)
      = ((midT env bytes k : ℕ) : F circomPrime) := by
    rw [eval_foldl_add]
    unfold midT
    rw [← Fin.sum_univ_eq_sum_range (fun d =>
      if 8 * (startByte k + d) + 8 ≤ min (121 * (k + 1)) 4096 then
        byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
      else 0) 16, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : 8 * (startByte k + d.val) + 8 ≤ min (121 * (k + 1)) 4096
    · rw [if_pos h, if_pos h]
      unfold byteVal
      simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [ZMod.natCast_zmod_val]
    · rw [if_neg h, if_neg h]
      simp [Expression.eval]
  -- lo piece
  have hLo : Expression.eval env
        (if 121 * ((⟨k, hk⟩ : Fin numLimbs).val + 1) % 8 ≠ 0
            ∧ (⟨k, hk⟩ : Fin numLimbs).val + 1 < numLimbs then
          splitLo ((⟨k, hk⟩ : Fin numLimbs).val + 1)
            * (((2 ^ (121 - 121 * ((⟨k, hk⟩ : Fin numLimbs).val + 1) % 8) : ℕ) : F circomPrime) :
                Expression (F circomPrime))
        else 0)
      = ((loT env splitLo k : ℕ) : F circomPrime) := by
    show Expression.eval env
        (if 121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < numLimbs then
          splitLo (k + 1)
            * (((2 ^ (121 - 121 * (k + 1) % 8) : ℕ) : F circomPrime) : Expression (F circomPrime))
        else 0) = _
    unfold loT
    by_cases h : 121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < 34
    · rw [if_pos h, if_pos h, eval_mul', eval_const']
      push_cast
      rw [ZMod.natCast_zmod_val]
    · rw [if_neg h, if_neg h]
      norm_num
      rfl
  rw [hHi, hMid, hLo, ← Nat.cast_add, ← Nat.cast_add]
  exact val_natCast_lt' (lt_trans
    (limb_pieces_lt env bytes splitLo splitHi hbytes hsplit k hk)
    two_pow_121_lt_circomPrime)

/-- `packLimbsSplit` is `Normalized` at limb width `121`. -/
theorem packLimbsSplit_normalized (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (hsplit : SplitPieces env bytes splitLo splitHi) :
    BigInt.Normalized limbBits
      (Vector.map (Expression.eval env) (packLimbsSplit bytes splitLo splitHi)) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_map,
    packLimbsSplit_limb_eval env bytes splitLo splitHi hbytes hsplit i.val i.isLt]
  exact limb_pieces_lt env bytes splitLo splitHi hbytes hsplit i.val i.isLt

/-! ## Global value: `packLimbsSplit` denotes the base-256 byte value -/

/-- The `hi` piece of boundary `k+1`, at its global weight `2^(121·(k+1))`. -/
def hiNext (env : Environment (F circomPrime))
    (splitHi : ℕ → Expression (F circomPrime)) (k : ℕ) : ℕ :=
  if 121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < 34 then
    (Expression.eval env (splitHi (k + 1))).val * 2 ^ (121 * (k + 1))
  else 0

/-- `midT` as an untruncated `range` sum. -/
theorem midT_eq_range (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512) (k : ℕ) :
    midT env bytes k
      = ∑ d ∈ Finset.range (midCnt k),
          byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k) := by
  unfold midT
  rw [show (∑ d ∈ Finset.range 16,
        if 8 * (startByte k + d) + 8 ≤ min (121 * (k + 1)) 4096 then
          byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
        else 0)
      = ∑ d ∈ Finset.range 16,
        if d < midCnt k then
          byteVal env bytes (startByte k + d) * 2 ^ (8 * (startByte k + d) - 121 * k)
        else 0 from
    Finset.sum_congr rfl (fun d _ => by rw [if_congr (mid_guard_iff k d) rfl rfl])]
  exact sum_range_guard_lt (midCnt_le_16 k) _

theorem mid_exp_total (k d : ℕ) (hd : d < midCnt k) :
    8 * (startByte k + d) - 121 * k + 121 * k = 8 * (startByte k + d) := by
  simp only [midCnt, startByte] at hd ⊢
  omega

/-- The whole-byte window of limb `k` sums to `midT k · 2^(121·k)`. -/
theorem mid_window_eq (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512) (k : ℕ) :
    (∑ je ∈ Finset.Ico (startByte k) (startByte k + midCnt k),
        byteVal env bytes je * 2 ^ (8 * je))
      = midT env bytes k * 2 ^ (121 * k) := by
  rw [Finset.sum_Ico_eq_sum_range, add_tsub_cancel_left, midT_eq_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc, ← pow_add, mid_exp_total k d (Finset.mem_range.mp hd)]

/-! ### Window endpoint arithmetic -/

theorem winLo_straddle (k : ℕ) (hk : k < 34) : min (startByte k) 512 = startByte k := by
  simp only [startByte]
  omega

theorem winHi_straddle (k : ℕ) (h : 121 * (k + 1) % 8 ≠ 0) (hk : k + 1 < 34) :
    min (startByte (k + 1)) 512 = startByte k + midCnt k + 1 := by
  simp only [startByte, midCnt]
  rw [Nat.min_eq_left (by omega : 121 * (k + 1) ≤ 4096)]
  omega

theorem winHi_aligned (k : ℕ) (hk : k < 34) (h : ¬(121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < 34)) :
    min (startByte (k + 1)) 512 = startByte k + midCnt k := by
  simp only [startByte, midCnt]
  rcases Nat.lt_or_ge k 33 with hlt | hge
  · rw [Nat.min_eq_left (by omega : 121 * (k + 1) ≤ 4096)]
    omega
  · have hk33 : k = 33 := by omega
    subst hk33
    omega

theorem splitByteLE_next (k : ℕ) (h : 121 * (k + 1) % 8 ≠ 0) (hk : k + 1 < 34) :
    splitByteLE (k + 1) = startByte k + midCnt k := by
  simp only [splitByteLE, startByte, midCnt]
  omega

theorem win_exp1 (k : ℕ) (h : 121 * (k + 1) % 8 ≠ 0) (hk : k + 1 < 34) :
    8 * (startByte k + midCnt k) = 121 - 121 * (k + 1) % 8 + 121 * k := by
  simp only [startByte, midCnt]
  omega

theorem win_exp2 (k : ℕ) (h : 121 * (k + 1) % 8 ≠ 0) (hk : k + 1 < 34) :
    121 * (k + 1) % 8 + 8 * (startByte k + midCnt k) = 121 * (k + 1) := by
  simp only [startByte, midCnt]
  omega

theorem sb_le_sb_mid (k : ℕ) : startByte k ≤ startByte k + midCnt k := Nat.le_add_right _ _

/-- Per-window sum: the bytes of window `k` denote limb `k`'s mid and `lo`
pieces (at weight `2^(121·k)`) plus boundary `k+1`'s `hi` piece (at weight
`2^(121·(k+1))`). -/
theorem window_eq (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hsplit : SplitPieces env bytes splitLo splitHi)
    (k : ℕ) (hk : k < 34) :
    (∑ je ∈ Finset.Ico (min (startByte k) 512) (min (startByte (k + 1)) 512),
        byteVal env bytes je * 2 ^ (8 * je))
      = (midT env bytes k + loT env splitLo k) * 2 ^ (121 * k) + hiNext env splitHi k := by
  rw [winLo_straddle k hk]
  by_cases hlo : 121 * (k + 1) % 8 ≠ 0 ∧ k + 1 < 34
  · -- straddling: peel the straddled byte off the top of the window
    rw [winHi_straddle k hlo.1 hlo.2, Finset.sum_Ico_succ_top (sb_le_sb_mid k),
      mid_window_eq]
    obtain ⟨hl, hh, hrec⟩ := hsplit (k + 1) hlo.2 hlo.1
    have hbyte : byteVal env bytes (startByte k + midCnt k) * 2 ^ (8 * (startByte k + midCnt k))
        = loT env splitLo k * 2 ^ (121 * k) + hiNext env splitHi k := by
      rw [show startByte k + midCnt k = splitByteLE (k + 1) from
        (splitByteLE_next k hlo.1 hlo.2).symm, hrec]
      unfold loT hiNext
      rw [if_pos hlo, if_pos hlo]
      rw [Nat.add_mul, mul_assoc, mul_assoc, ← pow_add, ← pow_add]
      rw [show splitByteLE (k + 1) = startByte k + midCnt k from
        splitByteLE_next k hlo.1 hlo.2]
      rw [show 121 - 121 * (k + 1) % 8 + (121 * k) = 8 * (startByte k + midCnt k) from
        (win_exp1 k hlo.1 hlo.2).symm]
      rw [show 121 * (k + 1) % 8 + 8 * (startByte k + midCnt k) = 121 * (k + 1) from
        win_exp2 k hlo.1 hlo.2]
    rw [hbyte, Nat.add_mul]
    ring
  · -- aligned next boundary (or the top limb): no straddled byte
    rw [winHi_aligned k hk hlo, mid_window_eq]
    have hloZ : loT env splitLo k = 0 := by unfold loT; rw [if_neg hlo]
    have hhiZ : hiNext env splitHi k = 0 := by unfold hiNext; rw [if_neg hlo]
    rw [hloZ, hhiZ]
    ring

/-- Consecutive-`Ico` partition of a sum. -/
theorem sum_Ico_partition (f a : ℕ → ℕ) (hmono : ∀ i, a i ≤ a (i + 1)) (n : ℕ) :
    (∑ k ∈ Finset.range n, ∑ je ∈ Finset.Ico (a k) (a (k + 1)), f je)
      = ∑ je ∈ Finset.Ico (a 0) (a n), f je := by
  have hm : Monotone a := monotone_nat_of_le_succ hmono
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_Ico_consecutive _ (hm (Nat.zero_le m)) (hm (Nat.le_succ m))]

/-- The `hi` pieces reindexed: summing `hiT k · 2^(121·k)` over all limbs equals
summing `hiNext` over all windows. -/
theorem hi_shift (env : Environment (F circomPrime))
    (splitHi : ℕ → Expression (F circomPrime)) :
    (∑ k ∈ Finset.range 34, hiT env splitHi k * 2 ^ (121 * k))
      = ∑ k ∈ Finset.range 34, hiNext env splitHi k := by
  rw [show (34 : ℕ) = 33 + 1 from rfl,
    Finset.sum_range_succ (fun k => hiNext env splitHi k) 33,
    Finset.sum_range_succ' (fun k => hiT env splitHi k * 2 ^ (121 * k)) 33]
  have h0 : hiT env splitHi 0 * 2 ^ (121 * 0) = 0 := by
    unfold hiT
    norm_num
  have h33 : hiNext env splitHi 33 = 0 := by
    unfold hiNext
    rw [if_neg (by omega)]
  rw [h0, h33, Nat.add_zero, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  unfold hiT hiNext
  by_cases h : 121 * (k + 1) % 8 ≠ 0
  · rw [if_pos h, if_pos ⟨h, by omega⟩]
  · rw [if_neg h, if_neg (by tauto), Nat.zero_mul]

/-- **Value theorem.** `packLimbsSplit` denotes the little-endian base-256 value
of the byte vector. -/
theorem packLimbsSplit_value (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (hsplit : SplitPieces env bytes splitLo splitHi) :
    BigInt.value limbBits
        (Vector.map (Expression.eval env) (packLimbsSplit bytes splitLo splitHi))
      = ∑ je ∈ Finset.range 512, byteVal env bytes je * 2 ^ (8 * je) := by
  rw [MulMod.value_map_eval]
  -- LHS: per-limb pieces
  have hlimb : (∑ k : Fin numLimbs,
        (Expression.eval env ((packLimbsSplit bytes splitLo splitHi)[k.val])).val
          * 2 ^ (limbBits * k.val))
      = ∑ k ∈ Finset.range 34,
          ((midT env bytes k + loT env splitLo k) * 2 ^ (121 * k)
            + hiT env splitHi k * 2 ^ (121 * k)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k =>
      (midT env bytes k + loT env splitLo k) * 2 ^ (121 * k)
        + hiT env splitHi k * 2 ^ (121 * k)) 34]
    apply Finset.sum_congr rfl
    intro k _
    rw [packLimbsSplit_limb_eval env bytes splitLo splitHi hbytes hsplit k.val k.isLt]
    show (hiT env splitHi k.val + midT env bytes k.val + loT env splitLo k.val)
        * 2 ^ (121 * k.val) = _
    ring
  rw [hlimb, Finset.sum_add_distrib, hi_shift]
  -- RHS: window partition
  have hpart : (∑ je ∈ Finset.range 512, byteVal env bytes je * 2 ^ (8 * je))
      = ∑ k ∈ Finset.range 34,
          ∑ je ∈ Finset.Ico (min (startByte k) 512) (min (startByte (k + 1)) 512),
            byteVal env bytes je * 2 ^ (8 * je) := by
    rw [sum_Ico_partition (fun je => byteVal env bytes je * 2 ^ (8 * je))
      (fun k => min (startByte k) 512)
      (fun i => by simp only [startByte]; omega) 34]
    rw [show min (startByte 0) 512 = 0 from by norm_num [startByte],
      show min (startByte 34) 512 = 512 from by norm_num [startByte],
      Finset.range_eq_Ico]
  rw [hpart]
  rw [Finset.sum_congr rfl (fun k hk =>
    window_eq env bytes splitLo splitHi hsplit k (Finset.mem_range.mp hk))]
  rw [Finset.sum_add_distrib]

/-- The byte sum is `os2ip` of the evaluated byte vector. -/
theorem byte_sum_eq_os2ip (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512) :
    (∑ je ∈ Finset.range 512, byteVal env bytes je * 2 ^ (8 * je))
      = os2ip (Vector.map (fun e => (Expression.eval env e).val) bytes) := by
  rw [BytesLemmas.os2ip_vec_eq_sum_le]
  apply Finset.sum_congr rfl
  intro je hje
  rw [Finset.mem_range] at hje
  rw [getElem!_pos _ (511 - je) (by omega), Vector.getElem_map]
  rfl

/-! ## Assembly: `SplitPieces` from the circuit constraints -/

/-- Build `SplitPieces` for the 512-byte bignum packing from the 203 witnessed
bits' booleanity and the 29 top-bit booleanity constraints. -/
theorem splitPieces_of_constraints (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) 203)
    (hbool : ∀ (i : ℕ) (hi : i < 203), (Expression.eval env (bits[i]'hi)).val < 2)
    (htop : ∀ s : Fin 29, Expression.eval env (splitTop bytes bits s.val)
        * (Expression.eval env (splitTop bytes bits s.val) - 1) = 0) :
    SplitPieces env bytes (splitLoExpr bits) (splitHiExpr bytes bits) := by
  intro k hk hstr
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have hs : splitIdx k < 29 := splitIdx_lt k hk
  have hsb := splitBoundary_splitIdx k hk1 hk hstr
  have hres := split_sound env bytes bits (splitIdx k) hs
    (fun i hi => by
      unfold bitVal
      rw [dif_pos (by omega : 7 * splitIdx k + i < 203)]
      exact hbool _ _)
    (htop ⟨splitIdx k, hs⟩)
  rw [hsb] at hres
  exact hres

/-- Combined deliverable for the bignum gadget: normalized + value = `os2ip`. -/
theorem packLimbsSplit_value_eq_os2ip (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime))
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (hsplit : SplitPieces env bytes splitLo splitHi) :
    BigInt.value limbBits
        (Vector.map (Expression.eval env) (packLimbsSplit bytes splitLo splitHi))
      = os2ip (fieldBytesToNat (Vector.map (Expression.eval env) bytes)) := by
  rw [packLimbsSplit_value env bytes splitLo splitHi hbytes hsplit, byte_sum_eq_os2ip]
  congr 1
  unfold fieldBytesToNat
  rw [Vector.map_map]
  rfl

/-! ## Completeness of one byte split -/

/-- With the honest bit witnesses (bit `i` of the straddled byte), the implicit
top expression evaluates to the byte's top bit `y / 2^7`. -/
theorem split_complete {nb : ℕ} (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb)
    (s : ℕ) (hnb : 7 * s + 7 ≤ nb)
    (hbits : ∀ (i : ℕ), i < 7 →
      bitVal env bits (7 * s + i)
        = byteVal env bytes (splitByteLE (splitBoundary s)) / 2 ^ i % 2)
    (hbyte : byteVal env bytes (splitByteLE (splitBoundary s)) < 256) :
    Expression.eval env (splitTop bytes bits s)
      = ((byteVal env bytes (splitByteLE (splitBoundary s)) / 2 ^ 7 : ℕ) : F circomPrime) := by
  set y := byteVal env bytes (splitByteLE (splitBoundary s)) with hy
  -- the low seven bits recompose to `y − (y / 2^7) · 2^7`
  have hdecomp : (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i)
      + (y / 2 ^ 7) * 2 ^ 7 = y := by
    have hfull := sum_bits_eq y 8 (by rw [hy]; exact lt_of_lt_of_le hbyte (by norm_num))
    rw [Finset.sum_range_succ] at hfull
    have htopbit : y / 2 ^ 7 % 2 = y / 2 ^ 7 :=
      Nat.mod_eq_of_lt (Nat.div_lt_of_lt_mul (by
        have h128 : (2:ℕ) ^ 7 = 128 := by norm_num
        omega))
    rw [htopbit] at hfull
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [hbits i (Finset.mem_range.mp hi)])]
    exact hfull
  have hL_le : (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i) ≤ y := by omega
  rw [eval_splitTop, ← hy]
  rw [show ((y : ℕ) : F circomPrime)
        - ((∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i : ℕ) : F circomPrime)
      = (((y - (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i) : ℕ)) : F circomPrime)
    from by rw [Nat.cast_sub hL_le]]
  rw [show y - (∑ i ∈ Finset.range 7, bitVal env bits (7 * s + i) * 2 ^ i)
      = (y / 2 ^ 7) * 2 ^ 7 from by omega]
  rw [Nat.cast_mul, mul_comm ((((y / 2 ^ 7) : ℕ)) : F circomPrime), ← mul_assoc,
    inv_mul_cancel₀ pow7_ne_zero, one_mul]

/-- A field element equal to the cast of `0` or `1` satisfies the booleanity
row `x · (x − 1) = 0`. -/
theorem mul_sub_one_zero_of_lt_two {x : F circomPrime} {n : ℕ} (hn : n < 2)
    (hx : x = ((n : ℕ) : F circomPrime)) : x * (x - 1) = 0 := by
  rcases (show n = 0 ∨ n = 1 from by omega) with h | h <;> subst h <;> rw [hx] <;> norm_num

/-- A field element with `.val < 2` satisfies the booleanity row in the
`x · (x + -1)` shape `circuit_norm` leaves. -/
theorem mul_add_neg_one_eq_zero (x : F circomPrime) (h : x.val < 2) :
    x * (x + -1) = 0 := by
  have hcase : x = 0 ∨ x = 1 := by
    rcases (show x.val = 0 ∨ x.val = 1 from by omega) with h0 | h1
    · exact Or.inl ((ZMod.val_eq_zero x).mp h0)
    · refine Or.inr ?_
      rw [← ZMod.natCast_zmod_val x, h1, Nat.cast_one]
  rcases hcase with rfl | rfl <;> ring

/-- Turn an evaluated `a · (a − 1) = 0` constraint into the same fact about
`eval a`. -/
theorem eval_mul_sub_one (env : Environment (F circomPrime))
    (a : Expression (F circomPrime))
    (h : Expression.eval env (a * (a - 1)) = 0) :
    Expression.eval env a * (Expression.eval env a - 1) = 0 := by
  rw [eval_mul', eval_sub',
    show Expression.eval env (1 : Expression (F circomPrime)) = 1 from rfl] at h
  exact h

/-- Discharge an `a · (a − 1) = 0` obligation when `eval a` is a boolean cast. -/
theorem eval_mul_sub_one_zero (env : Environment (F circomPrime))
    (a : Expression (F circomPrime)) (n : ℕ) (hn : n < 2)
    (ha : Expression.eval env a = ((n : ℕ) : F circomPrime)) :
    Expression.eval env (a * (a - 1)) = 0 := by
  rw [eval_mul', eval_sub',
    show Expression.eval env (1 : Expression (F circomPrime)) = 1 from rfl, ha]
  rcases (show n = 0 ∨ n = 1 from by omega) with h | h <;> subst h <;> norm_num

/-! ## EM (PadDigest) instantiation -/

theorem splitByteLE_const_region (k : ℕ) (h3 : 3 ≤ k) :
    32 ≤ splitByteLE k ∧ splitByteLE k ≤ 511 - 32 ∨ 32 ≤ splitByteLE k := by
  right
  simp only [splitByteLE]
  omega

theorem splitByteLE_ge_32 (k : ℕ) (h3 : 3 ≤ k) : 32 ≤ splitByteLE k := by
  simp only [splitByteLE]
  omega

theorem splitByteLE_le_511 (k : ℕ) : splitByteLE k ≤ 511 ∨ True := Or.inr trivial

/-- The EM byte at little-endian index `je ≥ 32` is the constant
`emByteConst (511 − je)`. -/
theorem em_byteVal_const (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32) (je : ℕ)
    (hje : 32 ≤ je) :
    byteVal env (emByteExpr digBytes) je = emByteConst (511 - je) := by
  unfold byteVal emByteExpr
  rw [Vector.getElem_ofFn]
  rw [if_pos (show ((⟨511 - je, by omega⟩ : Fin 512) : ℕ) < 480 from by
    show 511 - je < 480; omega)]
  exact val_natCast_lt' (lt_trans (emByteConst_lt _) two_pow_256_lt_circomPrime)

/-- The EM byte at little-endian index `je < 32` is digest byte `31 − je`. -/
theorem em_byteVal_digest (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32) (je : ℕ) (hje : je < 32) :
    byteVal env (emByteExpr digBytes) je
      = (Expression.eval env (digBytes[31 - je]'(by omega))).val := by
  unfold byteVal emByteExpr
  rw [Vector.getElem_ofFn]
  rw [if_neg (show ¬(((⟨511 - je, by omega⟩ : Fin 512) : ℕ) < 480) from by
    show ¬(511 - je < 480); omega)]
  rw [getElem_congr_idx (show ((⟨511 - je, by omega⟩ : Fin 512) : ℕ) - 480 = 31 - je from by
    show 511 - je - 480 = 31 - je; omega)]

/-- Every EM byte is `< 256`, given the digest bytes are. -/
theorem em_bytes_lt (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (hoct : ∀ (dj : ℕ) (hdj : dj < 32), (Expression.eval env (digBytes[dj]'hdj)).val < 256) :
    ∀ je, je < 512 → byteVal env (emByteExpr digBytes) je < 256 := by
  intro je hje
  by_cases h : je < 32
  · rw [em_byteVal_digest env digBytes je h]
    exact hoct (31 - je) (by omega)
  · rw [em_byteVal_const env digBytes je (by omega)]
    exact emByteConst_lt _

/-- `SplitPieces` for the EM packing: the two digest-region boundaries are
discharged by the witnessed splits, the constant-region boundaries by
arithmetic on the constant bytes. -/
theorem em_splitPieces (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (bits : Vector (Expression (F circomPrime)) 14)
    (hbool : ∀ (i : ℕ) (hi : i < 14), (Expression.eval env (bits[i]'hi)).val < 2)
    (htop : ∀ s : Fin 2,
      Expression.eval env (splitTop (emByteExpr digBytes) bits s.val)
        * (Expression.eval env (splitTop (emByteExpr digBytes) bits s.val) - 1) = 0) :
    SplitPieces env (emByteExpr digBytes) (emSplitLo bits)
      (emSplitHi (emByteExpr digBytes) bits) := by
  intro k hk hstr
  unfold emSplitLo emSplitHi
  by_cases h3 : k < 3
  · rw [if_pos h3, if_pos h3]
    have hbool' : ∀ (s : ℕ), s < 2 → ∀ (i : ℕ), i < 7 → bitVal env bits (7 * s + i) < 2 := by
      intro s hs i hi
      unfold bitVal
      rw [dif_pos (by omega : 7 * s + i < 14)]
      exact hbool _ _
    rcases (show k = 1 ∨ k = 2 from by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; omega
        · omega) with h | h
    · subst h
      have hres := split_sound env (emByteExpr digBytes) bits 0 (by norm_num)
        (hbool' 0 (by norm_num)) (htop ⟨0, by norm_num⟩)
      rw [show splitBoundary 0 = 1 from rfl] at hres
      exact hres
    · subst h
      have hres := split_sound env (emByteExpr digBytes) bits 1 (by norm_num)
        (hbool' 1 (by norm_num)) (htop ⟨1, by norm_num⟩)
      rw [show splitBoundary 1 = 2 from rfl] at hres
      exact hres
  · -- constant region: split the constant byte arithmetically
    rw [if_neg h3, if_neg h3]
    have hc := emByteConst_lt (511 - splitByteLE k)
    have ht8 : 121 * k % 8 < 8 := Nat.mod_lt _ (by norm_num)
    refine ⟨?_, ?_, ?_⟩
    · rw [eval_const', val_natCast_lt' (lt_trans
        (lt_of_le_of_lt (Nat.mod_le _ _) hc) two_pow_256_lt_circomPrime)]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · rw [eval_const', val_natCast_lt' (lt_trans
        (lt_of_le_of_lt (Nat.div_le_self _ _) hc) two_pow_256_lt_circomPrime)]
      apply Nat.div_lt_of_lt_mul
      calc emByteConst (511 - splitByteLE k) < 256 := hc
        _ ≤ 2 ^ (121 * k % 8) * 2 ^ (8 - 121 * k % 8) := by
            rw [← pow_add, show 121 * k % 8 + (8 - 121 * k % 8) = 8 from by omega]
            norm_num
    · rw [em_byteVal_const env digBytes _ (splitByteLE_ge_32 k (by omega)),
        eval_const', eval_const',
        val_natCast_lt' (lt_trans
          (lt_of_le_of_lt (Nat.mod_le _ _) hc) two_pow_256_lt_circomPrime),
        val_natCast_lt' (lt_trans
          (lt_of_le_of_lt (Nat.div_le_self _ _) hc) two_pow_256_lt_circomPrime)]
      exact (Nat.mod_add_div' _ _).symm

/-- The EM byte sum is `< 2^4088` (the EM top byte is `0x00`). -/
theorem em_byte_sum_lt (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (hoct : ∀ (dj : ℕ) (hdj : dj < 32), (Expression.eval env (digBytes[dj]'hdj)).val < 256) :
    (∑ je ∈ Finset.range 512, byteVal env (emByteExpr digBytes) je * 2 ^ (8 * je))
      < 2 ^ 4088 := by
  rw [show (512 : ℕ) = 511 + 1 from rfl, Finset.sum_range_succ]
  have htop : byteVal env (emByteExpr digBytes) 511 = 0 := by
    rw [em_byteVal_const env digBytes 511 (by omega)]
    rfl
  rw [htop, Nat.zero_mul, Nat.add_zero,
    show (4088 : ℕ) = 8 * 511 from by norm_num]
  exact sum_range_lt_pow (B := 8) _
    (fun je hje => em_bytes_lt env digBytes hoct je (by omega))

end BytesSplitLemmas
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
