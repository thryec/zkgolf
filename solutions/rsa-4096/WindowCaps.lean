import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXV

/-!
# Triangular window-sum caps for the fused triple-product coefficient bounds

The fused-final gadget `SqMulModTo` certifies `a²·b = q·n + em` over `3m−1`
coefficients. For the *graduated* grouped equality (`GroupedEqXV`) we need
per-position coefficient bounds. The triple-product coefficient `z2[k]` is a sum
over an antidiagonal window whose weight is bounded by two triangular numbers
(one per flank); the `q·n` coefficient `z3[k]` by a plain window count. These
lemmas provide the closed-form triangular caps `Σ ≤ (k+1)(k+2)/2` and
`Σ ≤ (3m−2−k)(3m−1−k)/2`, kept `O(1)` so the per-boundary `GVXHyps` obligations
stay `decide`-able at concrete parameters.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace WindowCaps

open Finset

/-- `Σ_{i<n} (i+1) = n(n+1)/2`. -/
lemma sum_range_succ_id (n : ℕ) : (∑ i ∈ range n, (i + 1)) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
    have hu : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
    omega

/-- Left triangular cap: a guarded sum whose terms are `≤ i+1` and whose guard
forces `i ≤ k` is at most `(k+1)(k+2)/2`. -/
lemma guarded_sum_le_triL {L k : ℕ} (g : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hg : ∀ i, g i ≤ i + 1) (hP : ∀ i, P i → i ≤ k) :
    (∑ i ∈ range L, if P i then g i else 0) ≤ (k + 1) * (k + 2) / 2 := by
  calc (∑ i ∈ range L, if P i then g i else 0)
      ≤ ∑ i ∈ range L, if i ≤ k then (i + 1) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hpi : P i
        · rw [if_pos hpi, if_pos (hP i hpi)]; exact hg i
        · rw [if_neg hpi]; positivity
    _ = ∑ i ∈ (range L).filter (· ≤ k), (i + 1) := by rw [Finset.sum_filter]
    _ ≤ ∑ i ∈ range (k + 1), (i + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_filter] at hi
          exact Finset.mem_range.mpr (by omega)
        · intro i _ _; positivity
    _ = (k + 1) * (k + 2) / 2 := by rw [sum_range_succ_id]

/-- Right triangular cap: a guarded sum over `range L` (`L = 2m−1`) whose terms
are `≤ 2m−1−i` and whose guard forces `k − i < m` is at most
`(3m−2−k)(3m−1−k)/2`. -/
lemma guarded_sum_le_triR {m k : ℕ} (hm : 1 ≤ m) (hk : k ≤ 3 * m - 3) (g : ℕ → ℕ) (P : ℕ → Prop)
    [DecidablePred P]
    (hg : ∀ i, g i ≤ 2 * m - 1 - i) (hP : ∀ i, P i → k - i < m) :
    (∑ i ∈ range (2 * m - 1), if P i then g i else 0) ≤ (3 * m - 2 - k) * (3 * m - 1 - k) / 2 := by
  -- reindex j = (2m-2) - i, so the term weight 2m-1-i becomes j+1
  have hkey : (∑ i ∈ range (2 * m - 1), if P i then g i else 0)
      ≤ ∑ i ∈ range (2 * m - 1), if k - i < m then (2 * m - 1 - i) else 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hpi : P i
    · rw [if_pos hpi, if_pos (hP i hpi)]; exact hg i
    · by_cases hg2 : k - i < m
      · rw [if_neg hpi, if_pos hg2]; positivity
      · rw [if_neg hpi, if_neg hg2]
  refine le_trans hkey ?_
  -- reflect the index j = (2m-2) - i via `sum_range_reflect`
  set F : ℕ → ℕ := fun i => if k - i < m then (2 * m - 1 - i) else 0 with hF
  rw [← Finset.sum_range_reflect F (2 * m - 1)]
  -- after reflect, the term at j is F((2m-2)-j) = if k-(2m-2-j)<m then j+1 else 0
  have hstep : ∀ j ∈ range (2 * m - 1),
      F (2 * m - 1 - 1 - j)
        = (if k - (2 * m - 2 - j) < m then (j + 1) else 0) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only [hF]
    have he : 2 * m - 1 - 1 - j = 2 * m - 2 - j := by omega
    rw [he]
    by_cases hc : k - (2 * m - 2 - j) < m
    · rw [if_pos hc, if_pos hc]; congr 1; omega
    · rw [if_neg hc, if_neg hc]
  rw [Finset.sum_congr rfl hstep]
  calc (∑ j ∈ range (2 * m - 1), if k - (2 * m - 2 - j) < m then (j + 1) else 0)
      ≤ ∑ j ∈ range (2 * m - 1), if j ≤ 3 * m - 3 - k then (j + 1) else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        by_cases hc : k - (2 * m - 2 - j) < m
        · rw [if_pos hc]
          by_cases hc2 : j ≤ 3 * m - 3 - k
          · rw [if_pos hc2]
          · rw [if_neg hc2]; omega
        · rw [if_neg hc]; positivity
    _ = ∑ j ∈ (range (2 * m - 1)).filter (· ≤ 3 * m - 3 - k), (j + 1) := by rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ range (3 * m - 3 - k + 1), (j + 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          rw [Finset.mem_filter] at hj
          exact Finset.mem_range.mpr (by omega)
        · intro j _ _; positivity
    _ = (3 * m - 3 - k + 1) * (3 * m - 3 - k + 2) / 2 := by rw [sum_range_succ_id]
    _ = (3 * m - 2 - k) * (3 * m - 1 - k) / 2 := by
        have e1 : 3 * m - 3 - k + 1 = 3 * m - 2 - k := by omega
        have e2 : 3 * m - 3 - k + 2 = 3 * m - 1 - k := by omega
        rw [e1, e2]

/-- Window-count cap for the `q·n` coefficient: the number of index pairs
`(i, k−i)` with `i < 2m`, `k − i < m` is `≤ min(k+1, m, 3m−1−k)`, hence the
guarded constant sum is bounded coordinate-wise. -/
lemma guarded_count_le_qn {m k : ℕ} (c : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i, P i → i ≤ k ∧ k - i < m) :
    (∑ i ∈ range (2 * m), if P i then c else 0) ≤ min (k + 1) (min m (3 * m - 1 - k)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, Nat.add_zero, Finset.sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  -- card of the filter set is ≤ each of the three bounds
  set S := (range (2 * m)).filter (fun i => P i) with hS
  have hmemS : ∀ i, i ∈ S → i ≤ k ∧ k - i < m ∧ i < 2 * m := by
    intro i hi
    rw [hS, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨(hP i hi.2).1, (hP i hi.2).2, hi.1⟩
  have hc1 : S.card ≤ k + 1 := by
    have := Finset.card_le_card_of_injOn (s := S) (t := range (k + 1)) (fun i => i)
      (fun i hi => Finset.mem_range.mpr (by have h := (hmemS i hi).1; show i < k + 1; omega))
      (fun x _ y _ h => h)
    simpa using this
  have hc2 : S.card ≤ m := by
    have := Finset.card_le_card_of_injOn (s := S) (t := range m) (fun i => i - (k + 1 - m))
      (fun i hi => Finset.mem_range.mpr (by
        have h := hmemS i hi
        have hh : i - (k + 1 - m) < m := by omega
        exact hh))
      (fun x hx y hy hxy => by
        have hx2 := hmemS x (Finset.mem_coe.mp hx)
        have hy2 := hmemS y (Finset.mem_coe.mp hy)
        have : x - (k + 1 - m) = y - (k + 1 - m) := hxy
        omega)
    simpa using this
  have hc3 : S.card ≤ 3 * m - 1 - k := by
    have := Finset.card_le_card_of_injOn (s := S) (t := range (3 * m - 1 - k))
      (fun i => i - (k + 1 - m))
      (fun i hi => Finset.mem_range.mpr (by
        have h := hmemS i hi
        have hh : i - (k + 1 - m) < 3 * m - 1 - k := by omega
        exact hh))
      (fun x hx y hy hxy => by
        have hx2 := hmemS x (Finset.mem_coe.mp hx)
        have hy2 := hmemS y (Finset.mem_coe.mp hy)
        have : x - (k + 1 - m) = y - (k + 1 - m) := hxy
        omega)
    simpa using this
  exact le_min hc1 (le_min hc2 hc3)

/-! ## Per-position coefficient bounds for the fused triple product -/

section Coeff
variable {p : ℕ} [Fact p.Prime]
open MulMod (mulNoReduceX)

/-- Triangular closed-form cap on the triple-product window weight. -/
def triCap (m k : ℕ) : ℕ := min ((k + 1) * (k + 2) / 2) ((3 * m - 2 - k) * (3 * m - 1 - k) / 2)

/-- Window-count closed-form cap on the `q·n` window. -/
def qnCap (m k : ℕ) : ℕ := min (k + 1) (min m (3 * m - 1 - k))

/-- **Per-position bound for the triple-product coefficient** `z2[k] = (a·a)·b`.
Chaining the tent bound on the inner square (`z1[i] ≤ min(i+1,2m−1−i)·(2^B−1)²`)
through the weighted-window lemma yields `z2[k].val ≤ triCap(m,k)·(2^B−1)³`. -/
lemma z2_coeff_le {B m : ℕ} [NeZero m] (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (Z1 : Vector (Expression (F p)) (2 * m - 1))
    (k : Fin ((2 * m - 1) + m - 1)) (hm : 1 ≤ m)
    (hZ1 : ∀ i : Fin (2 * m - 1),
      Expression.eval env Z1[i.val] = Expression.eval env (bigIntMulNoReduce a a)[i.val])
    (ha : ∀ i : Fin m, (Expression.eval env (a[i.val]'i.isLt)).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env (b[i.val]'i.isLt)).val < 2 ^ B)
    (hbound_aa : m * (2 ^ B * 2 ^ B) < p)
    (hfield : (3 * m) * (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) < p) :
    (Expression.eval env ((mulNoReduceX Z1 b)[k.val])).val
      ≤ triCap m k.val * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) := by
  haveI : NeZero (2 * m - 1) := ⟨by omega⟩
  set C2 := (2 ^ B - 1) * (2 ^ B - 1) with hC2
  set C3 := (2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1) with hC3
  -- inner tent bound on z1
  have hZ1le : ∀ i : Fin (2 * m - 1),
      (Expression.eval env (Z1[i.val]'i.isLt)).val ≤ min (i.val + 1) (2 * m - 1 - i.val) * C2 := by
    intro i
    have hbridge : Expression.eval env (Z1[i.val]'i.isLt)
        = Expression.eval env ((bigIntMulNoReduce a a)[i.val]) := hZ1 i
    rw [hbridge]
    exact GroupedEqV.val_bigIntMulNoReduce_coeff_le_pos env a a i ha ha hbound_aa
  -- the guarded weight sum (with t(i) = min(i+1,2m-1-i)·C2)
  set t : ℕ → ℕ := fun i => min (i + 1) (2 * m - 1 - i) * C2 with ht
  set gsum := ∑ i ∈ Finset.range (2 * m - 1),
      (if i ≤ k.val ∧ k.val - i < m then t i * (2 ^ B - 1) else 0) with hgsum
  -- gsum ≤ triCap(m, k)·C3, via the two triangular caps
  have hgsum_le : gsum ≤ triCap m k.val * C3 := by
    have hpull : gsum
        = (∑ i ∈ Finset.range (2 * m - 1),
            (if i ≤ k.val ∧ k.val - i < m then min (i + 1) (2 * m - 1 - i) else 0)) * C3 := by
      rw [hgsum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ≤ k.val ∧ k.val - i < m
      · rw [if_pos h, if_pos h, ht]; simp only [hC3, hC2]; ring
      · rw [if_neg h, if_neg h, Nat.zero_mul]
    rw [hpull]
    apply Nat.mul_le_mul_right
    refine le_min ?_ ?_
    · exact guarded_sum_le_triL (fun i => min (i + 1) (2 * m - 1 - i))
        (fun i => i ≤ k.val ∧ k.val - i < m) (fun i => Nat.min_le_left _ _) (fun i h => h.1)
    · have hkle : k.val ≤ 3 * m - 3 := by have := k.isLt; omega
      exact guarded_sum_le_triR hm hkle (fun i => min (i + 1) (2 * m - 1 - i))
        (fun i => i ≤ k.val ∧ k.val - i < m) (fun i => Nat.min_le_right _ _) (fun i h => h.2)
  have hgsum_ltp : gsum < p := by
    have htrile : triCap m k.val ≤ (3 * m) * (3 * m) := by
      unfold triCap
      have h1 : (k.val + 1) * (k.val + 2) / 2 ≤ (k.val + 1) * (k.val + 2) := Nat.div_le_self _ _
      have hk := k.isLt
      calc min ((k.val + 1) * (k.val + 2) / 2) _
          ≤ (k.val + 1) * (k.val + 2) / 2 := Nat.min_le_left _ _
        _ ≤ (k.val + 1) * (k.val + 2) := Nat.div_le_self _ _
        _ ≤ (3 * m) * (3 * m) := by
            apply Nat.mul_le_mul <;> omega
    calc gsum ≤ triCap m k.val * C3 := hgsum_le
      _ ≤ (3 * m) * (3 * m) * C3 := Nat.mul_le_mul_right _ htrile
      _ < p := hfield
  -- apply the weighted-window lemma
  have hweighted := val_mulNoReduceX_coeff_le_weighted (B := B) env Z1 b k t
    (fun i => hZ1le i) hb (by
      have : (∑ i ∈ Finset.range (2 * m - 1),
          (if i ≤ k.val ∧ k.val - i < m then t i * (2 ^ B - 1) else 0)) = gsum := rfl
      rw [this]; exact hgsum_ltp)
  calc (Expression.eval env ((mulNoReduceX Z1 b)[k.val])).val
      ≤ ∑ i ∈ Finset.range (2 * m - 1),
          (if i ≤ k.val ∧ k.val - i < m then t i * (2 ^ B - 1) else 0) := hweighted
    _ = gsum := rfl
    _ ≤ triCap m k.val * C3 := hgsum_le

/-- **Per-position bound for the `q·n` coefficient** `z3[k]`. The window count is
capped by `qnCap(m,k)`, each pair contributing `< (2^B−1)²`. -/
lemma z3_coeff_le {B m : ℕ} [NeZero m] (env : Environment (F p))
    (q : Vector (Expression (F p)) (2 * m)) (n : Var (BigInt m) (F p))
    (k : Fin ((2 * m) + m - 1)) (hm : 1 ≤ m)
    (hq : ∀ i : Fin (2 * m), (Expression.eval env (q[i.val]'i.isLt)).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env (n[i.val]'i.isLt)).val < 2 ^ B)
    (hfield : (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1)) < p) :
    (Expression.eval env ((mulNoReduceX q n)[k.val])).val
      ≤ qnCap m k.val * ((2 ^ B - 1) * (2 ^ B - 1)) := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  set C2 := (2 ^ B - 1) * (2 ^ B - 1) with hC2
  set gsum := ∑ i ∈ Finset.range (2 * m),
      (if i ≤ k.val ∧ k.val - i < m then (2 ^ B - 1) * (2 ^ B - 1) else 0) with hgsum
  have hgsum_le : gsum ≤ qnCap m k.val * C2 := by
    rw [hgsum, hC2]
    exact guarded_count_le_qn C2 (fun i => i ≤ k.val ∧ k.val - i < m) (fun i h => h)
  have hgsum_ltp : gsum < p := by
    have hcap : qnCap m k.val ≤ 3 * m := by
      unfold qnCap
      exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_left _ _) (by omega))
    calc gsum ≤ qnCap m k.val * C2 := hgsum_le
      _ ≤ (3 * m) * C2 := Nat.mul_le_mul_right _ hcap
      _ < p := hfield
  have hweighted := val_mulNoReduceX_coeff_le_weighted (B := B) env q n k
    (fun _ => 2 ^ B - 1) (fun i => Nat.le_pred_of_lt (hq i)) hn (by
      have heq : (∑ i ∈ Finset.range (2 * m),
          (if i ≤ k.val ∧ k.val - i < m then (2 ^ B - 1) * (2 ^ B - 1) else 0)) = gsum := rfl
      rw [heq]; exact hgsum_ltp)
  calc (Expression.eval env ((mulNoReduceX q n)[k.val])).val
      ≤ ∑ i ∈ Finset.range (2 * m),
          (if i ≤ k.val ∧ k.val - i < m then (2 ^ B - 1) * (2 ^ B - 1) else 0) := hweighted
    _ = gsum := rfl
    _ ≤ qnCap m k.val * C2 := hgsum_le

/-! ## Top-limb-aware weighted caps

The closed-form caps above treat every limb as a full `2^B − 1`. The operands of
the fused step are tighter: `a`, `b`, `n` have `tb`-bit top limbs and the
quotient `q` has a `tq`-bit top limb (over `2m` limbs). The graduated caps below
track those top limbs through the two convolution stages, which shrinks the
coefficient bounds near the right flank and lets the tail carries of the
grouped equality be range-checked at much smaller widths. -/

/-- Position-dependent limb cap: the top limb of an `L`-limb operand is
`tw`-bit, all lower limbs are full `B`-bit. -/
def limbCap (B tw L j : ℕ) : ℕ := if j = L - 1 then 2 ^ tw - 1 else 2 ^ B - 1

/-- Guarded weighted convolution cap `Σ_{i ≤ k, k−i < n₂} t(i)·s(k−i)`. -/
def wconv (n₁ n₂ : ℕ) (t s : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ range n₁, if i ≤ k ∧ k - i < n₂ then t i * s (k - i) else 0

/-- Top-limb-aware cap on the inner-square coefficients `z1 = a·a`. -/
def sqCapW (B tb m : ℕ) : ℕ → ℕ := wconv m m (limbCap B tb m) (limbCap B tb m)

/-- Top-limb-aware cap on the triple-product coefficients `z2 = (a·a)·b`. -/
def triCapW (B tb m : ℕ) : ℕ → ℕ := wconv (2 * m - 1) m (sqCapW B tb m) (limbCap B tb m)

/-- Top-limb-aware cap on the `q·n` coefficients (`q` spans `2m` limbs with a
`tq`-bit top limb). -/
def qnCapW (B tb tq m : ℕ) : ℕ → ℕ := wconv (2 * m) m (limbCap B tq (2 * m)) (limbCap B tb m)

lemma limbCap_le {B tw : ℕ} (htw : tw ≤ B) (L j : ℕ) : limbCap B tw L j ≤ 2 ^ B - 1 := by
  unfold limbCap
  split
  · exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) htw) 1
  · exact le_refl _

lemma wconv_mono {n₁ n₂ : ℕ} {t t' s s' : ℕ → ℕ} (ht : ∀ i, t i ≤ t' i)
    (hs : ∀ j, s j ≤ s' j) (k : ℕ) : wconv n₁ n₂ t s k ≤ wconv n₁ n₂ t' s' k := by
  unfold wconv
  apply Finset.sum_le_sum
  intro i _
  split
  · exact Nat.mul_le_mul (ht i) (hs (k - i))
  · exact le_refl _

/-- Window count for the `m × m` square window: `≤ min(k+1, 2m−1−k)`. -/
lemma guarded_count_le_sq {m k : ℕ} (c : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ i, P i → i ≤ k ∧ k - i < m) :
    (∑ i ∈ range m, if P i then c else 0) ≤ min (k + 1) (2 * m - 1 - k) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, Nat.add_zero, Finset.sum_const, smul_eq_mul]
  apply Nat.mul_le_mul_right
  set S := (range m).filter (fun i => P i) with hS
  have hmemS : ∀ i, i ∈ S → i ≤ k ∧ k - i < m ∧ i < m := by
    intro i hi
    rw [hS, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨(hP i hi.2).1, (hP i hi.2).2, hi.1⟩
  have hc1 : S.card ≤ k + 1 := by
    have := Finset.card_le_card_of_injOn (s := S) (t := range (k + 1)) (fun i => i)
      (fun i hi => Finset.mem_range.mpr (by have h := (hmemS i hi).1; show i < k + 1; omega))
      (fun x _ y _ h => h)
    simpa using this
  have hc2 : S.card ≤ 2 * m - 1 - k := by
    have := Finset.card_le_card_of_injOn (s := S) (t := range (2 * m - 1 - k))
      (fun i => i - (k + 1 - m))
      (fun i hi => Finset.mem_range.mpr (by
        have h := hmemS i hi
        have hh : i - (k + 1 - m) < 2 * m - 1 - k := by omega
        exact hh))
      (fun x hx y hy hxy => by
        have hx2 := hmemS x (Finset.mem_coe.mp hx)
        have hy2 := hmemS y (Finset.mem_coe.mp hy)
        have : x - (k + 1 - m) = y - (k + 1 - m) := hxy
        omega)
    simpa using this
  exact le_min hc1 hc2

/-- The weighted square cap is below the tent. -/
lemma sqCapW_le_tent {B tb m : ℕ} (htb : tb ≤ B) (i : ℕ) :
    sqCapW B tb m i ≤ min (i + 1) (2 * m - 1 - i) * ((2 ^ B - 1) * (2 ^ B - 1)) := by
  calc sqCapW B tb m i
      ≤ wconv m m (fun _ => 2 ^ B - 1) (fun _ => 2 ^ B - 1) i :=
        wconv_mono (limbCap_le htb m) (limbCap_le htb m) i
    _ ≤ min (i + 1) (2 * m - 1 - i) * ((2 ^ B - 1) * (2 ^ B - 1)) := by
        unfold wconv
        exact guarded_count_le_sq _ (fun j => j ≤ i ∧ i - j < m) (fun _ h => h)

/-- The weighted triple-product cap is below the triangular closed form. -/
lemma triCapW_le_tri {B tb m : ℕ} (htb : tb ≤ B) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ 3 * m - 3) :
    triCapW B tb m k ≤ triCap m k * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) := by
  set C2 := (2 ^ B - 1) * (2 ^ B - 1) with hC2
  set C3 := (2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1) with hC3
  have h1 : triCapW B tb m k
      ≤ wconv (2 * m - 1) m (fun i => min (i + 1) (2 * m - 1 - i) * C2) (fun _ => 2 ^ B - 1) k :=
    wconv_mono (sqCapW_le_tent htb) (limbCap_le htb m) k
  refine le_trans h1 ?_
  have hpull : wconv (2 * m - 1) m (fun i => min (i + 1) (2 * m - 1 - i) * C2) (fun _ => 2 ^ B - 1) k
      = (∑ i ∈ range (2 * m - 1),
          (if i ≤ k ∧ k - i < m then min (i + 1) (2 * m - 1 - i) else 0)) * C3 := by
    unfold wconv
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i ≤ k ∧ k - i < m
    · rw [if_pos h, if_pos h, hC3, hC2]; ring
    · rw [if_neg h, if_neg h, Nat.zero_mul]
  rw [hpull]
  apply Nat.mul_le_mul_right
  refine le_min ?_ ?_
  · exact guarded_sum_le_triL (fun i => min (i + 1) (2 * m - 1 - i))
      (fun i => i ≤ k ∧ k - i < m) (fun i => Nat.min_le_left _ _) (fun i h => h.1)
  · exact guarded_sum_le_triR hm hk (fun i => min (i + 1) (2 * m - 1 - i))
      (fun i => i ≤ k ∧ k - i < m) (fun i => Nat.min_le_right _ _) (fun i h => h.2)

/-- The weighted `q·n` cap is below the window-count closed form. -/
lemma qnCapW_le_qn {B tb tq m : ℕ} (htb : tb ≤ B) (htq : tq ≤ B) (k : ℕ) :
    qnCapW B tb tq m k ≤ qnCap m k * ((2 ^ B - 1) * (2 ^ B - 1)) := by
  calc qnCapW B tb tq m k
      ≤ wconv (2 * m) m (fun _ => 2 ^ B - 1) (fun _ => 2 ^ B - 1) k :=
        wconv_mono (limbCap_le htq (2 * m)) (limbCap_le htb m) k
    _ ≤ qnCap m k * ((2 ^ B - 1) * (2 ^ B - 1)) := by
        unfold wconv
        exact guarded_count_le_qn _ (fun i => i ≤ k ∧ k - i < m) (fun _ h => h)

/-- Doubly-weighted window bound: both operands carry per-position caps. -/
lemma val_mulNoReduceX_coeff_le_weighted2 {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (k : Fin (n₁ + n₂ - 1)) (t s : ℕ → ℕ)
    (ha : ∀ i : Fin n₁, (Expression.eval env (a[i.val]'i.isLt)).val ≤ t i.val)
    (hb : ∀ i : Fin n₂, (Expression.eval env (b[i.val]'i.isLt)).val ≤ s i.val)
    (hsum_lt : wconv n₁ n₂ t s k.val < p) :
    (Expression.eval env ((mulNoReduceX a b)[k.val])).val ≤ wconv n₁ n₂ t s k.val := by
  set natConv := ∑ i : Fin n₁, if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0 with hnat
  have hterm : ∀ i : Fin n₁, (if h : i.val ≤ k.val ∧ k.val - i.val < n₂ then
      (Expression.eval env a[i.val]).val
        * (Expression.eval env (b[k.val - i.val]'h.2)).val else 0)
      ≤ (if i.val ≤ k.val ∧ k.val - i.val < n₂ then t i.val * s (k.val - i.val) else 0) := by
    intro i
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
    · rw [dif_pos h, if_pos h]
      exact Nat.mul_le_mul (ha i) (hb ⟨k.val - i.val, h.2⟩)
    · rw [dif_neg h, if_neg h]
  have hle : natConv ≤ wconv n₁ n₂ t s k.val := by
    rw [hnat, wconv, ← Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ k.val ∧ k.val - i < n₂ then t i * s (k.val - i) else 0)]
    exact Finset.sum_le_sum (fun i _ => hterm i)
  have hlt : natConv < p := lt_of_le_of_lt hle hsum_lt
  have hcast : Expression.eval env ((mulNoReduceX a b)[k.val]) = ((natConv : ℕ) : F p) := by
    rw [MulMod.eval_mulNoReduceX_coeff env a b k, hnat, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
    · simp only [dif_pos h]
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    · simp only [dif_neg h, Nat.cast_zero]
  rw [hcast, ZMod.val_natCast_of_lt hlt]
  exact hle

/-- Weighted per-position bound for `bigIntMulNoReduce a b` coefficients. -/
lemma val_bigIntMulNoReduce_coeff_le_wconv {B m : ℕ} [NeZero m] (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1)) (t s : ℕ → ℕ)
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hat : ∀ i : Fin m, (Expression.eval env a[i.val]).val ≤ t i.val)
    (hbt : ∀ i : Fin m, (Expression.eval env b[i.val]).val ≤ s i.val)
    (hbound : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val ≤ wconv m m t s k.val := by
  rw [val_bigIntMulNoReduce_coeff env a b k ha hb hbound]
  rw [wconv, ← Fin.sum_univ_eq_sum_range
    (fun i => if i ≤ k.val ∧ k.val - i < m then t i * s (k.val - i) else 0)]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h]
    exact Nat.mul_le_mul (hat i) (hbt ⟨k.val - i.val, h.2⟩)
  · rw [dif_neg h, if_neg h]

/-- Per-position limb caps from normalization plus a top-limb bound. -/
lemma limb_caps_of_top {B tw L : ℕ} [NeZero L] (env : Environment (F p))
    (x : Vector (Expression (F p)) L)
    (hx : ∀ i : Fin L, (Expression.eval env (x[i.val]'i.isLt)).val < 2 ^ B)
    (hx_top : (Expression.eval env (x[L - 1]'(by have := Nat.pos_of_neZero L; omega))).val < 2 ^ tw) :
    ∀ i : Fin L, (Expression.eval env (x[i.val]'i.isLt)).val ≤ limbCap B tw L i.val := by
  intro i
  unfold limbCap
  by_cases h : i.val = L - 1
  · rw [if_pos h]
    refine Nat.le_pred_of_lt ?_
    have hx' := hx_top
    have hidx : x[i.val]'i.isLt = x[L - 1]'(by have := Nat.pos_of_neZero L; omega) := by
      simp only [h]
    rw [hidx]
    exact hx'
  · rw [if_neg h]
    exact Nat.le_pred_of_lt (hx i)

/-- **Top-limb-aware per-position bound for the triple-product coefficient.** -/
lemma z2_coeff_leW {B tb m : ℕ} [NeZero m] (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (Z1 : Vector (Expression (F p)) (2 * m - 1))
    (k : Fin ((2 * m - 1) + m - 1)) (hm : 1 ≤ m) (htbB : tb ≤ B)
    (hZ1 : ∀ i : Fin (2 * m - 1),
      Expression.eval env Z1[i.val] = Expression.eval env (bigIntMulNoReduce a a)[i.val])
    (ha : ∀ i : Fin m, (Expression.eval env (a[i.val]'i.isLt)).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env (b[i.val]'i.isLt)).val < 2 ^ B)
    (ha_top : (Expression.eval env (a[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb)
    (hb_top : (Expression.eval env (b[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb)
    (hbound_aa : m * (2 ^ B * 2 ^ B) < p)
    (hfield : (3 * m) * (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) < p) :
    (Expression.eval env ((mulNoReduceX Z1 b)[k.val])).val ≤ triCapW B tb m k.val := by
  haveI : NeZero (2 * m - 1) := ⟨by omega⟩
  have ha_cap := limb_caps_of_top (B := B) (tw := tb) env a ha ha_top
  have hb_cap := limb_caps_of_top (B := B) (tw := tb) env b hb hb_top
  have hZ1le : ∀ i : Fin (2 * m - 1),
      (Expression.eval env (Z1[i.val]'i.isLt)).val ≤ sqCapW B tb m i.val := by
    intro i
    have hbridge : Expression.eval env (Z1[i.val]'i.isLt)
        = Expression.eval env ((bigIntMulNoReduce a a)[i.val]) := hZ1 i
    rw [hbridge]
    exact val_bigIntMulNoReduce_coeff_le_wconv env a a i (limbCap B tb m) (limbCap B tb m)
      ha ha ha_cap ha_cap hbound_aa
  have hk3 : k.val ≤ 3 * m - 3 := by have := k.isLt; omega
  have htrile : triCap m k.val ≤ (3 * m) * (3 * m) := by
    unfold triCap
    calc min ((k.val + 1) * (k.val + 2) / 2) _
        ≤ (k.val + 1) * (k.val + 2) / 2 := Nat.min_le_left _ _
      _ ≤ (k.val + 1) * (k.val + 2) := Nat.div_le_self _ _
      _ ≤ (3 * m) * (3 * m) := by
          have hk := k.isLt
          apply Nat.mul_le_mul <;> omega
  have hsum_lt : wconv (2 * m - 1) m (sqCapW B tb m) (limbCap B tb m) k.val < p := by
    have h1 : triCapW B tb m k.val
        ≤ triCap m k.val * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) :=
      triCapW_le_tri htbB hm k.val hk3
    calc wconv (2 * m - 1) m (sqCapW B tb m) (limbCap B tb m) k.val
        = triCapW B tb m k.val := rfl
      _ ≤ triCap m k.val * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) := h1
      _ ≤ (3 * m) * (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1) * (2 ^ B - 1)) :=
          Nat.mul_le_mul_right _ htrile
      _ < p := hfield
  exact val_mulNoReduceX_coeff_le_weighted2 env Z1 b k (sqCapW B tb m) (limbCap B tb m)
    hZ1le hb_cap hsum_lt

/-- **Top-limb-aware per-position bound for the `q·n` coefficient.** -/
lemma z3_coeff_leW {B tb tq m : ℕ} [NeZero m] (env : Environment (F p))
    (q : Vector (Expression (F p)) (2 * m)) (n : Var (BigInt m) (F p))
    (k : Fin ((2 * m) + m - 1)) (hm : 1 ≤ m) (htbB : tb ≤ B) (htqB : tq ≤ B)
    (hq : ∀ i : Fin (2 * m), (Expression.eval env (q[i.val]'i.isLt)).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env (n[i.val]'i.isLt)).val < 2 ^ B)
    (hq_top : (Expression.eval env (q[2 * m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tq)
    (hn_top : (Expression.eval env (n[m - 1]'(by have := Nat.pos_of_neZero m; omega))).val < 2 ^ tb)
    (hfield : (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1)) < p) :
    (Expression.eval env ((mulNoReduceX q n)[k.val])).val ≤ qnCapW B tb tq m k.val := by
  haveI : NeZero (2 * m) := ⟨by omega⟩
  have hq_cap := limb_caps_of_top (B := B) (tw := tq) env q hq hq_top
  have hn_cap := limb_caps_of_top (B := B) (tw := tb) env n hn hn_top
  have hsum_lt : wconv (2 * m) m (limbCap B tq (2 * m)) (limbCap B tb m) k.val < p := by
    have h1 : qnCapW B tb tq m k.val ≤ qnCap m k.val * ((2 ^ B - 1) * (2 ^ B - 1)) :=
      qnCapW_le_qn htbB htqB k.val
    have hcap : qnCap m k.val ≤ 3 * m := by
      unfold qnCap
      exact le_trans (Nat.min_le_right _ _) (le_trans (Nat.min_le_left _ _) (by omega))
    calc wconv (2 * m) m (limbCap B tq (2 * m)) (limbCap B tb m) k.val
        = qnCapW B tb tq m k.val := rfl
      _ ≤ qnCap m k.val * ((2 ^ B - 1) * (2 ^ B - 1)) := h1
      _ ≤ (3 * m) * ((2 ^ B - 1) * (2 ^ B - 1)) := Nat.mul_le_mul_right _ hcap
      _ < p := hfield
  exact val_mulNoReduceX_coeff_le_weighted2 env q n k (limbCap B tq (2 * m)) (limbCap B tb m)
    hq_cap hn_cap hsum_lt

/-- List-fold evaluator for `wconv` (kernel-reduction-friendly form for `decide`). -/
def wconvL (n₁ n₂ : ℕ) (t s : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((List.range n₁).map (fun i => if i ≤ k ∧ k - i < n₂ then t i * s (k - i) else 0)).sum

lemma wconv_eq_wconvL (n₁ n₂ : ℕ) (t s : ℕ → ℕ) (k : ℕ) :
    wconv n₁ n₂ t s k = wconvL n₁ n₂ t s k := by
  induction n₁ with
  | zero => rfl
  | succ n ih =>
    rw [wconv, Finset.sum_range_succ, show (∑ i ∈ range n,
        if i ≤ k ∧ k - i < n₂ then t i * s (k - i) else 0) = wconv n n₂ t s k from rfl,
      ih, wconvL, wconvL, List.range_succ, List.map_append, List.sum_append]
    simp

lemma sqCapW_eqL (B tb m : ℕ) : sqCapW B tb m = wconvL m m (limbCap B tb m) (limbCap B tb m) :=
  funext fun k => wconv_eq_wconvL m m _ _ k

lemma triCapW_eqL (B tb m : ℕ) (k : ℕ) :
    triCapW B tb m k = wconvL (2 * m - 1) m
      (wconvL m m (limbCap B tb m) (limbCap B tb m)) (limbCap B tb m) k := by
  rw [show triCapW B tb m k = wconv (2 * m - 1) m (sqCapW B tb m) (limbCap B tb m) k from rfl,
    wconv_eq_wconvL, sqCapW_eqL]

lemma qnCapW_eqL (B tb tq m : ℕ) (k : ℕ) :
    qnCapW B tb tq m k = wconvL (2 * m) m (limbCap B tq (2 * m)) (limbCap B tb m) k := by
  rw [show qnCapW B tb tq m k = wconv (2 * m) m (limbCap B tq (2 * m)) (limbCap B tb m) k from rfl,
    wconv_eq_wconvL]

/-- Top limb of a `bigIntMulNoReduce`-shaped value from a value bound (converse
of `value_lt_tight`): if `value < 2^((L−1)·B + tw)` then the top limb is
`< 2^tw`. -/
lemma top_lt_of_value_lt {B tw L : ℕ} [NeZero L] {x : BigInt L (F p)}
    (h : BigInt.value B x < 2 ^ ((L - 1) * B + tw)) :
    (x[L - 1]'(by have := Nat.pos_of_neZero L; omega)).val < 2 ^ tw := by
  have hL : 0 < L := Nat.pos_of_neZero L
  have hle : (x[L - 1]'(by omega)).val * 2 ^ (B * (L - 1)) ≤ BigInt.value B x := by
    rw [BigInt.value_eq_sum]
    exact Finset.single_le_sum
      (f := fun k : Fin L => (x[k]).val * 2 ^ (B * k.val))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨L - 1, by omega⟩)
  have hlt : (x[L - 1]'(by omega)).val * 2 ^ (B * (L - 1)) < 2 ^ tw * 2 ^ (B * (L - 1)) := by
    have hexp : (2 : ℕ) ^ ((L - 1) * B + tw) = 2 ^ tw * 2 ^ (B * (L - 1)) := by
      rw [← pow_add]
      ring_nf
    calc (x[L - 1]'(by omega)).val * 2 ^ (B * (L - 1))
        ≤ BigInt.value B x := hle
      _ < 2 ^ ((L - 1) * B + tw) := h
      _ = 2 ^ tw * 2 ^ (B * (L - 1)) := hexp
  exact Nat.lt_of_mul_lt_mul_right hlt

end Coeff

/-! ## Signed windows: ℤ-lift bridges for balanced-digit operands

For balanced-digit operands the limb evaluations are field images of *signed*
integers, so the convolution coefficients wrap mod `p` and the unsigned
`val`-based window lemmas above do not apply. These bridges express the
evaluated convolution coefficients as field images of the ℤ-convolution of the
signed digit families — with no size hypotheses at all — plus magnitude caps
from per-limb magnitude bounds (reusing `wconv` as the cap shape). -/

section SignedWindow
variable {p : ℕ} [Fact p.Prime]

open MulMod (mulNoReduceX eval_mulNoReduceX_coeff)

/-- ℤ-valued guarded convolution of signed digit families. -/
def zconv (n₁ n₂ : ℕ) (za zb : ℕ → ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then za i * zb (k - i) else 0

/-- Signed eval bridge for `bigIntMulNoReduce`: if each operand limb evaluates
to the field image of a signed integer, the `k`-th convolution coefficient
evaluates to the field image of the ℤ-convolution. No size hypotheses. -/
lemma eval_bigIntMulNoReduce_intCast {m : ℕ} [NeZero m] (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (za zb : ℕ → ℤ)
    (ha : ∀ i : Fin m, Expression.eval env (a[i.val]'i.isLt) = ((za i.val : ℤ) : F p))
    (hb : ∀ i : Fin m, Expression.eval env (b[i.val]'i.isLt) = ((zb i.val : ℤ) : F p))
    (k : Fin (2 * m - 1)) :
    Expression.eval env ((bigIntMulNoReduce a b)[k.val])
      = ((zconv m m za zb k.val : ℤ) : F p) := by
  rw [eval_bigIntMulNoReduce_coeff env a b k, zconv,
    ← Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ k.val ∧ k.val - i < m then za i * zb (k.val - i) else 0),
    Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < m
  · rw [dif_pos h, if_pos h, ha i, hb ⟨k.val - i.val, h.2⟩, Int.cast_mul]
  · rw [dif_neg h, if_neg h, Int.cast_zero]

/-- Signed eval bridge for the mixed-length `mulNoReduceX` (fused-step shape). -/
lemma eval_mulNoReduceX_intCast {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]
    (env : Environment (F p))
    (a : Vector (Expression (F p)) n₁) (b : Vector (Expression (F p)) n₂)
    (za zb : ℕ → ℤ)
    (ha : ∀ i : Fin n₁, Expression.eval env (a[i.val]'i.isLt) = ((za i.val : ℤ) : F p))
    (hb : ∀ i : Fin n₂, Expression.eval env (b[i.val]'i.isLt) = ((zb i.val : ℤ) : F p))
    (k : Fin (n₁ + n₂ - 1)) :
    Expression.eval env ((mulNoReduceX a b)[k.val])
      = ((zconv n₁ n₂ za zb k.val : ℤ) : F p) := by
  rw [eval_mulNoReduceX_coeff env a b k, zconv,
    ← Fin.sum_univ_eq_sum_range
      (fun i => if i ≤ k.val ∧ k.val - i < n₂ then za i * zb (k.val - i) else 0),
    Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i.val ≤ k.val ∧ k.val - i.val < n₂
  · rw [dif_pos h, if_pos h, ha i, hb ⟨k.val - i.val, h.2⟩, Int.cast_mul]
  · rw [dif_neg h, if_neg h, Int.cast_zero]

/-- Magnitude cap on the ℤ-convolution from per-limb magnitude caps: the
absolute value is bounded by the guarded window sum `wconv` of the caps. -/
lemma abs_zconv_le (n₁ n₂ : ℕ) (za zb : ℕ → ℤ) (Ma Mb : ℕ → ℕ)
    (ha : ∀ i, |za i| ≤ (Ma i : ℤ)) (hb : ∀ i, |zb i| ≤ (Mb i : ℤ)) (k : ℕ) :
    |zconv n₁ n₂ za zb k| ≤ (wconv n₁ n₂ Ma Mb k : ℤ) := by
  unfold zconv wconv
  push_cast
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : i ≤ k ∧ k - i < n₂
  · rw [if_pos h, if_pos h, abs_mul]
    exact mul_le_mul (ha i) (hb (k - i)) (abs_nonneg _)
      (le_trans (abs_nonneg _) (ha i))
  · rw [if_neg h, if_neg h, abs_zero]

/-- Nonnegativity of the ℤ-convolution of nonnegative digit families. -/
lemma zconv_nonneg (n₁ n₂ : ℕ) (za zb : ℕ → ℤ)
    (ha : ∀ i, 0 ≤ za i) (hb : ∀ i, 0 ≤ zb i) (k : ℕ) :
    0 ≤ zconv n₁ n₂ za zb k := by
  unfold zconv
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases h : i ≤ k ∧ k - i < n₂
  · rw [if_pos h]
    exact mul_nonneg (ha i) (hb (k - i))
  · rw [if_neg h]

/-- Position-dependent *balanced* limb magnitude cap: the top limb of an
`L`-limb balanced operand has magnitude `< 2^tw`, all lower (shifted) limbs
have magnitude `≤ 2^(B−1)`. -/
def balCap (B tw L j : ℕ) : ℕ := if j = L - 1 then 2 ^ tw - 1 else 2 ^ (B - 1)

/-- `wconv` only depends on the pointwise values of its cap functions. -/
lemma wconv_congr {n₁ n₂ : ℕ} {t t' s s' : ℕ → ℕ} (ht : ∀ i, t i = t' i)
    (hs : ∀ j, s j = s' j) (k : ℕ) : wconv n₁ n₂ t s k = wconv n₁ n₂ t' s' k := by
  unfold wconv
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, hs (k - i)]

/-- Beyond the top convolution index the guarded window sum is empty. -/
lemma wconv_eq_zero_of_ge {n₁ n₂ : ℕ} (t s : ℕ → ℕ) {k : ℕ} (hk : n₁ + n₂ - 1 ≤ k) :
    wconv n₁ n₂ t s k = 0 := by
  unfold wconv
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  rw [if_neg]
  rintro ⟨h1, h2⟩
  omega

end SignedWindow

end WindowCaps
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
