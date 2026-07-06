import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqD
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.WindowCaps

/-!
# Balanced-digit ℤ core (phase 2 of the balanced residue chain)

Environment-free arithmetic for the balanced signed-digit batteries, plus the
`GroupedEqD` interface bridges:

* **ℤ Cauchy product**: the base-`2^B` value of the ℤ-convolution `zconv`
  equals the product of the operands' ℤ values (`zconv_polyVal`) — the signed
  analogue of `polyValue_bigIntMulNoReduce`'s arithmetic core.
* **ℤ battery identity** (`zsquare_identity`): from the vanishing of the
  `GroupedEqD` difference polynomial for the quadratic battery shape
  (`lhs = zconv a a`, `rhs = zconv q n + r`-limbs), conclude
  `VZ(a)² = VZ(q)·VZ(n) + VZ(r)` over ℤ, and the mod-`n` congruence.
* **`GroupedEqD` bridges**: build `Assumptions` from per-coefficient ℤ eval
  bridges + windows, and convert `Spec`'s windowed-lift sum to/from the plain
  ℤ difference sum (`zsum_of_specD_evald` / `specD_sum_of_zsum_evald`).
* **Balanced digit machinery**: the balanced digits of a value `v` are the
  plain base-`2^B` digits of `v + balShift` (per-limb shift `2^(B−1)` below
  the top), so the existing decomposition witness generators apply verbatim.
  Provides the digit windows (`u_i < 2^B` shifted, top `< 2^tw` unshifted),
  the top bound from `v < 2^((m−1)B + tw − 1)`, and the ℤ value identity
  `Σ (u_i − 2^(B−1))·2^(B·i) + u_top·2^(B(m−1)) = v`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

namespace BalancedZ

/-! ## ℤ Cauchy product for the schoolbook convolution -/

/-- Per-`i` reindex for the ℤ Cauchy product (clone of `cauchy_inner_reindex`). -/
lemma cauchy_inner_reindexZ (B m : ℕ) (f g : ℕ → ℤ) (i : ℕ) (hi : i < m) :
    (∑ k ∈ Finset.range (2 * m - 1),
        if i ≤ k ∧ k - i < m then f i * g (k - i) * 2 ^ (B * k) else 0)
      = ∑ j ∈ Finset.range m, f i * g j * 2 ^ (B * (i + j)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (i := fun k => k - i) (j := fun j => i + j)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [show i + (k - i) = k by omega]

/-- Base-`2^B` Cauchy product over ℤ (clone of `cauchy_base_pow`). -/
lemma cauchy_base_powZ (B m : ℕ) (f g : ℕ → ℤ) :
    (∑ i ∈ Finset.range m, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range m, g j * 2 ^ (B * j))
      = ∑ k ∈ Finset.range (2 * m - 1),
          (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
            * 2 ^ (B * k) := by
  rw [Finset.sum_mul_sum]
  have hrhs : (∑ k ∈ Finset.range (2 * m - 1),
        (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
          * 2 ^ (B * k))
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m, f i * g j * 2 ^ (B * (i + j)) := by
    have hstep : (∑ k ∈ Finset.range (2 * m - 1),
          (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < m then f i * g (k - i) else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range (2 * m - 1), ∑ i ∈ Finset.range m,
            if i ≤ k ∧ k - i < m then f i * g (k - i) * 2 ^ (B * k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_mul, zero_mul]
    rw [hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cauchy_inner_reindexZ B m f g i hi]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show B * (i + j) = B * i + B * j by ring, pow_add]
  ring

/-- The base-`2^B` ℤ value of the signed convolution `zconv` is the product of
the operands' ℤ values. -/
lemma zconv_polyVal (B m : ℕ) (f g : ℕ → ℤ) :
    (∑ k ∈ Finset.range (2 * m - 1), WindowCaps.zconv m m f g k * 2 ^ (B * k))
      = (∑ i ∈ Finset.range m, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range m, g j * 2 ^ (B * j)) := by
  rw [cauchy_base_powZ B m f g]
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- A low-limb-guarded sum collapses to the low range. -/
lemma guarded_low_sum (B m M : ℕ) (hmM : m ≤ M) (zr : ℕ → ℤ) :
    (∑ k ∈ Finset.range M, (if k < m then zr k else 0) * 2 ^ (B * k))
      = ∑ k ∈ Finset.range m, zr k * 2 ^ (B * k) := by
  rw [← Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmM))
    (fun x _ hx => by
      rw [if_neg (by simp only [Finset.mem_range, not_lt] at hx; omega), zero_mul])]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [if_pos hk]

/-! ## The ℤ battery identity -/

/-- **The ℤ core of the balanced quadratic battery**: if the `GroupedEqD`
difference polynomial for the shape `lhs = zconv a a`,
`rhs = zconv q n + r`-limbs vanishes, then `VZ(a)² = VZ(q)·VZ(n) + VZ(r)`
over ℤ. -/
lemma zsquare_identity (B m : ℕ) (hm : 1 ≤ m) (za zq zn zr : ℕ → ℤ)
    (hsum : (∑ k ∈ Finset.range (2 * m - 1),
        (WindowCaps.zconv m m za za k
          - (WindowCaps.zconv m m zq zn k + (if k < m then zr k else 0))) * 2 ^ (B * k)) = 0) :
    (∑ i ∈ Finset.range m, za i * 2 ^ (B * i)) * (∑ i ∈ Finset.range m, za i * 2 ^ (B * i))
      = (∑ i ∈ Finset.range m, zq i * 2 ^ (B * i)) * (∑ i ∈ Finset.range m, zn i * 2 ^ (B * i))
        + ∑ i ∈ Finset.range m, zr i * 2 ^ (B * i) := by
  have hsplit : (∑ k ∈ Finset.range (2 * m - 1),
        (WindowCaps.zconv m m za za k
          - (WindowCaps.zconv m m zq zn k + (if k < m then zr k else 0))) * 2 ^ (B * k))
      = (∑ k ∈ Finset.range (2 * m - 1), WindowCaps.zconv m m za za k * 2 ^ (B * k))
        - ((∑ k ∈ Finset.range (2 * m - 1), WindowCaps.zconv m m zq zn k * 2 ^ (B * k))
          + (∑ k ∈ Finset.range (2 * m - 1), (if k < m then zr k else 0) * 2 ^ (B * k))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit, guarded_low_sum B m (2 * m - 1) (by omega) zr,
    zconv_polyVal B m za za, zconv_polyVal B m zq zn] at hsum
  linarith

/-- Congruence packaging: `A·A = Q·N + R` gives `R ≡ A·A (mod N)` over ℤ. -/
lemma modEq_of_identity {A Q N R : ℤ} (h : A * A = Q * N + R) :
    R ≡ A * A [ZMOD N] := by
  have hd : N ∣ A * A - R := ⟨Q, by linarith⟩
  exact Int.modEq_iff_dvd.mpr hd

/-! ## `GroupedEqD` interface bridges -/

section Bridges
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

open GroupedEqX (CoeffsX)

/-- Per-coefficient windowed-lift identification: with eval bridges to ℤ digit
families and difference windows, the `zsval` reading of each evaluated
coefficient difference is the ℤ difference. -/
lemma zsval_diff_eq (NfP NfN : ℕ → ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) (zl zr : ℕ → ℤ)
    (hL : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (lhs[k]'hk) = ((zl k : ℤ) : F p))
    (hR : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (rhs[k]'hk) = ((zr k : ℤ) : F p))
    (hlo : ∀ k, k < L → -(NfN k : ℤ) < zl k - zr k)
    (hhi : ∀ k, k < L → zl k - zr k < (NfP k : ℤ))
    (hNfp : ∀ k, k < L → NfP k + NfN k ≤ p)
    (k : ℕ) (hk : k < L) :
    GroupedEqD.zsval (NfP k)
        (Expression.eval env (lhs[k]'hk) - Expression.eval env (rhs[k]'hk))
      = zl k - zr k := by
  refine GroupedEqD.zsval_eq_of_window ?_ (hlo k hk) (hhi k hk) (hNfp k hk)
  rw [hL k hk, hR k hk]
  push_cast
  ring

/-- Build `GroupedEqD.Assumptions`-shaped facts from per-coefficient ℤ eval
bridges and difference windows. -/
lemma assumptionsD_evald (NfP NfN : ℕ → ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) (zl zr : ℕ → ℤ)
    (hL : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (lhs[k]'hk) = ((zl k : ℤ) : F p))
    (hR : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (rhs[k]'hk) = ((zr k : ℤ) : F p))
    (hlo : ∀ k, k < L → -(NfN k : ℤ) < zl k - zr k)
    (hhi : ∀ k, k < L → zl k - zr k < (NfP k : ℤ)) :
    ∀ k : Fin L, ∃ z : ℤ,
      ((z : ℤ) : F p)
          = Expression.eval env (lhs[k.val]'k.isLt)
            - Expression.eval env (rhs[k.val]'k.isLt) ∧
      -(NfN k.val : ℤ) < z ∧ z < (NfP k.val : ℤ) := by
  intro k
  refine ⟨zl k.val - zr k.val, ?_, hlo k.val k.isLt, hhi k.val k.isLt⟩
  rw [hL k.val k.isLt, hR k.val k.isLt]
  push_cast
  ring

/-- Extract the plain ℤ difference sum from the `GroupedEqD.Spec` windowed-lift
sum (soundness direction). -/
lemma zsum_of_specD_evald (B : ℕ) (NfP NfN : ℕ → ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) (zl zr : ℕ → ℤ)
    (hL : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (lhs[k]'hk) = ((zl k : ℤ) : F p))
    (hR : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (rhs[k]'hk) = ((zr k : ℤ) : F p))
    (hlo : ∀ k, k < L → -(NfN k : ℤ) < zl k - zr k)
    (hhi : ∀ k, k < L → zl k - zr k < (NfP k : ℤ))
    (hNfp : ∀ k, k < L → NfP k + NfN k ≤ p)
    (hspec : (∑ k : Fin L,
        GroupedEqD.zsval (NfP k.val)
          (Expression.eval env (lhs[k.val]'k.isLt)
            - Expression.eval env (rhs[k.val]'k.isLt)) * 2 ^ (B * k.val)) = 0) :
    (∑ k ∈ Finset.range L, (zl k - zr k) * 2 ^ (B * k)) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (zl k - zr k) * 2 ^ (B * k)), ← hspec]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsval_diff_eq NfP NfN env lhs rhs zl zr hL hR hlo hhi hNfp k.val k.isLt]

/-- Produce the `GroupedEqD.Spec` windowed-lift sum from the plain ℤ difference
sum (completeness direction). -/
lemma specD_sum_of_zsum_evald (B : ℕ) (NfP NfN : ℕ → ℕ) (env : Environment (F p))
    (lhs rhs : Var (CoeffsX L) (F p)) (zl zr : ℕ → ℤ)
    (hL : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (lhs[k]'hk) = ((zl k : ℤ) : F p))
    (hR : ∀ (k : ℕ) (hk : k < L),
      Expression.eval env (rhs[k]'hk) = ((zr k : ℤ) : F p))
    (hlo : ∀ k, k < L → -(NfN k : ℤ) < zl k - zr k)
    (hhi : ∀ k, k < L → zl k - zr k < (NfP k : ℤ))
    (hNfp : ∀ k, k < L → NfP k + NfN k ≤ p)
    (hzero : (∑ k ∈ Finset.range L, (zl k - zr k) * 2 ^ (B * k)) = 0) :
    (∑ k : Fin L,
        GroupedEqD.zsval (NfP k.val)
          (Expression.eval env (lhs[k.val]'k.isLt)
            - Expression.eval env (rhs[k.val]'k.isLt)) * 2 ^ (B * k.val)) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (zl k - zr k) * 2 ^ (B * k))] at hzero
  rw [← hzero]
  apply Finset.sum_congr rfl
  intro k _
  rw [zsval_diff_eq NfP NfN env lhs rhs zl zr hL hR hlo hhi hNfp k.val k.isLt]

end Bridges

/-! ## Balanced digit machinery

The balanced digits of `v` are the plain base-`2^B` digits of
`N := v + balShift B m`: subtracting the constant shift `2^(B−1)` from every
digit below the top recovers exactly `v` over ℤ, the digit range checks are
the usual `< 2^B` (plus `< 2^tw` at the top), and the honest windows are
`d_i ∈ [−2^(B−1), 2^(B−1) − 1]`, `d_top ∈ [0, 2^tw)`. -/

/-- The balanced shift value: `2^(B−1)` in every limb below the top. -/
def balShift (B m : ℕ) : ℕ := ∑ i ∈ Finset.range (m - 1), 2 ^ (B - 1) * 2 ^ (B * i)

/-- The `i`-th balanced digit witness of `v`: the plain base-`2^B` digit of
`v + balShift B m`. -/
def balDigit (B m v i : ℕ) : ℕ := (v + balShift B m) / 2 ^ (B * i) % 2 ^ B

private lemma shift_sum_lt (B : ℕ) (hB : 1 ≤ B) :
    ∀ t : ℕ, (∑ i ∈ Finset.range t, 2 ^ (B - 1) * 2 ^ (B * i)) < 2 ^ (B * t) := by
  intro t
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : (2 : ℕ) ^ (B * (n + 1)) = 2 ^ (B * n) * 2 ^ B := by
      rw [Nat.mul_add, Nat.mul_one, pow_add]
    have h2 : (2 : ℕ) ^ (B - 1) * 2 ^ (B * n) + 2 ^ (B * n) ≤ 2 ^ (B * n) * 2 ^ B := by
      have h3 : (2 : ℕ) ^ (B - 1) + 1 ≤ 2 ^ B := by
        have h4 : (2 : ℕ) ^ B = 2 ^ (B - 1) * 2 := by
          rw [← pow_succ]
          congr 1
          omega
        have h5 : (1 : ℕ) ≤ 2 ^ (B - 1) := Nat.one_le_two_pow
        omega
      calc (2 : ℕ) ^ (B - 1) * 2 ^ (B * n) + 2 ^ (B * n)
          = (2 ^ (B - 1) + 1) * 2 ^ (B * n) := by ring
        _ ≤ 2 ^ B * 2 ^ (B * n) := Nat.mul_le_mul_right _ h3
        _ = 2 ^ (B * n) * 2 ^ B := by ring
    omega

/-- The shift value fits below the top limb. -/
lemma balShift_lt (B m : ℕ) (hB : 1 ≤ B) : balShift B m < 2 ^ (B * (m - 1)) :=
  shift_sum_lt B hB (m - 1)

/-- The shifted value fits `m` limbs with a `tw`-bit top:
`v < 2^((m−1)B + tw − 1)` gives `v + balShift < 2^((m−1)B + tw)`. -/
lemma add_balShift_lt (B m tw v : ℕ) (hB : 1 ≤ B) (htw : 1 ≤ tw)
    (hv : v < 2 ^ ((m - 1) * B + tw - 1)) :
    v + balShift B m < 2 ^ ((m - 1) * B + tw) := by
  have h1 := balShift_lt B m hB
  have h2 : (2 : ℕ) ^ ((m - 1) * B + tw - 1) = 2 ^ (B * (m - 1)) * 2 ^ (tw - 1) := by
    rw [← pow_add]
    congr 1
    have : (m - 1) * B = B * (m - 1) := Nat.mul_comm _ _
    omega
  have h3 : (2 : ℕ) ^ ((m - 1) * B + tw) = 2 ^ (B * (m - 1)) * 2 ^ tw := by
    rw [← pow_add]
    congr 1
    have : (m - 1) * B = B * (m - 1) := Nat.mul_comm _ _
    omega
  have h4 : (2 : ℕ) ^ tw = 2 ^ (tw - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have h5 : (1 : ℕ) ≤ 2 ^ (tw - 1) := Nat.one_le_two_pow
  have h6 : (1 : ℕ) ≤ 2 ^ (B * (m - 1)) := Nat.one_le_two_pow
  rw [h2] at hv
  rw [h3, h4]
  nlinarith

/-- Every balanced digit is a `B`-bit word. -/
lemma balDigit_lt (B m v i : ℕ) : balDigit B m v i < 2 ^ B :=
  Nat.mod_lt _ (Nat.two_pow_pos B)

/-- The top balanced digit is a `tw`-bit word. -/
lemma balDigit_top_lt (B m tw v : ℕ) (hB : 1 ≤ B) (htw : 1 ≤ tw)
    (hv : v < 2 ^ ((m - 1) * B + tw - 1)) :
    balDigit B m v (m - 1) < 2 ^ tw := by
  have hN := add_balShift_lt B m tw v hB htw hv
  have h1 : (v + balShift B m) / 2 ^ (B * (m - 1)) < 2 ^ tw := by
    apply Nat.div_lt_of_lt_mul
    calc v + balShift B m < 2 ^ ((m - 1) * B + tw) := hN
      _ = 2 ^ (B * (m - 1)) * 2 ^ tw := by
          rw [← pow_add]
          congr 1
          have : (m - 1) * B = B * (m - 1) := Nat.mul_comm _ _
          omega
  exact lt_of_le_of_lt (Nat.mod_le _ _) h1

/-- Base-`2^B` digit recomposition: the digits of `N < 2^(B·m)` sum back to `N`. -/
lemma digits_sum (B : ℕ) : ∀ (m N : ℕ), N < 2 ^ (B * m) →
    (∑ i ∈ Finset.range m, (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i)) = N := by
  intro m
  induction m with
  | zero =>
    intro N hN
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at hN
    simp [hN]
  | succ n ih =>
    intro N hN
    rw [Finset.sum_range_succ']
    have hterm : ∀ i, (N / 2 ^ (B * (i + 1)) % 2 ^ B) * 2 ^ (B * (i + 1))
        = (((N / 2 ^ B) / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i)) * 2 ^ B := by
      intro i
      have hd : N / 2 ^ (B * (i + 1)) = (N / 2 ^ B) / 2 ^ (B * i) := by
        rw [Nat.div_div_eq_div_mul, show B * (i + 1) = B + B * i from by ring, pow_add]
      have hp : (2 : ℕ) ^ (B * (i + 1)) = 2 ^ (B * i) * 2 ^ B := by
        rw [show B * (i + 1) = B * i + B from by ring, pow_add]
      rw [hd, hp]
      ring
    rw [show (∑ i ∈ Finset.range n, (N / 2 ^ (B * (i + 1)) % 2 ^ B) * 2 ^ (B * (i + 1)))
        = (∑ i ∈ Finset.range n, ((N / 2 ^ B) / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i)) * 2 ^ B from by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => hterm i]
    have hdivN : N / 2 ^ B < 2 ^ (B * n) := by
      apply Nat.div_lt_of_lt_mul
      calc N < 2 ^ (B * (n + 1)) := hN
        _ = 2 ^ B * 2 ^ (B * n) := by
            rw [← pow_add]
            congr 1
            ring
    rw [ih (N / 2 ^ B) hdivN]
    simp only [Nat.mul_zero, pow_zero, mul_one, Nat.div_one]
    have h := Nat.mod_add_div' N (2 ^ B)
    omega

/-- **The balanced value identity**: subtracting the per-limb shift `2^(B−1)`
below the top recovers `v` from its balanced digits, over ℤ. -/
lemma balanced_value (B m tw v : ℕ) (hB : 1 ≤ B) (hm : 1 ≤ m) (htw : 1 ≤ tw)
    (htwB : tw ≤ B) (hv : v < 2 ^ ((m - 1) * B + tw - 1)) :
    (∑ i ∈ Finset.range (m - 1),
        ((balDigit B m v i : ℤ) - 2 ^ (B - 1)) * 2 ^ (B * i))
      + (balDigit B m v (m - 1) : ℤ) * 2 ^ (B * (m - 1)) = (v : ℤ) := by
  set N := v + balShift B m with hN
  have hNlt : N < 2 ^ (B * m) := by
    have h1 := add_balShift_lt B m tw v hB htw hv
    have hcomm : (m - 1) * B = B * (m - 1) := Nat.mul_comm _ _
    have hBm : B * m = B * (m - 1) + B := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      ring
    calc N < 2 ^ ((m - 1) * B + tw) := h1
      _ ≤ 2 ^ (B * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum := digits_sum B m N hNlt
  -- split the top digit off the ℕ recomposition
  have hsplit : (∑ i ∈ Finset.range (m - 1), (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i))
      + (N / 2 ^ (B * (m - 1)) % 2 ^ B) * 2 ^ (B * (m - 1)) = N := by
    have h2 : (∑ i ∈ Finset.range ((m - 1) + 1), (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i))
        = (∑ i ∈ Finset.range (m - 1), (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i))
          + (N / 2 ^ (B * (m - 1)) % 2 ^ B) * 2 ^ (B * (m - 1)) := Finset.sum_range_succ _ _
    rw [← h2, show (m - 1) + 1 = m from by omega]
    exact hsum
  -- cast and rearrange: the lhs of the goal is (ℕ digit sum) − balShift
  have hcast : (∑ i ∈ Finset.range (m - 1),
        ((balDigit B m v i : ℤ) - 2 ^ (B - 1)) * 2 ^ (B * i))
      = ((∑ i ∈ Finset.range (m - 1), (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i) : ℕ) : ℤ)
        - ((balShift B m : ℕ) : ℤ) := by
    rw [balShift]
    push_cast
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [balDigit, ← hN]
    push_cast
    ring
  rw [hcast]
  have htop : (balDigit B m v (m - 1) : ℤ)
      = ((N / 2 ^ (B * (m - 1)) % 2 ^ B : ℕ) : ℤ) := by
    rw [balDigit, ← hN]
  rw [htop]
  have hZ : ((∑ i ∈ Finset.range (m - 1), (N / 2 ^ (B * i) % 2 ^ B) * 2 ^ (B * i) : ℕ) : ℤ)
      + ((N / 2 ^ (B * (m - 1)) % 2 ^ B : ℕ) : ℤ) * ((2 : ℤ) ^ (B * (m - 1)))
      = (N : ℤ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hsplit
  have hNv : (N : ℤ) = (v : ℤ) + (balShift B m : ℤ) := by
    rw [hN]
    push_cast
    ring
  linarith

/-- Honest digit window (below the top): the shifted digit lies in
`[−2^(B−1), 2^(B−1) − 1]`, i.e. its magnitude is at most `2^(B−1)`. -/
lemma abs_balDigit_shift_le (B m v i : ℕ) (hB : 1 ≤ B) :
    |(balDigit B m v i : ℤ) - 2 ^ (B - 1)| ≤ 2 ^ (B - 1) := by
  have h1 := balDigit_lt B m v i
  have h2 : (2 : ℕ) ^ B = 2 ^ (B - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [abs_le]
  constructor
  · have : (0 : ℤ) ≤ (balDigit B m v i : ℤ) := by positivity
    omega
  · have h3 : (balDigit B m v i : ℤ) < ((2 ^ (B - 1) * 2 : ℕ) : ℤ) := by
      exact_mod_cast h2 ▸ h1
    push_cast at h3
    omega

/-- Generic soundness-side window: any range-checked shifted digit
(`u < 2·S`) has magnitude at most `S` after the shift. -/
lemma abs_shift_le_of_lt {u S : ℕ} (hu : u < 2 * S) : |(u : ℤ) - S| ≤ S := by
  rw [abs_le]
  have : (0 : ℤ) ≤ (u : ℤ) := by positivity
  have : (u : ℤ) < 2 * S := by exact_mod_cast hu
  omega

/-- Honest top-digit window: magnitude at most `2^tw − 1` (nonnegative). -/
lemma abs_balDigit_top_le (B m tw v : ℕ) (hB : 1 ≤ B) (htw : 1 ≤ tw)
    (hv : v < 2 ^ ((m - 1) * B + tw - 1)) :
    |(balDigit B m v (m - 1) : ℤ)| ≤ 2 ^ tw - 1 := by
  have h1 := balDigit_top_lt B m tw v hB htw hv
  rw [abs_le]
  have h2 : (balDigit B m v (m - 1) : ℤ) < ((2 ^ tw : ℕ) : ℤ) := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ (balDigit B m v (m - 1) : ℤ) := by positivity
  have h4 : ((2 ^ tw : ℕ) : ℤ) = (2 : ℤ) ^ tw := by push_cast; ring
  omega

/-! ## Phase 3: balanced value reading, digit families, mixed ℤ Cauchy product -/

section Phase3
variable {p : ℕ} [Fact p.Prime] {m : ℕ}

/-- The balanced ℤ reading of a limb vector: its unsigned positional value
minus the balanced shift. -/
def VZ (B : ℕ) (x : BigInt m (F p)) : ℤ :=
  (BigInt.value B x : ℤ) - (balShift B m : ℤ)

/-- The *signed* digit family of a limb vector: shift `2^(B−1)` off every limb
below the top, zero beyond the top. -/
def zdigits (B : ℕ) (x : BigInt m (F p)) (i : ℕ) : ℤ :=
  if h : i < m then
    (if i = m - 1 then ((x[i]'h).val : ℤ) else ((x[i]'h).val : ℤ) - 2 ^ (B - 1))
  else 0

/-- The *unsigned* digit family (ℤ casts of the limb values, zero beyond). -/
def udigits (x : BigInt m (F p)) (i : ℕ) : ℤ :=
  if h : i < m then ((x[i]'h).val : ℤ) else 0

lemma udigits_nonneg (x : BigInt m (F p)) (i : ℕ) : 0 ≤ udigits x i := by
  unfold udigits
  split
  · positivity
  · exact le_refl 0

/-- `BigInt.value` as a ℤ positional sum over `Finset.range m` of `udigits`. -/
lemma sum_udigits (B : ℕ) (x : BigInt m (F p)) :
    (∑ i ∈ Finset.range m, udigits x i * 2 ^ (B * i)) = (BigInt.value B x : ℤ) := by
  rw [BigInt.value_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => udigits x i * 2 ^ (B * i))]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [udigits, dif_pos i.isLt]
  simp only [Fin.getElem_fin]

/-- The signed digit family sums to the balanced reading `VZ`. -/
lemma sum_zdigits (B : ℕ) (hm : 1 ≤ m) (x : BigInt m (F p)) :
    (∑ i ∈ Finset.range m, zdigits B x i * 2 ^ (B * i)) = VZ B x := by
  have hsplit : ∀ i ∈ Finset.range m,
      zdigits B x i * 2 ^ (B * i)
        = udigits x i * 2 ^ (B * i)
          - (if i = m - 1 then 0 else (2 : ℤ) ^ (B - 1)) * 2 ^ (B * i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [zdigits, udigits, dif_pos hi, dif_pos hi]
    by_cases h : i = m - 1
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, sum_udigits B x]
  have hshift : (∑ i ∈ Finset.range m,
      (if i = m - 1 then 0 else (2 : ℤ) ^ (B - 1)) * 2 ^ (B * i))
        = (balShift B m : ℤ) := by
    have hsucc : (∑ i ∈ Finset.range ((m - 1) + 1),
        (if i = m - 1 then 0 else (2 : ℤ) ^ (B - 1)) * 2 ^ (B * i))
          = (∑ i ∈ Finset.range (m - 1),
              (if i = m - 1 then 0 else (2 : ℤ) ^ (B - 1)) * 2 ^ (B * i))
            + (if m - 1 = m - 1 then 0 else (2 : ℤ) ^ (B - 1)) * 2 ^ (B * (m - 1)) :=
      Finset.sum_range_succ _ _
    rw [show (m - 1) + 1 = m from by omega] at hsucc
    rw [hsucc, if_pos rfl, zero_mul, add_zero, balShift]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_neg (by omega)]
  rw [hshift, VZ]

/-- Magnitude cap for the signed digit family from per-limb windows. -/
lemma abs_zdigits_le {B tw : ℕ} (hB : 1 ≤ B) (hm : 1 ≤ m) (x : BigInt m (F p))
    (hnorm : x.Normalized B)
    (htop : (x[m - 1]'(by omega)).val < 2 ^ tw) (i : ℕ) :
    |zdigits B x i| ≤ (WindowCaps.balCap B tw m i : ℤ) := by
  unfold zdigits WindowCaps.balCap
  by_cases h : i < m
  · rw [dif_pos h]
    by_cases htopi : i = m - 1
    · rw [if_pos htopi, if_pos htopi]
      have hv : (x[i]'h).val < 2 ^ tw := by
        subst htopi
        exact htop
      have hle : (x[i]'h).val ≤ 2 ^ tw - 1 := by omega
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((x[i]'h).val : ℤ))]
      exact_mod_cast hle
    · rw [if_neg htopi, if_neg htopi]
      have hv : (x[i]'h).val < 2 * 2 ^ (B - 1) := by
        have h1 : (x[i]'h).val < 2 ^ B := hnorm ⟨i, h⟩
        have h2 : (2 : ℕ) ^ B = 2 * 2 ^ (B - 1) := by
          conv_lhs => rw [show B = (B - 1) + 1 from by omega]
          rw [pow_succ]
          ring
        omega
      have := abs_shift_le_of_lt (u := (x[i]'h).val) (S := 2 ^ (B - 1)) hv
      push_cast at this ⊢
      exact this
  · rw [dif_neg h]
    simp only [abs_zero]
    split
    · exact Int.natCast_nonneg _
    · exact Int.natCast_nonneg _

/-- Cap for the unsigned digit family from per-limb windows (`limbCap` shape). -/
lemma abs_udigits_le_limbCap {B tw : ℕ} (hm : 1 ≤ m) (x : BigInt m (F p))
    (hnorm : x.Normalized B)
    (htop : (x[m - 1]'(by omega)).val < 2 ^ tw) (i : ℕ) :
    |udigits x i| ≤ (WindowCaps.limbCap B tw m i : ℤ) := by
  unfold udigits WindowCaps.limbCap
  by_cases h : i < m
  · rw [dif_pos h, abs_of_nonneg (by positivity)]
    by_cases htopi : i = m - 1
    · rw [if_pos htopi]
      have hv : (x[i]'h).val < 2 ^ tw := by
        subst htopi
        exact htop
      have hle : (x[i]'h).val ≤ 2 ^ tw - 1 := by omega
      exact_mod_cast hle
    · rw [if_neg htopi]
      have h1 : (x[i]'h).val < 2 ^ B := hnorm ⟨i, h⟩
      have hle : (x[i]'h).val ≤ 2 ^ B - 1 := by omega
      exact_mod_cast hle
  · rw [dif_neg h]
    simp only [abs_zero]
    split
    · exact Int.natCast_nonneg _
    · exact Int.natCast_nonneg _

end Phase3

/-! ## Mixed-length ℤ Cauchy product -/

/-- Per-`i` reindex for the mixed ℤ Cauchy product. -/
lemma cauchy_inner_reindexZX (B n₁ n₂ : ℕ) (f g : ℕ → ℤ) (i : ℕ) (hi : i < n₁) :
    (∑ k ∈ Finset.range (n₁ + n₂ - 1),
        if i ≤ k ∧ k - i < n₂ then f i * g (k - i) * 2 ^ (B * k) else 0)
      = ∑ j ∈ Finset.range n₂, f i * g j * 2 ^ (B * (i + j)) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (i := fun k => k - i) (j := fun j => i + j)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    rw [show i + (k - i) = k by omega]

/-- Base-`2^B` mixed Cauchy product over ℤ. -/
lemma cauchy_base_powZX (B n₁ n₂ : ℕ) (f g : ℕ → ℤ) :
    (∑ i ∈ Finset.range n₁, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range n₂, g j * 2 ^ (B * j))
      = ∑ k ∈ Finset.range (n₁ + n₂ - 1),
          (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then f i * g (k - i) else 0)
            * 2 ^ (B * k) := by
  rw [Finset.sum_mul_sum]
  have hrhs : (∑ k ∈ Finset.range (n₁ + n₂ - 1),
        (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then f i * g (k - i) else 0)
          * 2 ^ (B * k))
      = ∑ i ∈ Finset.range n₁, ∑ j ∈ Finset.range n₂, f i * g j * 2 ^ (B * (i + j)) := by
    have hstep : (∑ k ∈ Finset.range (n₁ + n₂ - 1),
          (∑ i ∈ Finset.range n₁, if i ≤ k ∧ k - i < n₂ then f i * g (k - i) else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range (n₁ + n₂ - 1), ∑ i ∈ Finset.range n₁,
            if i ≤ k ∧ k - i < n₂ then f i * g (k - i) * 2 ^ (B * k) else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [ite_mul, zero_mul]
    rw [hstep, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [cauchy_inner_reindexZX B n₁ n₂ f g i hi]
  rw [hrhs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show B * (i + j) = B * i + B * j by ring, pow_add]
  ring

/-- The base-`2^B` ℤ value of the mixed signed convolution is the product of
the operands' ℤ values. -/
lemma zconv_polyVal_mixed (B n₁ n₂ : ℕ) (f g : ℕ → ℤ) :
    (∑ k ∈ Finset.range (n₁ + n₂ - 1), WindowCaps.zconv n₁ n₂ f g k * 2 ^ (B * k))
      = (∑ i ∈ Finset.range n₁, f i * 2 ^ (B * i))
        * (∑ j ∈ Finset.range n₂, g j * 2 ^ (B * j)) := by
  rw [cauchy_base_powZX B n₁ n₂ f g]
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-! ## Difference-sum splits for the battery / fused shapes -/

/-- **Quadratic difference-sum split**: the base-`2^B` value of the
per-coefficient difference `zconv a a − (zconv q n + r-limbs)` is
`VZ(a)² − (VZ(q)·VZ(n) + VZ(r))` over ℤ. Both soundness (sum = 0 ⟹ identity)
and completeness (identity ⟹ sum = 0) read off this equality. -/
lemma zsquare_sum_split (B m : ℕ) (hm : 1 ≤ m) (za zq zn zr : ℕ → ℤ) :
    (∑ k ∈ Finset.range (2 * m - 1),
        (WindowCaps.zconv m m za za k
          - (WindowCaps.zconv m m zq zn k + (if k < m then zr k else 0))) * 2 ^ (B * k))
      = (∑ i ∈ Finset.range m, za i * 2 ^ (B * i))
          * (∑ i ∈ Finset.range m, za i * 2 ^ (B * i))
        - ((∑ i ∈ Finset.range m, zq i * 2 ^ (B * i))
            * (∑ i ∈ Finset.range m, zn i * 2 ^ (B * i))
          + ∑ i ∈ Finset.range m, zr i * 2 ^ (B * i)) := by
  have hsplit : (∑ k ∈ Finset.range (2 * m - 1),
        (WindowCaps.zconv m m za za k
          - (WindowCaps.zconv m m zq zn k + (if k < m then zr k else 0))) * 2 ^ (B * k))
      = (∑ k ∈ Finset.range (2 * m - 1), WindowCaps.zconv m m za za k * 2 ^ (B * k))
        - ((∑ k ∈ Finset.range (2 * m - 1), WindowCaps.zconv m m zq zn k * 2 ^ (B * k))
          + (∑ k ∈ Finset.range (2 * m - 1), (if k < m then zr k else 0) * 2 ^ (B * k))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit, guarded_low_sum B m (2 * m - 1) (by omega) zr,
    zconv_polyVal B m za za, zconv_polyVal B m zq zn]

/-- **Fused (triple-product) difference-sum split**: with `z1` a `2m−1`-long
family and `zb`, `zq` (`2m`-long), `zn`, `zem` digit families, the base-`2^B`
value of the padded per-coefficient difference is
`(Σz1)·(Σzb) − ((Σzq)·(Σzn) + Σzem)` over ℤ. -/
lemma ztriple_sum_split (B m : ℕ) (hm : 1 ≤ m) (z1 zb zq zn zem : ℕ → ℤ) :
    (∑ k ∈ Finset.range (2 * m + m - 1),
        ((if k < (2 * m - 1) + m - 1 then WindowCaps.zconv (2 * m - 1) m z1 zb k else 0)
          - (WindowCaps.zconv (2 * m) m zq zn k + (if k < m then zem k else 0)))
          * 2 ^ (B * k))
      = (∑ j ∈ Finset.range (2 * m - 1), z1 j * 2 ^ (B * j))
          * (∑ j ∈ Finset.range m, zb j * 2 ^ (B * j))
        - ((∑ i ∈ Finset.range (2 * m), zq i * 2 ^ (B * i))
            * (∑ j ∈ Finset.range m, zn j * 2 ^ (B * j))
          + ∑ i ∈ Finset.range m, zem i * 2 ^ (B * i)) := by
  have hsplit : (∑ k ∈ Finset.range (2 * m + m - 1),
        ((if k < (2 * m - 1) + m - 1 then WindowCaps.zconv (2 * m - 1) m z1 zb k else 0)
          - (WindowCaps.zconv (2 * m) m zq zn k + (if k < m then zem k else 0)))
          * 2 ^ (B * k))
      = (∑ k ∈ Finset.range (2 * m + m - 1),
          (if k < (2 * m - 1) + m - 1 then WindowCaps.zconv (2 * m - 1) m z1 zb k else 0)
            * 2 ^ (B * k))
        - ((∑ k ∈ Finset.range (2 * m + m - 1),
            WindowCaps.zconv (2 * m) m zq zn k * 2 ^ (B * k))
          + (∑ k ∈ Finset.range (2 * m + m - 1), (if k < m then zem k else 0) * 2 ^ (B * k))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsplit,
    guarded_low_sum B ((2 * m - 1) + m - 1) (2 * m + m - 1) (by omega)
      (WindowCaps.zconv (2 * m - 1) m z1 zb),
    guarded_low_sum B m (2 * m + m - 1) (by omega) zem,
    show (2 * m + m - 1) = (2 * m) + m - 1 from by omega,
    zconv_polyVal_mixed B (2 * m) m zq zn,
    show (2 * m - 1) + m - 1 = (2 * m - 1) + m - 1 from rfl,
    zconv_polyVal_mixed B (2 * m - 1) m z1 zb]

end BalancedZ

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
