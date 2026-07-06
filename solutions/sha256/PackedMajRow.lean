import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Maj32Theorems
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Cross-round packed `Maj` rows (two-row unique pin)

The soundness core of the cross-round `Maj` packing. For one bit index, the packed
witness `Z` superimposes the two rounds' majority bits at weights `1` and `λ`:

  `Z = maj(s,x,y) + λ·maj(u,s,x)`,  per-bit `maj(a,b,c) = a·b + c·(a+b−2·a·b)`,

with inputs `(s,x,y,u) = (a_t[j], b_t[j], c_t[j], a_{t+1}[j])`.

Unlike `Ch` (degree 2, CLASS-P, one row), `Maj` is degree 3, so **no single R1CS row
pins it uniquely**. But *two* two-valued CLASS-A rows do: each is a product of two
affine forms vanishing at the honest value, and their spurious roots differ at every
boolean corner, so their common root is uniquely the honest value. Concretely

  `Row1 = (Z − (λ+1)·s)·(Z − (y + λ·u))            = 0`
  `Row2 = (Z − (s + λ·x))·(Z − (λ·(s+x+u−1) + y))  = 0`.

`Row1 − Row2` is *linear* in `Z` with coefficient `λ·(2x−1)` (a unit for boolean `x`
and `λ ≠ 0`), which pins `Z`. Verified exhaustively (symbolically in `λ`) on the
boolean cube and mod `p` at `λ = 2^40`.
-/

namespace PackedMajRow

/-- Per-bit majority value `maj(a,b,c) = a·b + c·(a+b−2·a·b)` (the honest `Maj32`
    witness value). -/
def majBit (a b c : F p) : F p := a * b + c * (a + b - 2 * (a * b))

lemma majBit_isBool {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    IsBool (majBit a b c) :=
  Maj32.maj_is_bool ha hb hc

/-- **Packed cross-round `Maj` two-row uniqueness.** With `s, x, y, u` boolean and
    `λ ≠ 0`, the two R1CS rows

      `Row1 = (Z − (λ+1)·s)·(Z − (y + λ·u))            = 0`,
      `Row2 = (Z − (s + λ·x))·(Z − (λ·(s+x+u−1) + y))  = 0`,

    pin the witness `Z` to the packed value `maj(s,x,y) + λ·maj(u,s,x)`. The linear
    form `Row1 − Row2 = λ·(2x−1)·Z + …` has invertible leading coefficient. -/
lemma majRows_unique {lam s x y u Z : F p} (hlam : lam ≠ 0)
    (hs : IsBool s) (hx : IsBool x) (hy : IsBool y) (hu : IsBool u)
    (h1 : (Z - (lam + 1) * s) * (Z - (y + lam * u)) = 0)
    (h2 : (Z - (s + lam * x)) * (Z - (lam * (s + x + u - 1) + y)) = 0) :
    Z = majBit s x y + lam * majBit u s x := by
  have hs' : s * (s - 1) = 0 := by rcases hs with h | h <;> rw [h] <;> ring
  have hx' : x * (x - 1) = 0 := by rcases hx with h | h <;> rw [h] <;> ring
  -- `λ·(2x−1)·(Z − honest) = (Row1 − Row2) + corrections` (coefficients machine-found).
  have key : lam * (2 * x - 1) * (Z - (majBit s x y + lam * majBit u s x)) = 0 := by
    unfold majBit
    linear_combination h1 - h2 + lam * hs'
      + (4 * lam ^ 2 * s * u - 2 * lam ^ 2 * s - 2 * lam ^ 2 * u + lam ^ 2
          + 4 * lam * s * y - 2 * lam * s - 2 * lam * y) * hx'
  -- `2x − 1 ≠ 0` for boolean `x`; combined with `λ ≠ 0`, the leading coefficient is a unit.
  have hx2 : (2 * x - 1 : F p) ≠ 0 := by
    rcases hx with h | h <;> rw [h] <;> intro hc
    · exact one_ne_zero (by linear_combination -hc)
    · exact one_ne_zero (by linear_combination hc)
  have hunit : lam * (2 * x - 1) ≠ 0 := mul_ne_zero hlam hx2
  rcases mul_eq_zero.mp key with hz | hz
  · exact absurd hz hunit
  · exact eq_of_sub_eq_zero hz

end PackedMajRow
end Solution.SHA256
end
