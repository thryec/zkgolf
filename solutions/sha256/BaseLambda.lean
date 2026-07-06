import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Base-λ separation for the fused two-round adder

The one genuinely new arithmetic fact behind the cross-round packing redesign
(design §2.2). With `λ = 2^40`, a single fused field equation
`A + 2^40·B = A' + 2^40·B'` over `F p` (`p > 2^76`) between four naturals each
`< 2^35` is *equivalent to* the two independent integer equations `A = A'` and
`B = B'`. The fused two-round adder emits exactly one such row per chain; this
lemma splits it back into the two per-round modular-addition equations.

*Proof.* Reduce to a single `Nat`-cast equality; both sides are `< 2^76 < p`, so
`ZMod.val` injectivity lifts it to `A + 2^40·B = A' + 2^40·B'` over `ℕ`. Since
`A, A' < 2^35 < 2^40`, base-`2^40` uniqueness (`omega`) forces `A = A'`, `B = B'`.
-/

/-- **Base-λ separation** (`λ = 2^40`). For `A, B, A', B' < 2^35`, the fused field
    equation `A + 2^40·B = A' + 2^40·B'` in `F p` (with `p > 2^76`) is equivalent to
    `A = A' ∧ B = B'`. -/
lemma baseLambda_sep [Fact (p > 2^76)] {A B A' B' : ℕ}
    (hA : A < 2^35) (hB : B < 2^35) (hA' : A' < 2^35) (hB' : B' < 2^35)
    (h : (A : F p) + 2^40 * (B : F p) = (A' : F p) + 2^40 * (B' : F p)) :
    A = A' ∧ B = B' := by
  have hp : (2:ℕ)^76 < p := Fact.out
  -- Combine into a single natural-number cast equality.
  have hcast : ((A + 2^40 * B : ℕ) : F p) = ((A' + 2^40 * B' : ℕ) : F p) := by
    push_cast
    linear_combination h
  -- Numeric expansions so `omega` can reason with the literal coefficient.
  have e35 : (2:ℕ)^35 = 34359738368 := by norm_num
  have e40 : (2:ℕ)^40 = 1099511627776 := by norm_num
  have e76 : (2:ℕ)^76 = 75557863725914323419136 := by norm_num
  have hlt1 : A + 2^40 * B < p := by
    rw [e40]; rw [e35] at hA hB; rw [e76] at hp; omega
  have hlt2 : A' + 2^40 * B' < p := by
    rw [e40]; rw [e35] at hA' hB'; rw [e76] at hp; omega
  have hnat : A + 2^40 * B = A' + 2^40 * B' := by
    have hv := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hv
  rw [e40] at hnat; rw [e35] at hA hB hA' hB'
  omega

end Solution.SHA256
end
