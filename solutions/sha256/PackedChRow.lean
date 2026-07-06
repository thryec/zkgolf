import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Ch32Theorems
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

/-!
# Cross-round packed `Ch` row (design §6.3)

The soundness core of the cross-round `Ch` packing. For one bit index, the packed
row superimposes the two rounds' choice bits into a single witness `z`, at weights
`1` and `λ`:

  `z = ch(s,x,y) + λ·ch(u,s,x)`,  where per-bit `ch(e,f,g) = g + e·(f−g)`,

with inputs `(s,x,y,u) = (e_t[j], f_t[j], g_t[j], e_{t+1}[j])`. It is a CLASS-P row:
`z` appears only linearly with coefficient `−8` (a unit mod `p`), so the honest
value is the *unique* root — no separate booleanity row is needed. (Contrast Maj,
whose only single-row cross-round packing is two-valued and unsound, design §4.2.)
-/

namespace PackedChRow

/-- Per-bit choice value `ch(e,f,g) = g + e·(f−g)` (`= f` if `e=1`, `g` if `e=0`),
    the honest `Ch32` witness value. -/
def chBit (e f g : F p) : F p := g + e * (f - g)

/-- **Packed cross-round `Ch` row uniqueness** (design §6.3).
    With `s, x, y, u` boolean and `λ` arbitrary, the single R1CS row `A·B + C = 0`
    with
      `A = −3s + 2x + 4y + 2λu`,
      `B =  s − 2x + 4y − 2λu`,
      `C =  3s + (8λ+4)x − 8y + 4λ²u − 8z`,
    pins the witness `z` to the packed value `ch(s,x,y) + λ·ch(u,s,x)`.
    The coefficient of `z` in `C` is `−8`, a unit for `p > 2^35`. -/
lemma chRow_unique [Fact (p > 2^35)] {lam s x y u z : F p}
    (hs : IsBool s) (hx : IsBool x) (hy : IsBool y) (hu : IsBool u)
    (h : (-3 * s + 2 * x + 4 * y + 2 * lam * u) * (s - 2 * x + 4 * y - 2 * lam * u)
       + (3 * s + (8 * lam + 4) * x - 8 * y + 4 * lam ^ 2 * u - 8 * z) = 0) :
    z = chBit s x y + lam * chBit u s x := by
  have hs' : s * (s - 1) = 0 := by rcases hs with h | h <;> rw [h] <;> ring
  have hx' : x * (x - 1) = 0 := by rcases hx with h | h <;> rw [h] <;> ring
  have hy' : y * (y - 1) = 0 := by rcases hy with h | h <;> rw [h] <;> ring
  have hu' : u * (u - 1) = 0 := by rcases hu with h | h <;> rw [h] <;> ring
  -- The row equals `8·(z − honest)` modulo the four boolean relations.
  have key : (8 : F p) * (z - (chBit s x y + lam * chBit u s x)) = 0 := by
    simp only [chBit]
    linear_combination -h - 3 * hs' - 4 * hx' + 16 * hy' - 4 * lam ^ 2 * hu'
  -- `8 ≠ 0` for `p > 2^35`, so `z` is pinned.
  have h8 : (8 : F p) ≠ 0 := by
    have hp : (2:ℕ) ^ 35 < p := Fact.out
    have hval : ((8 : ℕ) : F p) ≠ 0 := by
      intro hcon
      have hv := congrArg ZMod.val hcon
      rw [ZMod.val_natCast_of_lt (by omega : (8 : ℕ) < p), ZMod.val_zero] at hv
      omega
    simpa using hval
  exact eq_of_sub_eq_zero ((mul_eq_zero.mp key).resolve_left h8)

end PackedChRow
end Solution.SHA256
end
