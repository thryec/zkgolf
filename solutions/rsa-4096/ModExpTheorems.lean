import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExp

/-!
# A shallow closed form for the `ModExp` output variable

`circuit_proof_start` on the top-level RSA circuit embeds
`(ModExp.circuit P).output …` in the resulting goal. By default this is
`(ModExp.main P input).output offset`, whose normal form runs the entire
unrolled square-and-multiply loop — a term so deep the kernel/elaborator hits
its recursion limit when the goal is touched.

Here we give that output a shallow `varFromOffset` closed form and register it
with `circuit_norm`, so the offset machinery in `circuit_proof_start` rewrites it
to a small term and the soundness proof stays tractable.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace ModExp

open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- Length of the blocks *before* the last one in the unrolled loop (the output
sits `m` slots into the last block). Each squaring contributes `S = squareModLen`,
each multiply `L = mulModLen`; the last block is a multiply (last bit set) or a
squaring (last bit clear). Subtraction-free so the offset arithmetic stays linear. -/
def prefixLen (S L : ℕ) : List Bool → ℕ
  | [] => 0
  | [b] => if b then S else 0
  | b :: (c :: r) => (S + (if b then L else 0)) + prefixLen S L (c :: r)

/-- The output variable of the unrolled loop is a `varFromOffset` sitting `m` slots
into the last squaring/multiply block, at `offset + prefixLen S L (bit :: rest) + m`. -/
lemma modExpLoop_output (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p)
    (htbB : tb + 2 ≤ P.B) [Fact (p > 2)]
    (base n : Var (BigInt m) (F p)) (bit : Bool) :
    ∀ (rest : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      (modExpLoop P tb htb htbB base n (bit :: rest) acc).output offset
        = varFromOffset (BigInt m)
            (offset + prefixLen (squareModLen (m := m) P.B P.W tb) (mulModLen (m := m) P.B P.W tb) (bit :: rest)
              + m) := by
  have hSL : ∀ (x : Var (SquareModLazy.Inputs m) (F p)),
      (SquareModLazy.circuit P tb htb htbB).localLength x = squareModLen (m := m) P.B P.W tb := fun _ => rfl
  have hML : ∀ (x : Var (MulMod.Inputs m) (F p)),
      (MulModLazy.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB))).localLength x = mulModLen (m := m) P.B P.W tb := fun _ => rfl
  have hstep : ∀ (bs : List Bool) (acc' : Var (BigInt m) (F p)) (o : ℕ),
      (modExpLoop P tb htb htbB base n bs acc' o).1 = (modExpLoop P tb htb htbB base n bs acc').output o := fun _ _ _ => rfl
  suffices H : ∀ (bs : List Bool) (acc : Var (BigInt m) (F p)) (offset : ℕ), bs ≠ [] →
      (modExpLoop P tb htb htbB base n bs acc).output offset
        = varFromOffset (BigInt m)
            (offset + prefixLen (squareModLen (m := m) P.B P.W tb) (mulModLen (m := m) P.B P.W tb) bs + m) by
    intro rest acc offset
    exact H (bit :: rest) acc offset (by simp)
  intro bs
  induction bs with
  | nil => intro acc offset hne; exact absurd rfl hne
  | cons b rest ih =>
    intro acc offset _
    set S := squareModLen (m := m) P.B P.W tb with hS
    set L := mulModLen (m := m) P.B P.W tb with hL
    cases b
    · -- clear bit: 1 square, then loop on `rest`
      show (modExpLoop P tb htb htbB base n rest
          (Vector.mapRange m fun i => var { index := offset + m + i })
          (offset + (SquareModLazy.circuit P tb htb htbB).localLength { a := acc, modulus := n })).1 = _
      rw [hSL, hstep]
      cases rest with
      | nil =>
        rw [show (modExpLoop P tb htb htbB base n [] (Vector.mapRange m fun i => var { index := offset + m + i })).output
              (offset + S) = (Vector.mapRange m fun i => var { index := offset + m + i }) from rfl,
            ProvableType.varFromOffset_fields]
        apply Vector.ext
        intro i hi
        simp only [Vector.getElem_mapRange, prefixLen, Bool.false_eq_true, if_false, Nat.add_zero]
      | cons b2 r2 =>
        rw [ih _ _ (by simp)]
        congr 1
        show offset + S + prefixLen S L (b2 :: r2) + m = _
        simp only [prefixLen, Bool.false_eq_true, if_false, Nat.add_zero, Nat.add_assoc]
    · -- set bit: square + multiply, then loop on `rest`
      show (modExpLoop P tb htb htbB base n rest
          ((MulModLazy.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB))).output
            { a := (SquareModLazy.circuit P tb htb htbB).output { a := acc, modulus := n } offset,
              b := base, modulus := n }
            (offset + (SquareModLazy.circuit P tb htb htbB).localLength { a := acc, modulus := n }))
          (offset + (SquareModLazy.circuit P tb htb htbB).localLength { a := acc, modulus := n } +
            (MulModLazy.circuit P tb htb (Nat.le_of_succ_le (Nat.le_of_succ_le htbB))).localLength
              { a := (SquareModLazy.circuit P tb htb htbB).output { a := acc, modulus := n } offset,
                b := base, modulus := n })).1 = _
      rw [hSL, hML, hstep]
      cases rest with
      | nil =>
        show (varFromOffset (BigInt m) (offset + S + m) : (BigInt m) (Expression (F p)))
            = varFromOffset (BigInt m) _
        congr 1
      | cons b2 r2 =>
        rw [ih _ _ (by simp)]
        congr 1
        show offset + S + L + prefixLen S L (b2 :: r2) + m = _
        simp only [prefixLen, if_true, Nat.add_assoc]

/-- `prefixLen` of a run of `k` clear bits followed by a final set bit: `k` squarings
before the last (square + multiply) block, whose output sits one square in — total
`(k+1)·S`. This is exactly the shape of `eBits 65537`'s tail. -/
lemma prefixLen_falses_true (S L : ℕ) :
    ∀ k, prefixLen S L (List.replicate k false ++ [true]) = (k + 1) * S := by
  intro k
  induction k with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, prefixLen, if_true]
    ring
  | succ j ih =>
    have hcr : ∃ c r, List.replicate j false ++ [true] = c :: r := by
      cases j with
      | zero => exact ⟨true, [], by simp⟩
      | succ i => exact ⟨false, List.replicate i false ++ [true], by rw [List.replicate_succ, List.cons_append]⟩
    obtain ⟨c, r, hcr⟩ := hcr
    rw [List.replicate_succ, List.cons_append, hcr]
    show (S + (if false then L else 0)) + prefixLen S L (c :: r) = _
    rw [← hcr, ih]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    ring

/-- `prefixLen` of a run of `k+1` clear bits: `k` squaring blocks before the last
one (whose output sits `m` slots in). This is exactly the shape of
`eBits 65536`'s tail (16 clear bits). -/
lemma prefixLen_falses (S L : ℕ) :
    ∀ k, prefixLen S L (List.replicate (k + 1) false) = k * S := by
  intro k
  induction k with
  | zero =>
    show (if false then S else 0) = 0 * S
    simp
  | succ j ih =>
    have hcr : List.replicate (j + 1) false = false :: List.replicate j false :=
      List.replicate_succ ..
    rw [List.replicate_succ, hcr]
    show (S + (if false then L else 0)) + prefixLen S L (false :: List.replicate j false) = _
    rw [← hcr, ih]
    simp only [Bool.false_eq_true, if_false, Nat.add_zero]
    ring

/-- Shallow closed form for the top-level `ModExp.main` output **when the tail of
`eBits P.e` is non-empty** (the case for every `e ≥ 2`, in particular
`e = 65537`). Registered with `circuit_norm` so it fires inside
`circuit_proof_start`, keeping the resulting goal small. -/
@[circuit_norm]
lemma main_output_of_tail (P : RSAParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p)
    (htbB : tb + 2 ≤ P.bigIntParams.B) [Fact (p > 2)]
    (input : Var (Inputs m) (F p)) (offset : ℕ)
    (headBit : Bool) (b2 : Bool) (r2 : List Bool)
    (h : eBits P.e = headBit :: b2 :: r2) :
    (main P tb htb htbB input).output offset
      = varFromOffset (BigInt m)
          (offset + prefixLen (squareModLen (m := m) P.bigIntParams.B P.bigIntParams.W tb)
              (mulModLen (m := m) P.bigIntParams.B P.bigIntParams.W tb) (b2 :: r2)
            + m) := by
  simp only [main, h]
  show (modExpLoop P.bigIntParams tb htb htbB input.base input.modulus (b2 :: r2) input.base).output offset = _
  exact modExpLoop_output P.bigIntParams tb htb htbB input.base input.modulus b2 r2 input.base offset

end

end ModExp
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
