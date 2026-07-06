import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesSplitLemmas
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ByteBlockTheorems

/-!
# `BytesToBigInt` subcircuit — 512 big-endian bytes → `BigInt 34`

A self-contained `FormalCircuit` converting a `modulusBytesLen`-byte big-endian
octet string into the `BigInt 34` little-endian-limb representation of the
integer it denotes (`os2ip`).

The trusted `Assumptions` already guarantee every byte is `< 256`
(`IsOctetString`), so the limbs are built as **affine** combinations of the
byte expressions themselves (`packLimbsSplit`). Witnesses are needed only at
the `29` limb boundaries `121·k` (`k % 8 ≠ 0`) that fall strictly inside a
byte: for each such boundary the straddled byte's low `7` bits are witnessed
(`witnessVector 203`), boolean-checked, and its top bit is the implicit affine
expression `2⁻⁷·(byte − Σ bits·2^i)`, boolean-checked as well (29 rows). Total:
`203` witnesses and `232` constraint rows (vs. `4096`/`4608` for the bit-level
decomposition).

Used twice by `main` — once for the modulus, once for the signature.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace BytesToBigInt

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open BytesLemmas
open BytesSplitLemmas
open Specs.RSASSAPKCS1v15

/-- The `main` circuit: witness the `29·7 = 203` split bits, boolean-check them
and the `29` implicit top bits, and return the affine byte-split packing. -/
def main (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) := do
  let splitBits ← witnessVector 203 (splitBitsWitness bytes)
  Circuit.forEach splitBits (fun b => assertZero (b * (b - 1)))
  Circuit.forEach (Vector.ofFn fun s : Fin 29 =>
      splitTop bytes splitBits s.val * (splitTop bytes splitBits s.val - 1))
    assertZero
  return packLimbsSplit bytes (splitLoExpr splitBits) (splitHiExpr bytes splitBits)

set_option maxRecDepth 8192 in
instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields modulusBytesLen) (BigInt numLimbs) main where
  localLength _ := 203
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
  output bytes offset :=
    packLimbsSplit bytes (splitLoExpr (varFromOffset (fields 203) offset))
      (splitHiExpr bytes (varFromOffset (fields 203) offset))
  output_eq := by
    intro input offset
    simp only [main, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith [main, circuit_norm]
  channelsLawful := by
    intro input offset
    simp +arith [main, circuit_norm]

/-- Precondition: the input is a genuine octet string (each byte `< 256`). -/
def Assumptions (bytes : (fields modulusBytesLen) (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat bytes)

/-- Postcondition: the output is a normalized big integer denoting `os2ip bytes`. -/
def Spec (bytes : (fields modulusBytesLen) (F circomPrime))
    (out : BigInt numLimbs (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧
    out.value limbBits = os2ip (fieldBytesToNat bytes)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  set splitBits := (Vector.mapRange 203 fun i ↦ var (F := F circomPrime) { index := i₀ + i })
    with hBits
  obtain ⟨h_bool, h_top⟩ := h_holds
  -- booleanity of the 203 witnessed bits
  have hbool : ∀ (i : ℕ) (hi : i < 203),
      (Expression.eval env (splitBits[i]'hi)).val < 2 := by
    intro i hi
    rw [hBits, Vector.getElem_mapRange]
    show (env.get (i₀ + i)).val < 2
    have hz := h_bool ⟨i, hi⟩
    have hz' : env.get (i₀ + i) * (env.get (i₀ + i) - 1) = 0 := by
      rw [sub_eq_add_neg]; exact hz
    exact IsBool.val_lt_two (IsBool.iff_mul_sub_one.mpr hz')
  -- the 29 top-bit booleanity constraints
  have htop : ∀ s : Fin 29,
      Expression.eval env (splitTop input_var splitBits s.val)
        * (Expression.eval env (splitTop input_var splitBits s.val) - 1) = 0 := by
    intro s
    have h := h_top s
    rw [Vector.getElem_ofFn] at h
    exact eval_mul_sub_one env _ h
  -- byteness of the input
  have hbytes : ∀ je, je < 512 → byteVal env input_var je < 256 := by
    intro je hje
    have h := h_assumptions ⟨511 - je, by show 511 - je < 512; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at h
    simpa [byteVal] using h
  have hsplitp := splitPieces_of_constraints env input_var splitBits hbool htop
  constructor
  · exact packLimbsSplit_normalized env input_var _ _ hbytes hsplitp
  · rw [packLimbsSplit_value_eq_os2ip env input_var _ _ hbytes hsplitp]
    congr 1
    rw [fieldBytesToNat, ← h_input, fieldBytesToNat]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8192 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main, Assumptions]
  set splitBits := (Vector.mapRange 203 fun i ↦ var (F := F circomPrime) { index := i₀ + i })
    with hBits
  -- byteness of the input
  have hbytes : ∀ je, je < 512 → byteVal env.toEnvironment input_var je < 256 := by
    intro je hje
    have h := h_assumptions ⟨511 - je, by show 511 - je < 512; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at h
    simpa [byteVal] using h
  -- each witnessed cell holds the corresponding byte digit
  have hbiteval : ∀ (i : ℕ), i < 203 →
      env.get (i₀ + i)
        = ((byteVal env.toEnvironment input_var (splitByteLE (splitBoundary (i / 7)))
              / 2 ^ (i % 7) % 2 : ℕ) : F circomPrime) := by
    intro i hi
    rw [h_env.1 ⟨i, hi⟩]
    simp only [splitBitsWitness, Vector.getElem_ofFn]
    rw [dif_pos (show 511 - splitByteLE (splitBoundary (i / 7)) < modulusBytesLen from by
      show 511 - splitByteLE (splitBoundary (i / 7)) < 512
      omega)]
    rfl
  -- bit values as `bitVal`
  have hbitVal : ∀ (s : ℕ), s < 29 → ∀ (i : ℕ), i < 7 →
      bitVal env.toEnvironment splitBits (7 * s + i)
        = byteVal env.toEnvironment input_var (splitByteLE (splitBoundary s)) / 2 ^ i % 2 := by
    intro s hs i hi
    unfold bitVal
    rw [dif_pos (show 7 * s + i < 203 from by omega)]
    rw [hBits, Vector.getElem_mapRange]
    show (env.get (i₀ + (7 * s + i))).val = _
    rw [hbiteval (7 * s + i) (by omega)]
    rw [show (7 * s + i) / 7 = s from by omega, show (7 * s + i) % 7 = i from by omega]
    exact val_natCast_lt' (lt_trans (Nat.mod_lt _ (by norm_num))
      (lt_trans (by norm_num) two_pow_256_lt_circomPrime))
  constructor
  · -- booleanity rows
    intro i
    apply mul_add_neg_one_eq_zero
    rw [hbiteval i.val i.isLt]
    rw [val_natCast_lt' (lt_trans (Nat.mod_lt _ (by norm_num))
      (lt_trans (by norm_num) two_pow_256_lt_circomPrime))]
    exact Nat.mod_lt _ (by norm_num)
  · -- top-bit booleanity rows
    intro s
    rw [Vector.getElem_ofFn]
    have hy := hbytes (splitByteLE (splitBoundary s.val)) (by
      show splitByteLE (splitBoundary s.val) < 512
      have := s.isLt
      simp only [splitByteLE, splitBoundary]
      omega)
    have htopval := split_complete env.toEnvironment input_var splitBits s.val
      (by have := s.isLt; omega)
      (fun i hi => hbitVal s.val s.isLt i hi) hy
    exact eval_mul_sub_one_zero env.toEnvironment _ _
      (Nat.div_lt_of_lt_mul (by
        have h128 : (2:ℕ) ^ 7 = 128 := by norm_num
        omega))
      htopval

/-- The `BytesToBigInt` formal circuit. -/
def circuit : FormalCircuit (F circomPrime) (fields modulusBytesLen) (BigInt numLimbs) := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

end BytesToBigInt
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
