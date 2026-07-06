import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesSplitLemmas
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ByteBlockTheorems

/-!
# `PadDigest` subcircuit — SHA-256 digest bytes → padded message representative `h`

The EMSA-PKCS1-v1_5 encoding step, as an **affine** byte-split packing. The EM
byte vector is the digest spliced under the constant `00 01 FF…FF 00 ‖
DigestInfo` frame (`emByteExpr`), so every EM byte is either a digest byte
expression or a literal constant — *padding is enforced by construction*. The
`BigInt 34` limbs are affine combinations of those bytes (`packLimbsSplit`);
witnesses are needed only at the two limb boundaries inside the digest region
(`121` and `242`): `2·7 = 14` witnessed bits with `14 + 2 = 16` booleanity
rows. The straddled constant-region bytes are split arithmetically at
elaboration time, for free.

The output `h` denotes `os2ip (EMSA-PKCS1-v1_5-ENCODE(digest))` and is bounded
by `2^4088` (the top EM byte is `0x00`), which lets `main` derive `h < n` from
the modulus bit-size assumption.

Soundness and completeness are fully proved.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace PadDigest

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Bytes
open BytesLemmas
open BytesSplitLemmas
open Specs.RSASSAPKCS1v15

/-- The two straddled digest bytes sit below index 32. -/
theorem splitByteLE_digest_lt (s : ℕ) (hs : s < 2) :
    splitByteLE (splitBoundary s) < 32 := by
  simp only [splitByteLE, splitBoundary]
  omega

/-- The `main` circuit: witness the `2·7 = 14` digest split bits, boolean-check
them and the `2` implicit top bits, and return the affine byte-split packing of
the EM byte vector. -/
def main (digest : Var (fields digestBytesLen) (F circomPrime)) :
    Circuit (F circomPrime) (Var (BigInt numLimbs) (F circomPrime)) := do
  let splitBits ← witnessVector 14 (digestSplitBitsWitness digest)
  Circuit.forEach splitBits (fun b => assertZero (b * (b - 1)))
  Circuit.forEach (Vector.ofFn fun s : Fin 2 =>
      splitTop (emByteExpr digest) splitBits s.val
        * (splitTop (emByteExpr digest) splitBits s.val - 1))
    assertZero
  return packLimbsSplit (emByteExpr digest) (emSplitLo splitBits)
    (emSplitHi (emByteExpr digest) splitBits)

set_option maxRecDepth 8192 in
instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields digestBytesLen) (BigInt numLimbs) main where
  localLength _ := 14
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
  output digest offset :=
    packLimbsSplit (emByteExpr digest) (emSplitLo (varFromOffset (fields 14) offset))
      (emSplitHi (emByteExpr digest) (varFromOffset (fields 14) offset))
  output_eq := by
    intro input offset
    simp only [main, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith [main, circuit_norm]
  channelsLawful := by
    intro input offset
    simp +arith [main, circuit_norm]

/-- Precondition: the digest is a genuine octet string (each byte `< 256`). -/
def Assumptions (digest : (fields digestBytesLen) (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat digest)

/-- Postcondition: the output is a normalized big integer, bounded by `2^4088`,
denoting `os2ip EM` where `EM` is the EMSA-PKCS1-v1_5 encoding of the digest. -/
def Spec (digest : (fields digestBytesLen) (F circomPrime))
    (out : BigInt numLimbs (F circomPrime)) : Prop :=
  out.Normalized limbBits ∧
    out.value limbBits < 2 ^ 4088 ∧
    ∃ EM : Vector ℕ 512,
      emsaPkcs1v15Encode? HashAlgorithm.sha256 (fieldBytesToNat digest) 512 = some EM ∧
        IsOctetString EM ∧
        out.value limbBits = os2ip EM

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  set splitBits := (Vector.mapRange 14 fun i ↦ var (F := F circomPrime) { index := i₀ + i })
    with hBits
  obtain ⟨h_bool, h_top⟩ := h_holds
  -- booleanity of the 14 witnessed bits
  have hbool : ∀ (i : ℕ) (hi : i < 14),
      (Expression.eval env (splitBits[i]'hi)).val < 2 := by
    intro i hi
    rw [hBits, Vector.getElem_mapRange]
    show (env.get (i₀ + i)).val < 2
    have hz := h_bool ⟨i, hi⟩
    have hz' : env.get (i₀ + i) * (env.get (i₀ + i) - 1) = 0 := by
      rw [sub_eq_add_neg]; exact hz
    exact IsBool.val_lt_two (IsBool.iff_mul_sub_one.mpr hz')
  -- the 2 top-bit booleanity constraints
  have htop : ∀ s : Fin 2,
      Expression.eval env (splitTop (emByteExpr input_var) splitBits s.val)
        * (Expression.eval env (splitTop (emByteExpr input_var) splitBits s.val) - 1) = 0 := by
    intro s
    have h := h_top s
    rw [Vector.getElem_ofFn] at h
    exact eval_mul_sub_one env _ h
  -- byteness of the digest, then of the whole EM byte vector
  have hoct' : ∀ (dj : ℕ) (hdj : dj < 32),
      (Expression.eval env (input_var[dj]'hdj)).val < 256 := by
    intro dj hdj
    have h := h_assumptions ⟨dj, by show dj < 32; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at h
    simpa using h
  have hembytes := em_bytes_lt env input_var hoct'
  have hsplitp := em_splitPieces env input_var splitBits hbool htop
  -- octet-string fact for the evaluated digest bytes
  have hoct : Specs.RSASSAPKCS1v15.IsOctetString
      (Vector.map (fun e => (Expression.eval env e).val) input_var) := by
    intro i
    rw [Fin.getElem_fin, Vector.getElem_map]
    exact hoct' i.val i.isLt
  -- `fieldBytesToNat input = map (val ∘ eval) input_var`
  have hfb : fieldBytesToNat input
      = Vector.map (fun e => (Expression.eval env e).val) input_var := by
    rw [← h_input]; unfold fieldBytesToNat; rw [Vector.map_map]; rfl
  refine ⟨?_, ?_, ?_⟩
  · -- Normalized
    exact packLimbsSplit_normalized env (emByteExpr input_var) _ _ hembytes hsplitp
  · -- value < 2^4088
    rw [packLimbsSplit_value env (emByteExpr input_var) _ _ hembytes hsplitp]
    exact em_byte_sum_lt env input_var hoct'
  · -- ∃ EM, encode = some EM ∧ IsOctetString EM ∧ value = os2ip EM
    refine ⟨emVec (Vector.map (fun e => (Expression.eval env e).val) input_var), ?_, ?_, ?_⟩
    · rw [hfb]
      exact emsaEncode_eq_emVec _ hoct
    · exact isOctetString_emVec _ hoct
    · rw [packLimbsSplit_value env (emByteExpr input_var) _ _ hembytes hsplitp,
        byte_sum_eq_os2ip, emByteExpr_eval_eq_EM]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8192 in
theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main, Assumptions]
  set splitBits := (Vector.mapRange 14 fun i ↦ var (F := F circomPrime) { index := i₀ + i })
    with hBits
  -- byteness of the digest, then of the whole EM byte vector
  have hoct' : ∀ (dj : ℕ) (hdj : dj < 32),
      (Expression.eval env.toEnvironment (input_var[dj]'hdj)).val < 256 := by
    intro dj hdj
    have h := h_assumptions ⟨dj, by show dj < 32; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at h
    simpa using h
  have hembytes := em_bytes_lt env.toEnvironment input_var hoct'
  -- each witnessed cell holds the corresponding straddled-EM-byte digit
  have hbiteval : ∀ (i : ℕ), i < 14 →
      env.get (i₀ + i)
        = ((byteVal env.toEnvironment (emByteExpr input_var)
              (splitByteLE (splitBoundary (i / 7))) / 2 ^ (i % 7) % 2 : ℕ) : F circomPrime) := by
    intro i hi
    rw [h_env.1 ⟨i, hi⟩]
    simp only [digestSplitBitsWitness, Vector.getElem_ofFn]
    rw [dif_pos (show 511 - splitByteLE (splitBoundary (i / 7)) - 480 < digestBytesLen from by
      show 511 - splitByteLE (splitBoundary (i / 7)) - 480 < 32
      omega)]
    rw [em_byteVal_digest env.toEnvironment input_var _
      (splitByteLE_digest_lt (i / 7) (by omega))]
    rw [getElem_congr_idx (show 511 - splitByteLE (splitBoundary (i / 7)) - 480
        = 31 - splitByteLE (splitBoundary (i / 7)) from by
      have := splitByteLE_digest_lt (i / 7) (by omega)
      omega)]
    rfl
  -- bit values as `bitVal`
  have hbitVal : ∀ (s : ℕ), s < 2 → ∀ (i : ℕ), i < 7 →
      bitVal env.toEnvironment splitBits (7 * s + i)
        = byteVal env.toEnvironment (emByteExpr input_var)
            (splitByteLE (splitBoundary s)) / 2 ^ i % 2 := by
    intro s hs i hi
    unfold bitVal
    rw [dif_pos (show 7 * s + i < 14 from by omega)]
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
    have hy := hembytes (splitByteLE (splitBoundary s.val))
      (by have := splitByteLE_digest_lt s.val s.isLt; omega)
    have htopval := split_complete env.toEnvironment (emByteExpr input_var) splitBits s.val
      (by have := s.isLt; omega)
      (fun i hi => hbitVal s.val s.isLt i hi) hy
    exact eval_mul_sub_one_zero env.toEnvironment _ _
      (Nat.div_lt_of_lt_mul (by
        have h128 : (2:ℕ) ^ 7 = 128 := by norm_num
        omega))
      htopval

/-- The `PadDigest` formal circuit. -/
def circuit : FormalCircuit (F circomPrime) (fields digestBytesLen) (BigInt numLimbs) := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

end PadDigest
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
