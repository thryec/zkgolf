import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Params24
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostG
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Bytes24

/-!
# Zero-witness B=24 byte-packing subcircuits

At `B = 24`, every RSA byte string packs three bytes per limb, with a 2-byte top
limb (bytes `510`/`511` — real data, no zero spare limb). These wrappers keep the
top-level `Main.lean` structure close to the B=32 solution while making the
byte-glue cost zero.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS
open Specs.RSASSAPKCS1v15
open BytesLemmas
open BytesSplitLemmas
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

namespace Bytes24ToBigInt

/-- Pure 512-byte to `BigInt 171` packing at `B = 24`. -/
def main (bytes : Var (fields modulusBytesLen) (F circomPrime)) :
    Circuit (F circomPrime) (Var (BigInt numLimbs24) (F circomPrime)) :=
  pure (Bytes24.packLimbs3 bytes)

instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields modulusBytesLen) (BigInt numLimbs24) main where
  localLength _ := 0
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
  output bytes _ := Bytes24.packLimbs3 bytes
  output_eq := by
    intro input offset
    simp only [main, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]
  channelsLawful := by
    intro input offset
    simp only [main, circuit_norm]

/-- Precondition: the public bytes are octets. -/
def Assumptions (bytes : (fields modulusBytesLen) (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat bytes)

/-- Postcondition: the packed value is normalized and denotes `os2ip bytes`. -/
def Spec (bytes : (fields modulusBytesLen) (F circomPrime))
    (out : BigInt numLimbs24 (F circomPrime)) : Prop :=
  out.Normalized 24 ∧ out.value 24 = os2ip (fieldBytesToNat bytes)

set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  have hbytes : ∀ je, je < 512 → byteVal env input_var je < 256 := by
    intro je hje
    have h := h_assumptions ⟨511 - je, by show 511 - je < 512; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at h
    simpa [byteVal] using h
  constructor
  · exact Bytes24.packLimbs3_normalized env input_var hbytes
  · rw [Bytes24.packLimbs3_value_eq_os2ip env input_var hbytes]
    have hfb : Vector.map (fun e => (Expression.eval env e).val) input_var
        = fieldBytesToNat input := by
      rw [← h_input]
      unfold fieldBytesToNat
      rw [Vector.map_map]
      rfl
    rw [hfb]

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main, Assumptions]

/-- Formal zero-cost byte-packing circuit. -/
def circuit : FormalCircuit (F circomPrime) (fields modulusBytesLen) (BigInt numLimbs24) := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

end Bytes24ToBigInt

namespace PadDigest24

/-- Pure SHA-256 digest to PKCS#1-v1_5 encoded-message packing at `B = 24`. -/
def main (digest : Var (fields digestBytesLen) (F circomPrime)) :
    Circuit (F circomPrime) (Var (BigInt numLimbs24) (F circomPrime)) :=
  pure (Bytes24.packLimbs3 (emByteExpr digest))

instance elaborated :
    ElaboratedCircuit (F circomPrime) (fields digestBytesLen) (BigInt numLimbs24) main where
  localLength _ := 0
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm]
  output digest _ := Bytes24.packLimbs3 (emByteExpr digest)
  output_eq := by
    intro input offset
    simp only [main, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp only [main, circuit_norm]
  channelsLawful := by
    intro input offset
    simp only [main, circuit_norm]

/-- Precondition: the digest bytes are octets. -/
def Assumptions (digest : (fields digestBytesLen) (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat digest)

/-- Postcondition: the packed EM is normalized, bounded, and equal to EMSA output. -/
def Spec (digest : (fields digestBytesLen) (F circomPrime))
    (out : BigInt numLimbs24 (F circomPrime)) : Prop :=
  out.Normalized 24 ∧
    out.value 24 < 2 ^ 4088 ∧
    ∃ EM : Vector ℕ 512,
      emsaPkcs1v15Encode? HashAlgorithm.sha256 (fieldBytesToNat digest) 512 = some EM ∧
        IsOctetString EM ∧
        out.value 24 = os2ip EM

set_option maxRecDepth 8192 in
theorem soundness : Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  have hoct' : ∀ (dj : ℕ) (hdj : dj < 32),
      (Expression.eval env (input_var[dj]'hdj)).val < 256 := by
    intro dj hdj
    have h := h_assumptions ⟨dj, by show dj < 32; omega⟩
    simp only [fieldBytesToNat, Fin.getElem_fin, Vector.getElem_map, ← h_input] at h
    simpa using h
  have hoct : IsOctetString (Vector.map (fun e => (Expression.eval env e).val) input_var) := by
    intro i
    rw [Fin.getElem_fin, Vector.getElem_map]
    exact hoct' i.val i.isLt
  have hfb : fieldBytesToNat input
      = Vector.map (fun e => (Expression.eval env e).val) input_var := by
    rw [← h_input]
    unfold fieldBytesToNat
    rw [Vector.map_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · exact Bytes24.packLimbs3_normalized env (emByteExpr input_var)
      (BytesSplitLemmas.em_bytes_lt env input_var hoct')
  · exact Bytes24.packLimbs3_em_value_lt env input_var hoct'
  · refine ⟨emVec (Vector.map (fun e => (Expression.eval env e).val) input_var), ?_, ?_, ?_⟩
    · rw [hfb]
      exact emsaEncode_eq_emVec _ hoct
    · exact isOctetString_emVec _ hoct
    · exact Bytes24.packLimbs3_em_value_eq env input_var hoct'

theorem completeness : Completeness (F circomPrime) main Assumptions := by
  circuit_proof_start [main, Assumptions]

/-- Formal zero-cost digest-padding circuit. -/
def circuit : FormalCircuit (F circomPrime) (fields digestBytesLen) (BigInt numLimbs24) := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}

end PadDigest24

namespace GadgetCost

/-! ## `Bytes24.packLimbs3` affineness (the packing is witness-free) -/

/-- Every limb of the 3-bytes-per-limb packing is affine when the byte
expressions are (the 2-byte top limb included). -/
theorem affineW_packLimbs3 (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ j (hj : j < 512), Affine bytes[j]) :
    AffineW (Bytes24.packLimbs3 bytes) := by
  intro k hk
  rw [Bytes24.packLimbs3, Vector.getElem_ofFn]
  split
  · refine Affine.add (Affine.add (hbytes _ (by omega)) ?_) ?_
    · exact Affine.mul_fconst _ (hbytes _ (by omega))
    · exact Affine.mul_fconst _ (hbytes _ (by omega))
  · exact Affine.add (hbytes _ (by omega)) (Affine.mul_fconst _ (hbytes _ (by omega)))

theorem costIs_sub_bytes24ToBigInt
    (b : Var (fields modulusBytesLen) (F circomPrime)) :
    CostIs (subcircuit Bytes24ToBigInt.circuit b) Count.zero :=
  CostIs.subcircuit
    (circuit := Bytes24ToBigInt.circuit) (b := b)
    (fun n => (CostIs.pure (Bytes24.packLimbs3 b) :
      CostIs (Bytes24ToBigInt.main b) Count.zero) n)

theorem costIs_sub_padDigest24
    (b : Var (fields digestBytesLen) (F circomPrime)) :
    CostIs (subcircuit PadDigest24.circuit b) Count.zero :=
  CostIs.subcircuit
    (circuit := PadDigest24.circuit) (b := b)
    (fun n => (CostIs.pure (Bytes24.packLimbs3 (emByteExpr b)) :
      CostIs (PadDigest24.main b) Count.zero) n)

theorem isR1CS_sub_bytes24ToBigInt
    (b : Var (fields modulusBytesLen) (F circomPrime))
    (_hb : AffineW b) :
    IsR1CSCirc (subcircuit Bytes24ToBigInt.circuit b) :=
  IsR1CSCirc.subcircuit
    (circuit := Bytes24ToBigInt.circuit) (b := b)
    (fun n => (IsR1CSCirc.pure (Bytes24.packLimbs3 b) :
      IsR1CSCirc (Bytes24ToBigInt.main b)) n)

theorem isR1CS_sub_padDigest24
    (b : Var (fields digestBytesLen) (F circomPrime))
    (_hb : AffineW b) :
    IsR1CSCirc (subcircuit PadDigest24.circuit b) :=
  IsR1CSCirc.subcircuit
    (circuit := PadDigest24.circuit) (b := b)
    (fun n => (IsR1CSCirc.pure (Bytes24.packLimbs3 (emByteExpr b)) :
      IsR1CSCirc (PadDigest24.main b)) n)

theorem affineW_sub_bytes24ToBigInt
    (b : Var (fields modulusBytesLen) (F circomPrime))
    (hb : AffineW b)
    (off : ℕ) :
    AffineW ((subcircuit Bytes24ToBigInt.circuit b).output off) := by
  change AffineW (Bytes24.packLimbs3 b)
  exact affineW_packLimbs3 b hb

theorem affineW_sub_padDigest24
    (b : Var (fields digestBytesLen) (F circomPrime))
    (hb : AffineW b)
    (off : ℕ) :
    AffineW ((subcircuit PadDigest24.circuit b).output off) := by
  change AffineW (Bytes24.packLimbs3 (emByteExpr b))
  exact affineW_packLimbs3 (emByteExpr b) (affine_emByteExpr b hb)

end GadgetCost

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
