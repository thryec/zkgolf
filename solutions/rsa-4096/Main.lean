import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MainTheorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Bytes24Circuits
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThanBytes
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SqMulModBalTo
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExpSqGT
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostBal
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Params24

/-!
# B=24/grouped solution — RSASSA-PKCS1-v1_5 / SHA256 / 4096 / e = 65537

Balanced signed-digit residue chain: the 15 chain squarings and the fused final
multiply witness their residues in *balanced* form (digits shifted by `2^(B−1)`
below the top, `tw`-bit top), and the coefficient equalities go through the
two-sided-window grouped equality `GroupedEqD`. The recovered identities are
over ℤ (`VZ(a)² ≡ … (mod n)`), chained through `Int.ModEq`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.GadgetCost

/-- `1 ≤ 16` (input tightness width of the fused final step). -/
theorem htb1_24 : 1 ≤ 16 := by norm_num

/-- `8 ≤ 24` (fused-final quotient top-limb width over `2m` limbs). -/
theorem htqB8 : 8 ≤ bigIntParams24q.B := by decide

/-- Balanced-top window: `1 ≤ 17 ∧ 2^17 < p`. -/
theorem htw24 : 1 ≤ 17 ∧ (2 : ℕ) ^ 17 < circomPrime := ⟨by decide, by decide⟩

/-- `17 ≤ 24` (balanced-top width fits the limb width). -/
theorem htwB24 : 17 ≤ bigIntParams24.B := by decide

/-- `16 < 17` (quotient top `tb` strictly below the balanced-residue top `tw`). -/
theorem htbw24 : 16 < 17 := by decide

/-- Modular-arithmetic bridge for the balanced chain over ℤ: if
`r₁ ≡ s² (mod n)`, `r ≡ r₁^(2^14) (mod n)` and `em ≡ r²·s (mod n)`, then
`em ≡ s^65537 (mod n)`. -/
private lemma zmod_chain {s r1 r em n : ℤ}
    (h1 : r1 ≡ s * s [ZMOD n])
    (h2 : r ≡ r1 ^ (2 ^ 14) [ZMOD n])
    (h3 : em ≡ r * r * s [ZMOD n]) :
    em ≡ s ^ 65537 [ZMOD n] := by
  have hsq : r ≡ s ^ 32768 [ZMOD n] := by
    have hstep := h2.trans (h1.pow (2 ^ 14))
    rw [show ((s * s) ^ (2 ^ 14) : ℤ) = s ^ 32768 from by ring] at hstep
    exact hstep
  have hfin := h3.trans ((hsq.mul hsq).mul (Int.ModEq.refl s))
  rwa [show (s ^ 32768 * s ^ 32768 * s : ℤ) = s ^ 65537 from by ring] at hfin

/-- The first half of `zmod_chain`: `VZ(r) ≡ s^32768 (mod n)`. -/
private lemma zmod_half {s r1 r n : ℤ}
    (h1 : r1 ≡ s * s [ZMOD n]) (h2 : r ≡ r1 ^ (2 ^ 14) [ZMOD n]) :
    r ≡ s ^ 32768 [ZMOD n] := by
  have hstep := h2.trans (h1.pow (2 ^ 14))
  rwa [show ((s * s) ^ (2 ^ 14) : ℤ) = s ^ 32768 from by ring] at hstep

/-- ℤ-congruence to canonical `ℕ` remainder: a canonical `a < n` congruent to
`b` is `b % n`. -/
private lemma zmod_to_nat {a b n : ℕ} (hn : 0 < n) (ha : a < n)
    (h : (a : ℤ) ≡ (b : ℤ) [ZMOD (n : ℤ)]) : a = b % n := by
  have hmod : (a : ℤ) % (n : ℤ) = (b : ℤ) % (n : ℤ) := h
  have hl : (a : ℤ) % (n : ℤ) = (a : ℤ) := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha)
  have hr : (b : ℤ) % (n : ℤ) = ((b % n : ℕ) : ℤ) := (Int.natCast_mod b n).symm
  rw [hl, hr] at hmod
  exact_mod_cast hmod

/-- Claimed witness-allocation count of `main` (proved by `mainCost`). -/
@[reducible] def allocations : Nat := 163529

/-- Claimed constraint-row count of `main` (proved by `mainCost`). -/
@[reducible] def constraints : Nat := 164225

section CircuitDef

/-- The top-level RSASSA-PKCS1-v1_5 / SHA256 / 4096 / e = 65537 verification
circuit (balanced residue chain). -/
def main (input : Var Input (F circomPrime)) :
    Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let n   ← subcircuit Bytes24ToBigInt.circuit input.modulus
  let sig ← subcircuit Bytes24ToBigInt.circuit input.signature
  let h   ← subcircuit PadDigest24.circuit input.digest
  LessThanBytes.circuit { lhs := input.signature, rhs := input.modulus }
  let sq1 ← subcircuitWithAssertion
    (SquareModBalFirstGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24
      gfFbal posOfFbal 39 vparamsFbal vparamsFbal hgvdFbal hNfFbal)
    { a := sig, modulus := n }
  let sq ← subcircuitWithAssertion
    (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24
      gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14)
    { base := sq1, modulus := n }
  subcircuitWithAssertion
    (SqMulModBalTo.generalCircuit bigIntParams24 bigIntParams24q 24 16 17 8 htq8 htqB8 htb1_24 htbq24
      gfXbal posOfXbal 70 vparamsXbal vparamsXRbal hgvdbal (by norm_num) hlhs_adXbal hrhs_adXbal
      hgvdbal_window rfl rfl)
    { a := sq, b := sig, modulus := n, em := h }

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main where
  localLength _ :=
    (56 + 1 + 71)
      + (numLimbs24 + numLimbs24
          + ((numLimbs24 - 1) * (bigIntParams24.B - 1) + (16 - 1))
          + ((numLimbs24 - 1) * (bigIntParams24.B - 1) + (17 - 1))
          + (2 * numLimbs24 - 1) + (2 * numLimbs24 - 2)
          + GroupedEqXV.widthAllocFrom vparamsFbal.Wf (39 - 2) 0)
      + (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24
            gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14).localLength
          { base := varFromOffset (BigInt numLimbs24) 0, modulus := varFromOffset (BigInt numLimbs24) 0 }
      + (2 * numLimbs24 + ((2 * numLimbs24 - 1) * (bigIntParams24q.B - 1) + (8 - 1))
          + ((2 * numLimbs24 - 1) + ((2 * numLimbs24 - 1) + numLimbs24 - 1) + ((2 * numLimbs24) + numLimbs24 - 2))
          + GroupedEqXV.widthAllocFrom vparamsXbal.Wf (70 - 2) 0)
  localLength_eq := by
    intro input offset
    have hML : ∀ x : Var (ModExpG.Inputs numLimbs24) (F circomPrime),
        (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24
          gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14).localLength x
          = 14 * ModExpSqGT.squareModTLen (m := numLimbs24) bigIntParams24.B bigIntParams24.W 16 17 39 vparamsQbal.Wf :=
      fun _ => rfl
    simp only [main, circuit_norm, Bytes24ToBigInt.circuit, Bytes24ToBigInt.elaborated,
      PadDigest24.circuit, PadDigest24.elaborated, LessThanBytes.circuit, LessThanBytes.elaborated,
      SquareModBalFirstGT.generalCircuit, SquareModBalFirstGT.elaborated,
      ModExpSqGT.generalCircuit, ModExpSqGT.elaborated,
      SqMulModBalTo.generalCircuit, SqMulModBalTo.elaborated, hML]
    ring
  output _ _ := ()
  output_eq := by
    intro input offset
    exact Subsingleton.elim (α := Unit) _ _
  subcircuitsConsistent := by
    intro input offset
    have hMEg : (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14).channelsWithGuarantees = [] := rfl
    have hMEr : (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14).channelsWithRequirements = [] := rfl
    simp +arith only [main, circuit_norm, Bytes24ToBigInt.circuit, Bytes24ToBigInt.elaborated,
      PadDigest24.circuit, PadDigest24.elaborated, LessThanBytes.circuit, LessThanBytes.elaborated,
      SquareModBalFirstGT.generalCircuit, SquareModBalFirstGT.elaborated,
      ModExpSqGT.generalCircuit, ModExpSqGT.elaborated,
      SqMulModBalTo.generalCircuit, SqMulModBalTo.elaborated, hMEg, hMEr]
  channelsLawful := by
    intro input offset
    have hMEg : (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14).channelsWithGuarantees = [] := rfl
    have hMEr : (ModExpSqGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14).channelsWithRequirements = [] := rfl
    simp only [main, circuit_norm, Bytes24ToBigInt.circuit, Bytes24ToBigInt.elaborated,
      PadDigest24.circuit, PadDigest24.elaborated, LessThanBytes.circuit, LessThanBytes.elaborated,
      SquareModBalFirstGT.generalCircuit, SquareModBalFirstGT.elaborated,
      ModExpSqGT.generalCircuit, ModExpSqGT.elaborated,
      SqMulModBalTo.generalCircuit, SqMulModBalTo.elaborated, hMEg, hMEr]

end CircuitDef

/-! ## The four checker obligations -/

theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm,
    Bytes24ToBigInt.circuit, Bytes24ToBigInt.Spec, Bytes24ToBigInt.Assumptions,
    PadDigest24.circuit, PadDigest24.Spec, PadDigest24.Assumptions,
    LessThanBytes.circuit, LessThanBytes.elaborated, LessThanBytes.Assumptions, LessThanBytes.Spec,
    SquareModBalFirstGT.generalCircuit, SquareModBalFirstGT.SoundAssumptions, SquareModBalFirstGT.Spec,
    ModExpSqGT.generalCircuit, ModExpSqGT.Spec, ModExpSqGT.Assumptions,
    SqMulModBalTo.generalCircuit, SqMulModBalTo.Assumptions, SqMulModBalTo.Spec] at h_holds
  obtain ⟨h_n, h_sig, h_pad, h_lt, h_sq1, h_modexp, h_mmt⟩ := h_holds
  refine ⟨?_, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  simp only [Specs.RSASSAPKCS1v15_SHA256_4096_65537.Assumptions,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.algorithm,
    Specs.RSASSAPKCS1v15.Assumptions] at h_assumptions
  obtain ⟨hn_oct, hdig_oct, hsig_oct, hn_bits⟩ := h_assumptions
  set nBI := Vector.map (Expression.eval env) (Bytes24.packLimbs3 input_var_modulus) with hnBI
  set sigBI := Vector.map (Expression.eval env) (Bytes24.packLimbs3 input_var_signature) with hsigBI
  set hBI := Vector.map (Expression.eval env)
    (Bytes24.packLimbs3 (BytesLemmas.emByteExpr input_var_digest)) with hhBI
  obtain ⟨hn_norm, hn_val⟩ := h_n hn_oct
  obtain ⟨hsig_norm, hsig_val⟩ := h_sig hsig_oct
  obtain ⟨hpad_norm, hpad_lt, EM, hEM_enc, hEM_oct, hpad_val⟩ := h_pad hdig_oct
  have hB2 : bigIntParams24.B = 24 := rfl
  have hn_ge : (2 : ℕ) ^ 4095 ≤ BigInt.value 24 nBI := by
    rw [hn_val, show (4095 : ℕ) = Specs.RSASSAPKCS1v15_SHA256_4096_65537.modulusBytesLen * 8 - 1 from by decide]
    exact hn_bits.1
  have hn_lt2 : BigInt.value 24 nBI < 2 ^ 4096 := by
    rw [hn_val]
    have h := SoundnessLemmas.os2ip_lt_pow (fieldBytesToNat input_modulus) hn_oct
    rwa [show (256 : ℕ) ^ 512 = 2 ^ 4096 from by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]] at h
  have hsig_lt4096 : BigInt.value 24 sigBI < 2 ^ 4096 := by
    rw [hsig_val]
    have h := SoundnessLemmas.os2ip_lt_pow (fieldBytesToNat input_signature) hsig_oct
    rwa [show (256 : ℕ) ^ 512 = 2 ^ 4096 from by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]] at h
  have hn_pos : 0 < BigInt.value 24 nBI := lt_of_lt_of_le (Nat.two_pow_pos 4095) hn_ge
  have hsig_lt : BigInt.value 24 sigBI < BigInt.value 24 nBI := by
    rw [hsig_val, hn_val]; exact h_lt ⟨hsig_oct, hn_oct⟩
  have hn4096 : BigInt.value 24 nBI < 2 ^ ((numLimbs24 - 1) * 24 + 16) := by
    rw [show (numLimbs24 - 1) * 24 + 16 = 4096 from by decide]; exact hn_lt2
  have hn_geT : 2 ^ ((numLimbs24 - 1) * 24 + 16 - 1) ≤ BigInt.value 24 nBI := by
    rw [show (numLimbs24 - 1) * 24 + 16 - 1 = 4095 from by decide]; exact hn_ge
  have hsig4096T : BigInt.value 24 sigBI < 2 ^ ((numLimbs24 - 1) * 24 + 16) := by
    rw [show (numLimbs24 - 1) * 24 + 16 = 4096 from by decide]; exact hsig_lt4096
  have hpad_lt_n : BigInt.value 24 hBI < BigInt.value 24 nBI :=
    lt_of_lt_of_le (lt_of_lt_of_le hpad_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num))) hn_ge
  -- first battery
  have hsq1_assum : SquareModBalFirstGT.SoundAssumptions bigIntParams24.B 16
      ({ a := sigBI, modulus := nBI } : SquareModLazy.Inputs numLimbs24 (F circomPrime)) :=
    ⟨by rw [hB2]; exact hsig_norm, by rw [hB2]; exact hn_norm, by rw [hB2]; exact hsig4096T,
     by rw [hB2]; exact hn4096, by rw [hB2]; exact hn_pos, by rw [hB2]; exact hn_geT⟩
  obtain ⟨hsq1_tight, hsq1_val⟩ := h_sq1 hsq1_assum
  rw [hB2] at hsq1_tight hsq1_val
  have hsq1_ltT := BigInt.value_lt_tight (m := numLimbs24) (by decide : (17:ℕ) ≤ 24) hsq1_tight
  -- chain
  have hmodexp_assum : ModExpSqGT.Assumptions bigIntParams24.B 16 17
      ({ base := _, modulus := nBI } : ModExpG.Inputs numLimbs24 (F circomPrime)) :=
    ⟨by rw [hB2]; exact hsq1_tight.1, by rw [hB2]; exact hn_norm,
     by rw [hB2]; exact hsq1_ltT, by rw [hB2]; exact hn4096,
     by rw [hB2]; exact hn_pos, by rw [hB2]; exact hn_geT⟩
  obtain ⟨hsq_tight, hsq_val⟩ := h_modexp hmodexp_assum
  rw [hB2] at hsq_tight hsq_val
  have hsq_ltT := BigInt.value_lt_tight (m := numLimbs24) (by decide : (17:ℕ) ≤ 24) hsq_tight
  -- fused
  have hmmt := h_mmt ⟨by rw [hB2]; exact hsq_tight.1, by rw [hB2]; exact hsig_norm,
    by rw [hB2]; exact hn_norm, by rw [hB2]; exact hpad_norm,
    by rw [hB2]; exact hsq_ltT, by rw [hB2]; exact hsig_lt,
    by rw [hB2]; exact hpad_lt_n, by rw [hB2]; exact hn4096⟩
  rw [hB2] at hmmt
  -- chain the ℤ congruences
  have hchain := zmod_chain hsq1_val hsq_val hmmt
  -- convert to canonical ℕ remainder
  have hchain' : (BigInt.value 24 hBI : ℤ)
      ≡ ((BigInt.value 24 sigBI ^ 65537 : ℕ) : ℤ) [ZMOD (BigInt.value 24 nBI : ℤ)] := by
    refine hchain.trans ?_
    push_cast
    exact Int.ModEq.refl _
  have hrec_nat : BigInt.value 24 hBI = BigInt.value 24 sigBI ^ 65537 % BigInt.value 24 nBI :=
    zmod_to_nat hn_pos hpad_lt_n hchain'
  -- assemble the trusted spec
  have hpow : (Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_signature))
        ^ Specs.RSASSAPKCS1v15_SHA256_4096_65537.publicExponent
        % (Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_modulus))
      = Specs.RSASSAPKCS1v15.os2ip EM := by
    rw [show Specs.RSASSAPKCS1v15_SHA256_4096_65537.publicExponent = 65537 from rfl,
      ← hsig_val, ← hn_val, ← hpad_val]
    exact hrec_nat.symm
  have hsig_lt' : Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_signature)
      < Specs.RSASSAPKCS1v15.os2ip (fieldBytesToNat input_modulus) := by
    rw [← hsig_val, ← hn_val]; exact hsig_lt
  simp only [Specs.RSASSAPKCS1v15_SHA256_4096_65537.Spec,
    Specs.RSASSAPKCS1v15.Spec, Specs.RSASSAPKCS1v15_SHA256_4096_65537.algorithm]
  exact SoundnessLemmas.verifySignature_true _
    (fieldBytesToNat input_modulus) (fieldBytesToNat input_signature)
    (fieldBytesToNat input_digest) EM hsig_lt' hEM_enc hpow hEM_oct

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main ProverAssumptions ProverSpec := by
  circuit_proof_start
  simp only [circuit_norm,
    Bytes24ToBigInt.circuit, Bytes24ToBigInt.Spec, Bytes24ToBigInt.Assumptions,
    PadDigest24.circuit, PadDigest24.Spec, PadDigest24.Assumptions,
    LessThanBytes.circuit, LessThanBytes.elaborated,
    SquareModBalFirstGT.generalCircuit, SquareModBalFirstGT.Assumptions, SquareModBalFirstGT.SoundAssumptions,
    SquareModBalFirstGT.ProverSpec, SquareModBalFirstGT.Spec,
    ModExpSqGT.generalCircuit] at h_env
  simp only [circuit_norm,
    Bytes24ToBigInt.circuit, Bytes24ToBigInt.Assumptions,
    PadDigest24.circuit, PadDigest24.Assumptions,
    LessThanBytes.circuit, LessThanBytes.elaborated, LessThanBytes.Assumptions, LessThanBytes.Spec,
    SquareModBalFirstGT.generalCircuit, SquareModBalFirstGT.SoundAssumptions,
    ModExpSqGT.generalCircuit, ModExpSqGT.ProverAssumptions, ModExpSqGT.Assumptions,
    SqMulModBalTo.generalCircuit, SqMulModBalTo.ProverAssumptions, SqMulModBalTo.Assumptions]
  obtain ⟨h_assum, h_spec⟩ := h_assumptions
  simp only [Assumptions, Spec,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.Assumptions,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.Spec,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.algorithm,
    Specs.RSASSAPKCS1v15_SHA256_4096_65537.publicExponent,
    Specs.RSASSAPKCS1v15.Assumptions, Specs.RSASSAPKCS1v15.Spec] at h_assum h_spec
  obtain ⟨hn_oct, hdig_oct, hsig_oct, hn_bits⟩ := h_assum
  set nBI := Vector.map (Expression.eval env.toEnvironment) (Bytes24.packLimbs3 input_var_modulus) with hnBI
  set sigBI := Vector.map (Expression.eval env.toEnvironment) (Bytes24.packLimbs3 input_var_signature) with hsigBI
  set hBI := Vector.map (Expression.eval env.toEnvironment)
    (Bytes24.packLimbs3 (BytesLemmas.emByteExpr input_var_digest)) with hhBI
  obtain ⟨h_envN, h_envSig, h_envPad, h_envSq1, h_envModExp, h_envExtra⟩ := h_env
  obtain ⟨hn_norm, hn_val⟩ := h_envN hn_oct
  obtain ⟨hsig_norm, hsig_val⟩ := h_envSig hsig_oct
  obtain ⟨hpad_norm, hpad_lt, EM, hEM_enc, hEM_oct, hpad_val⟩ := h_envPad hdig_oct
  have hB2 : bigIntParams24.B = 24 := rfl
  obtain ⟨hlt_os, hpow_os⟩ :=
    MainTheorems.verifySignature_invert (fieldBytesToNat input_modulus)
      (fieldBytesToNat input_signature) (fieldBytesToNat input_digest) EM hEM_enc h_spec
  have hn_ge : (2 : ℕ) ^ 4095 ≤ BigInt.value 24 nBI := by
    rw [hn_val, show (4095 : ℕ) = Specs.RSASSAPKCS1v15_SHA256_4096_65537.modulusBytesLen * 8 - 1 from by decide]
    exact hn_bits.1
  have hn_lt2 : BigInt.value 24 nBI < 2 ^ 4096 := by
    rw [hn_val]
    have h := SoundnessLemmas.os2ip_lt_pow (fieldBytesToNat input_modulus) hn_oct
    rwa [show (256 : ℕ) ^ 512 = 2 ^ 4096 from by rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]] at h
  have hn_pos : 0 < BigInt.value 24 nBI := lt_of_lt_of_le (Nat.two_pow_pos 4095) hn_ge
  have hsig_lt : BigInt.value 24 sigBI < BigInt.value 24 nBI := by rw [hsig_val, hn_val]; exact hlt_os
  have hsig_lt4096 : BigInt.value 24 sigBI < 2 ^ 4096 := lt_trans hsig_lt hn_lt2
  have hn4096 : BigInt.value 24 nBI < 2 ^ ((numLimbs24 - 1) * 24 + 16) := by
    rw [show (numLimbs24 - 1) * 24 + 16 = 4096 from by decide]; exact hn_lt2
  have hn_geT : 2 ^ ((numLimbs24 - 1) * 24 + 16 - 1) ≤ BigInt.value 24 nBI := by
    rw [show (numLimbs24 - 1) * 24 + 16 - 1 = 4095 from by decide]; exact hn_ge
  have hsig4096T : BigInt.value 24 sigBI < 2 ^ ((numLimbs24 - 1) * 24 + 16) := by
    rw [show (numLimbs24 - 1) * 24 + 16 = 4096 from by decide]; exact hsig_lt4096
  have hpad_lt_n : BigInt.value 24 hBI < BigInt.value 24 nBI :=
    lt_of_lt_of_le (lt_of_lt_of_le hpad_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num))) hn_ge
  -- first battery: soundness (VZ(sq1) ≡ sig²) + prover spec (sq1 canonical)
  have hsq1_sound_assum : SquareModBalFirstGT.SoundAssumptions bigIntParams24.B 16
      ({ a := sigBI, modulus := nBI } : SquareModLazy.Inputs numLimbs24 (F circomPrime)) :=
    ⟨by rw [hB2]; exact hsig_norm, by rw [hB2]; exact hn_norm, by rw [hB2]; exact hsig4096T,
     by rw [hB2]; exact hn4096, by rw [hB2]; exact hn_pos, by rw [hB2]; exact hn_geT⟩
  have hsq1_assum : SquareModBalFirstGT.Assumptions bigIntParams24.B 16
      ({ a := sigBI, modulus := nBI } : SquareModLazy.Inputs numLimbs24 (F circomPrime)) :=
    ⟨hsq1_sound_assum, by rw [hB2]; exact hsig_lt⟩
  obtain ⟨h_sq1_spec, hsq1_ge, hsq1_ltN⟩ := h_envSq1 hsq1_assum
  obtain ⟨hsq1_tight, hsq1_val⟩ := h_sq1_spec hsq1_sound_assum
  have hsq1_ltT := BigInt.value_lt_tight (m := numLimbs24) (by decide : (17:ℕ) ≤ bigIntParams24.B) hsq1_tight
  -- chain: soundness (VZ(sq) ≡ VZ(sq1)^(2^14)) + prover spec (sq canonical)
  have hmodexp_sound_assum : ModExpSqGT.Assumptions bigIntParams24.B 16 17
      { base := _, modulus := nBI } :=
    ⟨hsq1_tight.1, hn_norm, hsq1_ltT, hn4096, hn_pos, hn_geT⟩
  have hmodexp_assum : ModExpSqGT.ProverAssumptions bigIntParams24.B 16 17
      { base := _, modulus := nBI } :=
    ⟨hmodexp_sound_assum, hsq1_ge, hsq1_ltN⟩
  obtain ⟨h_modexp_spec, hsq_ge, hsq_ltN⟩ := h_envModExp hmodexp_assum
  obtain ⟨hsq_tight, hsq_val⟩ := h_modexp_spec hmodexp_sound_assum
  have hsq_ltT := BigInt.value_lt_tight (m := numLimbs24) (by decide : (17:ℕ) ≤ bigIntParams24.B) hsq_tight
  -- honest residue: VZ(sq) ≡ sig^32768 (mod n)
  have hsq_sig := zmod_half hsq1_val hsq_val
  -- h.value = sig^65537 mod n
  have h_em_nat : BigInt.value 24 hBI = BigInt.value 24 sigBI ^ 65537 % BigInt.value 24 nBI := by
    rw [hsig_val, hn_val, hpow_os]; exact hpad_val
  have h_em0 : (BigInt.value 24 hBI : ℤ)
      ≡ ((BigInt.value 24 sigBI ^ 65537 : ℕ) : ℤ) [ZMOD (BigInt.value 24 nBI : ℤ)] := by
    have hnm : BigInt.value 24 hBI % BigInt.value 24 nBI
        = BigInt.value 24 sigBI ^ 65537 % BigInt.value 24 nBI := by
      rw [h_em_nat, Nat.mod_mod]
    show (BigInt.value 24 hBI : ℤ) % (BigInt.value 24 nBI : ℤ)
      = ((BigInt.value 24 sigBI ^ 65537 : ℕ) : ℤ) % (BigInt.value 24 nBI : ℤ)
    rw [← Int.natCast_mod, ← Int.natCast_mod]
    exact_mod_cast hnm
  have h_em : (BigInt.value 24 hBI : ℤ)
      ≡ (BigInt.value 24 sigBI : ℤ) ^ 65537 [ZMOD (BigInt.value 24 nBI : ℤ)] := by
    have hcast : ((BigInt.value 24 sigBI ^ 65537 : ℕ) : ℤ) = (BigInt.value 24 sigBI : ℤ) ^ 65537 := by
      push_cast; ring
    rwa [hcast] at h_em0
  -- assemble the goal
  refine ⟨hn_oct, hsig_oct, hdig_oct,
    ⟨⟨hsig_oct, hn_oct⟩, hlt_os⟩,
    hsq1_assum,
    hmodexp_assum,
    ⟨⟨by rw [hB2]; exact hsq_tight.1, by rw [hB2]; exact hsig_norm,
        by rw [hB2]; exact hn_norm, by rw [hB2]; exact hpad_norm,
        by rw [hB2]; exact hsq_ltT, by rw [hB2]; exact hsig_lt,
        by rw [hB2]; exact hpad_lt_n, by rw [hB2]; exact hn4096⟩,
      by rw [hB2]; exact hsq_ge, by rw [hB2]; exact hsq_ltN, ?_⟩⟩
  -- fused prover-assumption spec: h.value ≡ VZ(sq)²·sig (mod n)
  rw [hB2]
  refine h_em.trans ?_
  have hmul := (hsq_sig.mul hsq_sig).mul (Int.ModEq.refl (BigInt.value 24 sigBI : ℤ))
  have hpow : (BigInt.value 24 sigBI : ℤ) ^ 65537
      = (BigInt.value 24 sigBI : ℤ) ^ 32768 * (BigInt.value 24 sigBI : ℤ) ^ 32768
        * (BigInt.value 24 sigBI : ℤ) := by ring
  rw [hpow]
  exact hmul.symm


section Cost

set_option maxHeartbeats 1600000 in
private theorem costIs_main (input : Var Input (F circomPrime)) :
    CostIs (main input) ⟨allocations, constraints⟩ :=
  CostIs.bind (costIs_sub_bytes24ToBigInt _) fun _ =>
  CostIs.bind (costIs_sub_bytes24ToBigInt _) fun _ =>
  CostIs.bind (costIs_sub_padDigest24 _) fun _ =>
  CostIs.bind (GadgetCost.costIs_assertion_lessThanBytes _) fun _ =>
  CostIs.bind (costIs_sub_squareModBalFirstGT bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfFbal posOfFbal 39 vparamsFbal vparamsFbal hgvdFbal hNfFbal _) fun _ =>
  CostIs.bind (costIs_sub_modExpSqGT bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14 _) fun _ =>
  CostIs.bind (costIs_sub_sqMulModBalTo bigIntParams24 bigIntParams24q 24 16 17 8 htq8 htqB8
    htb1_24 htbq24 gfXbal posOfXbal 70 vparamsXbal vparamsXRbal hgvdbal (by norm_num) hlhs_adXbal hrhs_adXbal hgvdbal_window rfl rfl _) fun _ =>
  CostIs.pure _

theorem mainCost :
    Challenge.CostR1CS.circuitCost main ⟨allocations, constraints⟩ :=
  fun input => costIs_main input

set_option maxHeartbeats 800000 in
private theorem isR1CS_main_param (input : Var Input (F circomPrime))
    (hmod : AffineW input.modulus) (hsig : AffineW input.signature)
    (hdig : AffineW input.digest) :
    IsR1CSCirc (main input) := by
  unfold main
  refine IsR1CSCirc.bind_out (isR1CS_sub_bytes24ToBigInt _ hmod) fun nn => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_bytes24ToBigInt _ hsig) fun nsig => ?_
  refine IsR1CSCirc.bind_out (isR1CS_sub_padDigest24 _ hdig) fun nh => ?_
  have hN := affineW_sub_bytes24ToBigInt input.modulus hmod nn
  have hSig := affineW_sub_bytes24ToBigInt input.signature hsig nsig
  have hH := affineW_sub_padDigest24 input.digest hdig nh
  refine IsR1CSCirc.bind (GadgetCost.isR1CS_assertion_lessThanBytes _ hsig hmod) fun _ => ?_
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_squareModBalFirstGT bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfFbal posOfFbal 39 vparamsFbal vparamsFbal hgvdFbal hNfFbal _ hSig hN) fun nsq1 => ?_
  have hSq1 := affineW_sub_squareModBalFirstGT bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfFbal posOfFbal 39 vparamsFbal vparamsFbal hgvdFbal hNfFbal
    { a := (subcircuit Bytes24ToBigInt.circuit input.signature).output nsig,
      modulus := (subcircuit Bytes24ToBigInt.circuit input.modulus).output nn } nsq1
  refine IsR1CSCirc.bind_out
    (isR1CS_sub_modExpSqGT bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14 _ hSq1 hN) fun nrec => ?_
  have hRec := affineW_sub_modExpSqGT bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfQbal posOfQbal 39 vparamsQbal vparamsQRbal hgvdQbal hNfDQbal 14
    { base := (subcircuitWithAssertion
        (SquareModBalFirstGT.generalCircuit bigIntParams24 16 17 htb24 htw24 htbB24sqT htwB24 htbw24 gfFbal posOfFbal 39 vparamsFbal vparamsFbal hgvdFbal hNfFbal)
        { a := (subcircuit Bytes24ToBigInt.circuit input.signature).output nsig,
          modulus := (subcircuit Bytes24ToBigInt.circuit input.modulus).output nn }).output nsq1,
      modulus := (subcircuit Bytes24ToBigInt.circuit input.modulus).output nn } nrec hSq1
  exact isR1CS_sub_sqMulModBalTo bigIntParams24 bigIntParams24q 24 16 17 8 htq8 htqB8
    htb1_24 htbq24 gfXbal posOfXbal 70 vparamsXbal vparamsXRbal hgvdbal (by norm_num) hlhs_adXbal hrhs_adXbal hgvdbal_window rfl rfl _
    hRec hSig hN hH

private theorem affineW_of_modulus {input : Var Input (F circomPrime)}
    (h : Challenge.CostR1CS.AffineProvable input) : AffineW input.modulus := by
  have hw : AffineW (input.modulus ++ (input.digest ++ (input.signature ++
      (#v[] : Vector (Expression (F circomPrime)) 0)))) := by
    intro i hi
    have hb : i < size Input := by
      simp only [circuit_norm, List.sum_cons, List.sum_nil]; omega
    simpa only [circuit_norm, explicit_provable_type, Vector.getElem_cast] using h i hb
  exact hw.left_of_append

private theorem affineW_of_digest {input : Var Input (F circomPrime)}
    (h : Challenge.CostR1CS.AffineProvable input) : AffineW input.digest := by
  have hw : AffineW (input.modulus ++ (input.digest ++ (input.signature ++
      (#v[] : Vector (Expression (F circomPrime)) 0)))) := by
    intro i hi
    have hb : i < size Input := by
      simp only [circuit_norm, List.sum_cons, List.sum_nil]; omega
    simpa only [circuit_norm, explicit_provable_type, Vector.getElem_cast] using h i hb
  exact hw.right_of_append.left_of_append

private theorem affineW_of_signature {input : Var Input (F circomPrime)}
    (h : Challenge.CostR1CS.AffineProvable input) : AffineW input.signature := by
  have hw : AffineW (input.modulus ++ (input.digest ++ (input.signature ++
      (#v[] : Vector (Expression (F circomPrime)) 0)))) := by
    intro i hi
    have hb : i < size Input := by
      simp only [circuit_norm, List.sum_cons, List.sum_nil]; omega
    simpa only [circuit_norm, explicit_provable_type, Vector.getElem_cast] using h i hb
  exact hw.right_of_append.right_of_append.left_of_append

private theorem affineOutput_main (input : Var Input (F circomPrime)) :
    Challenge.CostR1CS.AffineOutput (main input) := by
  intro n i hi
  simp only [circuit_norm] at hi
  omega

theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  Challenge.CostR1CS.isR1CS_of_IsR1CSCirc
    (fun input h => isR1CS_main_param input
      (affineW_of_modulus h) (affineW_of_signature h) (affineW_of_digest h))
    (fun input _ => affineOutput_main input)

end Cost

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
