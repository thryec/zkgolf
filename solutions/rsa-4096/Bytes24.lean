import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesSplitLemmas

/-!
# 24-bit-limb byte packing (`Bytes24`)

At `B = 24` every limb is exactly `3` consecutive bytes — no limb boundary ever
falls inside a byte, so the whole `BytesSplitLemmas` split machinery disappears:
each of the `170` low limbs is the affine combination
`b₀ + 2^8·b₁ + 2^16·b₂` of three byte expressions, and the `171`-st (top) limb
is the 2-byte affine combination `b₀ + 2^8·b₁` (bytes `510` and `511` in
little-endian order — real data, unlike the `B = 32` zero spare limb). The
packing needs **zero witnesses and zero constraint rows**: byteness of the
inputs is a trusted `Assumption` (`IsOctetString`), and each limb is `< 2^24`
by construction (the top limb even `< 2^16`).

This file provides the pure packing function `packLimbs3` and its
normalization / value / EM lemmas; the affineness (R1CS) lemma lives in
`Bytes24Circuits.lean` with the rest of the zero-cost wrappers.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace Bytes24

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open BytesLemmas
open BytesSplitLemmas
open Specs.RSASSAPKCS1v15

/-- `2^24` fits the field. -/
theorem two_pow_24_lt_circomPrime : (2 : ℕ) ^ 24 < circomPrime := by decide

/-- Pack `512` big-endian byte expressions into `171` little-endian `24`-bit
limbs: limb `k < 170` is the affine 3-byte combination
`bytes[511−3k] + 2^8·bytes[511−(3k+1)] + 2^16·bytes[511−(3k+2)]`
(little-endian byte order inside the limb), and the top limb is the 2-byte
combination `bytes[511−510] + 2^8·bytes[511−511]`. -/
def packLimbs3 (bytes : Vector (Expression (F circomPrime)) 512) :
    Var (BigInt 171) (F circomPrime) :=
  Vector.ofFn fun k : Fin 171 =>
    if _h : k.val < 170 then
      bytes[511 - 3 * k.val]'(by omega)
        + bytes[511 - (3 * k.val + 1)]'(by omega) * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + bytes[511 - (3 * k.val + 2)]'(by omega) * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime)
    else
      bytes[511 - 510]'(by omega)
        + bytes[511 - 511]'(by omega) * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)

/-- The value of packed limb `k < 170` is the little-endian 3-byte sum (no field
wraparound: the sum is `< 2^24 < p`). -/
theorem packLimbs3_limb_val (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (k : ℕ) (hk : k < 170) :
    (Expression.eval env ((packLimbs3 bytes)[k]'(by omega))).val
      = byteVal env bytes (3 * k) + byteVal env bytes (3 * k + 1) * 2 ^ 8
        + byteVal env bytes (3 * k + 2) * 2 ^ 16 := by
  unfold packLimbs3
  rw [Vector.getElem_ofFn]
  rw [dif_pos hk]
  set A := Expression.eval env (bytes[511 - 3 * k]'(by omega)) with hA
  set B := Expression.eval env (bytes[511 - (3 * k + 1)]'(by omega)) with hB
  set C := Expression.eval env (bytes[511 - (3 * k + 2)]'(by omega)) with hC
  have hAv : byteVal env bytes (3 * k) = A.val := rfl
  have hBv : byteVal env bytes (3 * k + 1) = B.val := rfl
  have hCv : byteVal env bytes (3 * k + 2) = C.val := rfl
  have hAlt : A.val < 256 := by rw [← hAv]; exact hbytes _ (by omega)
  have hBlt : B.val < 256 := by rw [← hBv]; exact hbytes _ (by omega)
  have hClt : C.val < 256 := by rw [← hCv]; exact hbytes _ (by omega)
  have heval : Expression.eval env
      (bytes[511 - 3 * k]'(by omega)
        + bytes[511 - (3 * k + 1)]'(by omega) * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + bytes[511 - (3 * k + 2)]'(by omega) * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime))
      = A + B * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + C * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime) := by
    simp only [Expression.eval]
    rw [hA, hB, hC]
  rw [heval]
  have hcast : A + B * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + C * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime)
      = ((A.val + B.val * 2 ^ 8 + C.val * 2 ^ 16 : ℕ) : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hcast, hAv, hBv, hCv]
  exact val_natCast_lt' (lt_of_lt_of_le (by
    show A.val + B.val * 2 ^ 8 + C.val * 2 ^ 16 < 2 ^ 24
    simp only [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 16 = 65536 from rfl,
      show (2 : ℕ) ^ 24 = 16777216 from rfl]
    omega) two_pow_24_lt_circomPrime.le)

/-- The value of the top limb is the little-endian 2-byte sum of bytes `510`
and `511` (no field wraparound: the sum is `< 2^16 < p`). -/
theorem packLimbs3_top_val (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    (Expression.eval env ((packLimbs3 bytes)[170]'(by omega))).val
      = byteVal env bytes 510 + byteVal env bytes 511 * 2 ^ 8 := by
  unfold packLimbs3
  rw [Vector.getElem_ofFn]
  rw [dif_neg (by omega : ¬ (170 : ℕ) < 170)]
  set A := Expression.eval env (bytes[511 - 510]'(by omega)) with hA
  set B := Expression.eval env (bytes[511 - 511]'(by omega)) with hB
  have hAv : byteVal env bytes 510 = A.val := rfl
  have hBv : byteVal env bytes 511 = B.val := rfl
  have hAlt : A.val < 256 := by rw [← hAv]; exact hbytes _ (by omega)
  have hBlt : B.val < 256 := by rw [← hBv]; exact hbytes _ (by omega)
  have heval : Expression.eval env
      (bytes[511 - 510]'(by omega)
        + bytes[511 - 511]'(by omega) * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime))
      = A + B * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime) := by
    simp only [Expression.eval]
    rw [hA, hB]
  rw [heval]
  have hcast : A + B * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
      = ((A.val + B.val * 2 ^ 8 : ℕ) : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [hcast, hAv, hBv]
  exact val_natCast_lt' (lt_of_lt_of_le (by
    show A.val + B.val * 2 ^ 8 < 2 ^ 24
    simp only [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 24 = 16777216 from rfl]
    omega) two_pow_24_lt_circomPrime.le)

/-- The packed limbs are normalized (`< 2^24`) whenever the bytes are bytes. -/
theorem packLimbs3_normalized (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    BigInt.Normalized 24 (Vector.map (Expression.eval env) (packLimbs3 bytes)) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_map]
  rcases Nat.lt_or_ge i.val 170 with hi | hi
  · rw [packLimbs3_limb_val env bytes hbytes i.val hi]
    have h0 := hbytes (3 * i.val) (by omega)
    have h1 := hbytes (3 * i.val + 1) (by omega)
    have h2 := hbytes (3 * i.val + 2) (by omega)
    simp only [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 16 = 65536 from rfl,
      show (2 : ℕ) ^ 24 = 16777216 from rfl]
    omega
  · have hi' : i.val = 170 := by have := i.isLt; omega
    rw [getElem_congr_idx hi', packLimbs3_top_val env bytes hbytes]
    have h0 := hbytes 510 (by omega)
    have h1 := hbytes 511 (by omega)
    simp only [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 24 = 16777216 from rfl]
    omega

/-- Sum of three terms as a `range 3` sum. -/
private theorem sum_range_three (g : ℕ → ℕ) :
    (∑ j ∈ Finset.range 3, g j) = g 0 + g 1 + g 2 := by
  simp [Finset.sum_range_succ]

/-- **Regrouping**: 3-byte limbs at base `2^24` recompose the base-`2^8` byte sum. -/
theorem three_byte_regroup (f : ℕ → ℕ) :
    ∀ n, (∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range 3, f (3 * k + j) * 2 ^ (8 * j)) * 2 ^ (24 * k))
      = ∑ je ∈ Finset.range (3 * n), f je * 2 ^ (8 * je) := by
  intro n
  induction n with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, sum_range_three]
    rw [show 3 * (t + 1) = 3 * t + 1 + 1 + 1 from by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    have e0 : 8 * (3 * t) = 8 * 0 + 24 * t := by ring
    have e1 : 8 * (3 * t + 1) = 8 * 1 + 24 * t := by ring
    have e2 : 8 * (3 * t + 1 + 1) = 8 * 2 + 24 * t := by ring
    have a1 : 3 * t + 1 + 1 = 3 * t + 2 := by ring
    rw [e0, e1, e2, a1, pow_add, pow_add, pow_add]
    simp only [Nat.add_zero]
    ring

/-- **Value.** The packed big integer denotes the little-endian base-`2^8` byte
sum. -/
theorem packLimbs3_value (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    BigInt.value 24 (Vector.map (Expression.eval env) (packLimbs3 bytes))
      = ∑ je ∈ Finset.range 512, byteVal env bytes je * 2 ^ (8 * je) := by
  set L : ℕ → ℕ := fun k =>
    if h : k < 171 then ((Vector.map (Expression.eval env) (packLimbs3 bytes))[k]'h).val else 0
    with hL
  have hval : BigInt.value 24 (Vector.map (Expression.eval env) (packLimbs3 bytes))
      = ∑ k ∈ Finset.range 171, L k * 2 ^ (24 * k) := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => L k * 2 ^ (24 * k))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hL, dif_pos i.isLt, Fin.getElem_fin]
  rw [hval, show (171 : ℕ) = 170 + 1 from rfl, Finset.sum_range_succ]
  have hLtop : L 170 = byteVal env bytes 510 + byteVal env bytes 511 * 2 ^ 8 := by
    simp only [hL, dif_pos (show (170 : ℕ) < 171 by omega)]
    rw [Vector.getElem_map]
    exact packLimbs3_top_val env bytes hbytes
  rw [hLtop]
  have hlow : (∑ k ∈ Finset.range 170, L k * 2 ^ (24 * k))
      = ∑ k ∈ Finset.range 170,
          (∑ j ∈ Finset.range 3, byteVal env bytes (3 * k + j) * 2 ^ (8 * j)) * 2 ^ (24 * k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    congr 1
    simp only [hL, dif_pos (show k < 171 by omega)]
    rw [Vector.getElem_map, packLimbs3_limb_val env bytes hbytes k hk, sum_range_three]
    norm_num
  rw [hlow, three_byte_regroup]
  have hsplit : (∑ je ∈ Finset.range 512, byteVal env bytes je * 2 ^ (8 * je))
      = (∑ je ∈ Finset.range 510, byteVal env bytes je * 2 ^ (8 * je))
        + byteVal env bytes 510 * 2 ^ (8 * 510)
        + byteVal env bytes 511 * 2 ^ (8 * 511) := by
    rw [show (512 : ℕ) = 511 + 1 from rfl, Finset.sum_range_succ,
      show (511 : ℕ) = 510 + 1 from rfl, Finset.sum_range_succ]
  rw [hsplit, show (3 * 170 : ℕ) = 510 from by norm_num,
    show (2 : ℕ) ^ (8 * 510) = 2 ^ (24 * 170) from by
      rw [show 8 * 510 = 24 * 170 from by norm_num],
    show (2 : ℕ) ^ (8 * 511) = 2 ^ 8 * 2 ^ (24 * 170) from by rw [← pow_add]]
  rw [Nat.add_mul, Nat.mul_assoc, ← Nat.add_assoc]

/-- **`os2ip` form of the value**: packing recovers `os2ip` of the evaluated
bytes. -/
theorem packLimbs3_value_eq_os2ip (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    BigInt.value 24 (Vector.map (Expression.eval env) (packLimbs3 bytes))
      = os2ip (Vector.map (fun e => (Expression.eval env e).val) bytes) := by
  rw [packLimbs3_value env bytes hbytes, os2ip_vec_eq_sum_le]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  congr 1
  rw [getElem!_pos _ (511 - k) (by omega), Vector.getElem_map]
  rfl

/-! ## EM (PKCS#1-v1_5) packing lemmas -/

/-- The packed EM value is `< 2^4088` (its top byte is `0x00`). -/
theorem packLimbs3_em_value_lt (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (hoct : ∀ (dj : ℕ) (hdj : dj < 32), (Expression.eval env (digBytes[dj]'hdj)).val < 256) :
    BigInt.value 24 (Vector.map (Expression.eval env) (packLimbs3 (emByteExpr digBytes)))
      < 2 ^ 4088 := by
  rw [packLimbs3_value env _ (em_bytes_lt env digBytes hoct)]
  exact em_byte_sum_lt env digBytes hoct

/-- The packed EM value equals `os2ip (emVec dnat)` for the evaluated digest
bytes `dnat`. -/
theorem packLimbs3_em_value_eq (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (hoct : ∀ (dj : ℕ) (hdj : dj < 32), (Expression.eval env (digBytes[dj]'hdj)).val < 256) :
    BigInt.value 24 (Vector.map (Expression.eval env) (packLimbs3 (emByteExpr digBytes)))
      = os2ip (emVec (Vector.map (fun e => (Expression.eval env e).val) digBytes)) := by
  rw [packLimbs3_value_eq_os2ip env _ (em_bytes_lt env digBytes hoct),
    emByteExpr_eval_eq_EM env digBytes]

end Bytes24
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
