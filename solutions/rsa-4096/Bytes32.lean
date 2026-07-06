import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesSplitLemmas

/-!
# 32-bit-limb byte packing (`Bytes32`)

At `B = 32` every limb is exactly `4` consecutive bytes — no limb boundary ever
falls inside a byte, so the whole `BytesSplitLemmas` split machinery disappears:
each of the `128` low limbs is the affine combination
`b₀ + 2^8·b₁ + 2^16·b₂ + 2^24·b₃` of four byte expressions, and the `129`-th
(spare) limb is the constant `0`. The packing needs **zero witnesses and zero
constraint rows**: byteness of the inputs is a trusted `Assumption`
(`IsOctetString`), and each limb is `< 2^32` by construction.

`129` limbs (rather than `128`) because the lazy-reduction quotients need
`4097+` bits; the values themselves occupy at most `4096` bits, so the top limb
of every packed input is `0`.

This file provides the pure packing function `packLimbs4` and its
normalization / value / EM lemmas; the affineness (R1CS) lemmas live in
`Cost.lean` with the rest of the cost infrastructure.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace Bytes32

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open BytesLemmas
open BytesSplitLemmas
open Specs.RSASSAPKCS1v15

/-- `2^32` fits the field. -/
theorem two_pow_32_lt_circomPrime : (2 : ℕ) ^ 32 < circomPrime := by decide

/-- Pack `512` big-endian byte expressions into `129` little-endian `32`-bit
limbs: limb `k < 128` is the affine 4-byte combination
`bytes[511−4k] + 2^8·bytes[511−(4k+1)] + 2^16·bytes[511−(4k+2)] + 2^24·bytes[511−(4k+3)]`
(little-endian byte order inside the limb), and the top (spare) limb is the
constant `0`. -/
def packLimbs4 (bytes : Vector (Expression (F circomPrime)) 512) :
    Var (BigInt 129) (F circomPrime) :=
  Vector.ofFn fun k : Fin 129 =>
    if _h : k.val < 128 then
      bytes[511 - 4 * k.val]'(by omega)
        + bytes[511 - (4 * k.val + 1)]'(by omega) * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + bytes[511 - (4 * k.val + 2)]'(by omega) * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime)
        + bytes[511 - (4 * k.val + 3)]'(by omega) * (((2 : ℕ) ^ 24 : ℕ) : F circomPrime)
    else 0

/-- The value of packed limb `k < 128` is the little-endian 4-byte sum (no field
wraparound: the sum is `< 2^32 < p`). -/
theorem packLimbs4_limb_val (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256)
    (k : ℕ) (hk : k < 128) :
    (Expression.eval env ((packLimbs4 bytes)[k]'(by omega))).val
      = byteVal env bytes (4 * k) + byteVal env bytes (4 * k + 1) * 2 ^ 8
        + byteVal env bytes (4 * k + 2) * 2 ^ 16
        + byteVal env bytes (4 * k + 3) * 2 ^ 24 := by
  unfold packLimbs4
  rw [Vector.getElem_ofFn]
  rw [dif_pos hk]
  set A := Expression.eval env (bytes[511 - 4 * k]'(by omega)) with hA
  set B := Expression.eval env (bytes[511 - (4 * k + 1)]'(by omega)) with hB
  set C := Expression.eval env (bytes[511 - (4 * k + 2)]'(by omega)) with hC
  set D := Expression.eval env (bytes[511 - (4 * k + 3)]'(by omega)) with hD
  have hAv : byteVal env bytes (4 * k) = A.val := rfl
  have hBv : byteVal env bytes (4 * k + 1) = B.val := rfl
  have hCv : byteVal env bytes (4 * k + 2) = C.val := rfl
  have hDv : byteVal env bytes (4 * k + 3) = D.val := rfl
  have hAlt : A.val < 256 := by rw [← hAv]; exact hbytes _ (by omega)
  have hBlt : B.val < 256 := by rw [← hBv]; exact hbytes _ (by omega)
  have hClt : C.val < 256 := by rw [← hCv]; exact hbytes _ (by omega)
  have hDlt : D.val < 256 := by rw [← hDv]; exact hbytes _ (by omega)
  have heval : Expression.eval env
      (bytes[511 - 4 * k]'(by omega)
        + bytes[511 - (4 * k + 1)]'(by omega) * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + bytes[511 - (4 * k + 2)]'(by omega) * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime)
        + bytes[511 - (4 * k + 3)]'(by omega) * (((2 : ℕ) ^ 24 : ℕ) : F circomPrime))
      = A + B * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + C * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime)
        + D * (((2 : ℕ) ^ 24 : ℕ) : F circomPrime) := by
    simp only [Expression.eval]
    rw [hA, hB, hC, hD]
  rw [heval]
  have hcast : A + B * (((2 : ℕ) ^ 8 : ℕ) : F circomPrime)
        + C * (((2 : ℕ) ^ 16 : ℕ) : F circomPrime)
        + D * (((2 : ℕ) ^ 24 : ℕ) : F circomPrime)
      = ((A.val + B.val * 2 ^ 8 + C.val * 2 ^ 16 + D.val * 2 ^ 24 : ℕ) : F circomPrime) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
  rw [hcast, hAv, hBv, hCv, hDv]
  exact val_natCast_lt' (lt_of_lt_of_le (by
    show A.val + B.val * 2 ^ 8 + C.val * 2 ^ 16 + D.val * 2 ^ 24 < 2 ^ 32
    simp only [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 16 = 65536 from rfl,
      show (2 : ℕ) ^ 24 = 16777216 from rfl, show (2 : ℕ) ^ 32 = 4294967296 from rfl]
    omega) two_pow_32_lt_circomPrime.le)

/-- The top (spare) limb evaluates to `0`. -/
theorem packLimbs4_top_val (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512) :
    (Expression.eval env ((packLimbs4 bytes)[128]'(by omega))).val = 0 := by
  unfold packLimbs4
  rw [Vector.getElem_ofFn]
  rw [dif_neg (by omega : ¬ (128 : ℕ) < 128)]
  simp [circuit_norm]

/-- The packed limbs are normalized (`< 2^32`) whenever the bytes are bytes. -/
theorem packLimbs4_normalized (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    BigInt.Normalized 32 (Vector.map (Expression.eval env) (packLimbs4 bytes)) := by
  intro i
  rw [Fin.getElem_fin, Vector.getElem_map]
  rcases Nat.lt_or_ge i.val 128 with hi | hi
  · rw [packLimbs4_limb_val env bytes hbytes i.val hi]
    have h0 := hbytes (4 * i.val) (by omega)
    have h1 := hbytes (4 * i.val + 1) (by omega)
    have h2 := hbytes (4 * i.val + 2) (by omega)
    have h3 := hbytes (4 * i.val + 3) (by omega)
    simp only [show (2 : ℕ) ^ 8 = 256 from rfl, show (2 : ℕ) ^ 16 = 65536 from rfl,
      show (2 : ℕ) ^ 24 = 16777216 from rfl, show (2 : ℕ) ^ 32 = 4294967296 from rfl]
    omega
  · have hi' : i.val = 128 := by have := i.isLt; omega
    rw [getElem_congr_idx hi', packLimbs4_top_val env bytes]
    exact Nat.two_pow_pos 32

/-- Sum of four terms as a `range 4` sum. -/
private theorem sum_range_four (g : ℕ → ℕ) :
    (∑ j ∈ Finset.range 4, g j) = g 0 + g 1 + g 2 + g 3 := by
  simp [Finset.sum_range_succ]

/-- **Regrouping**: 4-byte limbs at base `2^32` recompose the base-`2^8` byte sum. -/
theorem four_byte_regroup (f : ℕ → ℕ) :
    ∀ n, (∑ k ∈ Finset.range n,
          (∑ j ∈ Finset.range 4, f (4 * k + j) * 2 ^ (8 * j)) * 2 ^ (32 * k))
      = ∑ je ∈ Finset.range (4 * n), f je * 2 ^ (8 * je) := by
  intro n
  induction n with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, sum_range_four]
    rw [show 4 * (t + 1) = 4 * t + 1 + 1 + 1 + 1 from by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have e0 : 8 * (4 * t) = 8 * 0 + 32 * t := by ring
    have e1 : 8 * (4 * t + 1) = 8 * 1 + 32 * t := by ring
    have e2 : 8 * (4 * t + 1 + 1) = 8 * 2 + 32 * t := by ring
    have e3 : 8 * (4 * t + 1 + 1 + 1) = 8 * 3 + 32 * t := by ring
    have a1 : 4 * t + 1 + 1 = 4 * t + 2 := by ring
    have a2 : 4 * t + 1 + 1 + 1 = 4 * t + 3 := by ring
    rw [e0, e1, e2, e3, a1, a2, pow_add, pow_add, pow_add, pow_add]
    ring

/-- **Value.** The packed big integer denotes the little-endian base-`2^8` byte
sum. -/
theorem packLimbs4_value (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    BigInt.value 32 (Vector.map (Expression.eval env) (packLimbs4 bytes))
      = ∑ je ∈ Finset.range 512, byteVal env bytes je * 2 ^ (8 * je) := by
  set L : ℕ → ℕ := fun k =>
    if h : k < 129 then ((Vector.map (Expression.eval env) (packLimbs4 bytes))[k]'h).val else 0
    with hL
  have hval : BigInt.value 32 (Vector.map (Expression.eval env) (packLimbs4 bytes))
      = ∑ k ∈ Finset.range 129, L k * 2 ^ (32 * k) := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun k => L k * 2 ^ (32 * k))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hL, dif_pos i.isLt, Fin.getElem_fin]
  rw [hval, show (129 : ℕ) = 128 + 1 from rfl, Finset.sum_range_succ]
  have hLtop : L 128 = 0 := by
    simp only [hL, dif_pos (show (128 : ℕ) < 129 by omega)]
    rw [Vector.getElem_map]
    exact packLimbs4_top_val env bytes
  rw [hLtop, Nat.zero_mul, Nat.add_zero]
  have hlow : (∑ k ∈ Finset.range 128, L k * 2 ^ (32 * k))
      = ∑ k ∈ Finset.range 128,
          (∑ j ∈ Finset.range 4, byteVal env bytes (4 * k + j) * 2 ^ (8 * j)) * 2 ^ (32 * k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    congr 1
    simp only [hL, dif_pos (show k < 129 by omega)]
    rw [Vector.getElem_map, packLimbs4_limb_val env bytes hbytes k hk, sum_range_four]
    norm_num
  rw [hlow, four_byte_regroup]

/-- **`os2ip` form of the value**: packing recovers `os2ip` of the evaluated
bytes. -/
theorem packLimbs4_value_eq_os2ip (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (hbytes : ∀ je, je < 512 → byteVal env bytes je < 256) :
    BigInt.value 32 (Vector.map (Expression.eval env) (packLimbs4 bytes))
      = os2ip (Vector.map (fun e => (Expression.eval env e).val) bytes) := by
  rw [packLimbs4_value env bytes hbytes, os2ip_vec_eq_sum_le]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  congr 1
  rw [getElem!_pos _ (511 - k) (by omega), Vector.getElem_map]
  rfl

/-! ## EM (PKCS#1-v1_5) packing lemmas -/

/-- The top EM byte (big-endian byte `0`) is the constant `0x00`. -/
theorem em_top_byte_zero (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32) :
    byteVal env (emByteExpr digBytes) 511 = 0 := by
  rw [em_byteVal_const env digBytes 511 (by omega)]
  decide

/-- The packed EM value is `< 2^4088` (its top byte is `0x00`). -/
theorem packLimbs4_em_value_lt (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (hoct : ∀ (dj : ℕ) (hdj : dj < 32), (Expression.eval env (digBytes[dj]'hdj)).val < 256) :
    BigInt.value 32 (Vector.map (Expression.eval env) (packLimbs4 (emByteExpr digBytes)))
      < 2 ^ 4088 := by
  rw [packLimbs4_value env _ (em_bytes_lt env digBytes hoct)]
  rw [show (512 : ℕ) = 511 + 1 from rfl, Finset.sum_range_succ,
    em_top_byte_zero env digBytes, Nat.zero_mul, Nat.add_zero]
  have h := sum_range_lt_pow (B := 8) (n := 511)
    (fun je => byteVal env (emByteExpr digBytes) je)
    (fun i hi => em_bytes_lt env digBytes hoct i (by omega))
  rwa [show 8 * 511 = 4088 from rfl] at h

/-- The packed EM value equals `os2ip (emVec dnat)` for the evaluated digest
bytes `dnat`. -/
theorem packLimbs4_em_value_eq (env : Environment (F circomPrime))
    (digBytes : Vector (Expression (F circomPrime)) 32)
    (hoct : ∀ (dj : ℕ) (hdj : dj < 32), (Expression.eval env (digBytes[dj]'hdj)).val < 256) :
    BigInt.value 32 (Vector.map (Expression.eval env) (packLimbs4 (emByteExpr digBytes)))
      = os2ip (emVec (Vector.map (fun e => (Expression.eval env e).val) digBytes)) := by
  rw [packLimbs4_value_eq_os2ip env _ (em_bytes_lt env digBytes hoct),
    emByteExpr_eval_eq_EM env digBytes]

end Bytes32
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
