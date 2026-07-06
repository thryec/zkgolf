import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Theorems
import Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface

/-!
# Byte ↔ bit ↔ limb glue for the RSASSA-PKCS1-v1_5 / SHA256 / 4096 instance

Pure helper definitions (no proofs) used by `Main.lean` to bridge the byte-vector
`Input` of the trusted Challenge interface to the big-integer (`BigInt 34`)
inputs of the verified RSA core (`ModExp`, `LessThan`, `Equal`).

## Conventions

The byte vectors of the interface are **big-endian**: index `0` is the most
significant byte. For a `modulusBytesLen = 512`-byte vector the global bit index
`p ∈ [0, 4096)` of byte `j` (with `j = 0` the MSB), bit `t ∈ [0,8)` (the `2^t`
place of byte `j`) is

  `bitIndexOfByte j t = 8 * (511 - j) + t`.

Hence the integer denoted is `Σ_p bit[p] · 2^p` (little-endian over bits), and
each limb `k ∈ [0,34)` collects the 121 bits `[121·k, 121·k + 121)` (clamped to
`< 4096`), as an affine `Expression`:

  `limb_k = Σ_{t, 121·k+t < 4096, t < 121} bit[121·k + t] · 2^t`.

Limbs `0..32` are full 121-bit limbs (covering bits `0..3992`); limb `33` holds
the top 103 bits (`3993..4095`). Each limb is `< 2^121` by construction.

The EM (encoded message) for PKCS#1-v1_5 is also a 512-byte big-endian vector;
its low 256 bits are exactly the SHA-256 digest bits, the rest are the constant
DigestInfo/padding prefix.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace Bytes

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537

/-- Number of 121-bit limbs. -/
@[reducible] def numLimbs : ℕ := 34

/-- The limb width `B` (bits per limb). -/
@[reducible] def limbBits : ℕ := 121

/-- Total bit width covered by the modulus/signature/EM (`4096`). -/
@[reducible] def totalBits : ℕ := 4096

/-! ## Index helpers -/

/-- Global bit index of bit `t` of big-endian byte `j` (byte `0` = MSB), in a
`512`-byte (`4096`-bit) vector. -/
@[reducible] def bitIndexOfByte (j t : ℕ) : ℕ := 8 * (511 - j) + t

/-- Global bit index of bit `t` of big-endian digest byte `dj` (`dj = 0` = MSB),
within the low `256` digest bits. The 32 digest bytes occupy bits `[0, 256)`
exactly (least significant digest byte = digest byte 31). -/
@[reducible] def digestBitIndex (dj t : ℕ) : ℕ := 8 * (31 - dj) + t

/-! ## Byte reconstruction helper -/

/-- The affine expression `Σ_{t<8} bits[base + t] · 2^t` reconstructing the byte
value at flat bit offset `base`. Requires `base + 8 ≤ n`. Used to wire byte/bit
consistency in the `ByteBlock` assertion and to recompose limbs in
`BytesLemmas`. -/
def byteFromBits {n : ℕ} (bits : Vector (Expression (F circomPrime)) n)
    (base : ℕ) : Expression (F circomPrime) :=
  Fin.foldl 8 (fun acc t =>
    acc +
      (if h : base + t.val < n then bits[base + t.val]'h else 0) *
        (((2 ^ t.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-! ## Limb packing -/

/-- Pack a `totalBits`-bit boolean expression vector into a `BigInt 34` of
affine limbs: limb `k = Σ_{t<121, 121·k+t<4096} bits[121·k + t] · 2^t`. -/
def packLimbs (bits : Vector (Expression (F circomPrime)) totalBits) :
    Var (BigInt numLimbs) (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    Fin.foldl limbBits (fun acc t =>
      let p : ℕ := limbBits * k.val + t.val
      acc +
        (if h : p < totalBits then bits[p]'h else 0) *
          (((2 ^ t.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-! ## PKCS#1-v1_5 encoded-message (EM) constant prefix

EM is a 512-byte big-endian octet string:

* byte 0   = 0x00
* byte 1   = 0x01
* bytes 2..459   = 0xff   (458 bytes)
* byte 460 = 0x00
* bytes 461..479 = SHA-256 DER DigestInfo prefix (19 bytes):
    `30 31 30 0d 06 09 60 86 48 01 65 03 04 02 01 05 00 04 20`
* bytes 480..511 = the 32 digest bytes (the variable part).

The digest occupies the low 256 bits `[0,256)`; everything else is constant. -/

/-- The 19-byte SHA-256 DER DigestInfo prefix. -/
def derPrefix : Vector ℕ 19 :=
  #v[0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
     0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20]

/-- The constant EM byte value at big-endian byte index `j ∈ [0,512)`, for the
non-digest positions. (Digest positions `j ∈ [480,512)` are handled separately
by wiring in the digest bits; the value returned here for those positions is
`0` and is unused.) -/
def emByteConst (j : ℕ) : ℕ :=
  if j = 0 then 0x00
  else if j = 1 then 0x01
  else if 2 ≤ j ∧ j ≤ 459 then 0xff
  else if j = 460 then 0x00
  else if 461 ≤ j ∧ j ≤ 479 then (if h : j - 461 < 19 then derPrefix[j - 461] else 0)
  else 0

/-- The constant EM bit value at global bit index `p ∈ [0,4096)` for the
non-digest positions (`p ≥ 256`): bit `p % 8` of the constant EM byte
`511 - p / 8`. For `p < 256` the value is `0` (those bits come from the digest
and are wired in separately). -/
def emConstBit (p : ℕ) : F circomPrime :=
  if p < 256 then 0
  else
    let j : ℕ := 511 - p / 8
    let t : ℕ := p % 8
    ((emByteConst j / 2 ^ t % 2 : ℕ) : F circomPrime)

/-- Build the `4096`-bit EM expression vector: bits `[0,256)` are the digest bits
`digBits`, bits `[256,4096)` are the constant prefix bits `emConstBit`. -/
def emBits (digBits : Vector (Expression (F circomPrime)) 256) :
    Vector (Expression (F circomPrime)) totalBits :=
  Vector.ofFn fun p : Fin totalBits =>
    if h : p.val < 256 then digBits[p.val]'h
    else (Expression.const (emConstBit p.val))

/-! ## Byte-split affine limb packing

The trusted `Assumptions` already guarantee every input byte is `< 256`
(`IsOctetString`), so re-proving byteness bit by bit is wasted work. Instead,
each limb is built as an **affine** combination of whole input bytes; witnesses
are needed only where a limb boundary `121·k` falls strictly inside a byte.

Since `121 ≡ 1 (mod 8)`, boundary `k ∈ [1, 34)` is byte-aligned iff `8 ∣ k`;
the other `29` boundaries straddle a byte. For each straddling boundary the
straddled byte `y` is split as `y = hi·2^t + lo` (`t = 121·k mod 8`): the low
`7` bits of `y` are witnessed and its top bit is the implicit affine expression
`2⁻⁷·(y − Σ bits·2^i)` (the `RangeCheck` trick), so a split costs `7` witnesses
and `8` booleanity rows. `lo`/`hi` are affine in the witnessed bits and are
placed in the two adjacent limbs; all other bytes contribute to exactly one
limb as `byte·2^offset`. -/

/-- The boundary index of split `s ∈ [0, 29)` (the `s`-th `k ∈ [1,34)` with
`k % 8 ≠ 0`). -/
@[reducible] def splitBoundary (s : ℕ) : ℕ := s + s / 7 + 1

/-- The split index of a straddling boundary `k` (inverse of `splitBoundary`). -/
@[reducible] def splitIdx (k : ℕ) : ℕ := k - 1 - (k - 1) / 8

/-- Little-endian index of the byte containing bit `121·k` (the byte straddled
by boundary `k`, when `121·k % 8 ≠ 0`). -/
@[reducible] def splitByteLE (k : ℕ) : ℕ := 121 * k / 8

/-- First little-endian byte index whose start bit `8·je` is `≥ 121·k`. -/
@[reducible] def startByte (k : ℕ) : ℕ := (121 * k + 7) / 8

/-- The affine recomposition `Σ_{i<7} bits[7·s+i]·2^i` of split `s`'s seven
witnessed low bits. -/
def splitLowSum {nb : ℕ} (bits : Vector (Expression (F circomPrime)) nb) (s : ℕ) :
    Expression (F circomPrime) :=
  Fin.foldl 7 (fun acc i =>
    acc + (if h : 7 * s + i.val < nb then bits[7 * s + i.val]'h else 0)
      * (((2 ^ i.val : ℕ) : F circomPrime) : Expression (F circomPrime))) 0

/-- The implicit top bit of split `s`'s straddled byte:
`2⁻⁷ · (byte − Σ_{i<7} bits[7·s+i]·2^i)`. Boolean-constraining this expression
both enforces the recomposition and bounds the byte by `256`. -/
def splitTop {nb : ℕ} (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb) (s : ℕ) :
    Expression (F circomPrime) :=
  Expression.const ((((2 ^ 7 : ℕ) : F circomPrime))⁻¹) *
    (bytes[511 - splitByteLE (splitBoundary s)]'(by omega) - splitLowSum bits s)

/-- The low piece of the byte straddled by boundary `k`: the affine sum
`Σ_{i < t} bits[7·splitIdx k + i]·2^i` (`t = 121·k mod 8`). -/
def splitLoExpr {nb : ℕ} (bits : Vector (Expression (F circomPrime)) nb) (k : ℕ) :
    Expression (F circomPrime) :=
  Fin.foldl 7 (fun acc i =>
    acc + (if h : i.val < 121 * k % 8 ∧ 7 * splitIdx k + i.val < nb then
        bits[7 * splitIdx k + i.val]'h.2
          * (((2 ^ i.val : ℕ) : F circomPrime) : Expression (F circomPrime))
      else 0)) 0

/-- The high piece of the byte straddled by boundary `k`: the affine sum
`Σ_{t ≤ i < 7} bits[7·splitIdx k + i]·2^(i−t) + top·2^(7−t)`. -/
def splitHiExpr {nb : ℕ} (bytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) nb) (k : ℕ) :
    Expression (F circomPrime) :=
  Fin.foldl 7 (fun acc i =>
    acc + (if h : 121 * k % 8 ≤ i.val ∧ 7 * splitIdx k + i.val < nb then
        bits[7 * splitIdx k + i.val]'h.2
          * (((2 ^ (i.val - 121 * k % 8) : ℕ) : F circomPrime) : Expression (F circomPrime))
      else 0)) 0
  + splitTop bytes bits (splitIdx k)
      * (((2 ^ (7 - 121 * k % 8) : ℕ) : F circomPrime) : Expression (F circomPrime))

/-- Pack a big-endian byte-expression vector into `BigInt 34` **affine** limbs,
given the `lo`/`hi` pieces of every straddled byte. Limb `k` collects
* the `hi` piece of boundary `k` at offset `0` (when `k` straddles),
* every byte fully inside `[121·k, 121·(k+1))` at offset `8·je − 121·k`,
* the `lo` piece of boundary `k+1` at offset `121 − (121·(k+1) mod 8)`
  (when `k+1 < 34` straddles). -/
def packLimbsSplit (bytes : Vector (Expression (F circomPrime)) 512)
    (splitLo splitHi : ℕ → Expression (F circomPrime)) :
    Var (BigInt numLimbs) (F circomPrime) :=
  Vector.ofFn fun k : Fin numLimbs =>
    (if 121 * k.val % 8 ≠ 0 then splitHi k.val else 0)
    + Fin.foldl 16 (fun acc d =>
        acc + (if 8 * (startByte k.val + d.val) + 8 ≤ min (121 * (k.val + 1)) 4096 then
            bytes[511 - (startByte k.val + d.val)]'(by omega)
              * (((2 ^ (8 * (startByte k.val + d.val) - 121 * k.val) : ℕ) : F circomPrime) :
                  Expression (F circomPrime))
          else 0)) 0
    + (if 121 * (k.val + 1) % 8 ≠ 0 ∧ k.val + 1 < numLimbs then
        splitLo (k.val + 1)
          * (((2 ^ (121 - 121 * (k.val + 1) % 8) : ℕ) : F circomPrime) :
              Expression (F circomPrime))
      else 0)

/-- EM `lo` piece at boundary `k`: witnessed for the two digest-region
boundaries (`k ∈ {1,2}`), a constant otherwise. -/
def emSplitLo (bits : Vector (Expression (F circomPrime)) 14) (k : ℕ) :
    Expression (F circomPrime) :=
  if k < 3 then splitLoExpr bits k
  else Expression.const
    ((emByteConst (511 - splitByteLE k) % 2 ^ (121 * k % 8) : ℕ) : F circomPrime)

/-- EM `hi` piece at boundary `k`: witnessed for the two digest-region
boundaries (`k ∈ {1,2}`), a constant otherwise. -/
def emSplitHi (emBytes : Vector (Expression (F circomPrime)) 512)
    (bits : Vector (Expression (F circomPrime)) 14) (k : ℕ) :
    Expression (F circomPrime) :=
  if k < 3 then splitHiExpr emBytes bits k
  else Expression.const
    ((emByteConst (511 - splitByteLE k) / 2 ^ (121 * k % 8) : ℕ) : F circomPrime)

set_option maxRecDepth 2048 in
/-- Witness generator for the `2·7 = 14` split bits of the EM digest region:
bit `i` is bit `i % 7` of the digest byte straddled by boundary `i / 7 + 1`. -/
def digestSplitBitsWitness (digest : Var (fields digestBytesLen) (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : Vector (F circomPrime) 14 :=
  Vector.ofFn fun i : Fin 14 =>
    let dj : ℕ := 511 - splitByteLE (splitBoundary (i.val / 7)) - 480
    let y : ℕ :=
      if h : dj < digestBytesLen then
        (Expression.eval env.toEnvironment (digest[dj]'h)).val
      else 0
    ((y / 2 ^ (i.val % 7) % 2 : ℕ) : F circomPrime)

/-- Witness generator for the `29·7 = 203` split bits of a 512-byte bignum:
bit `i` is bit `i % 7` of the byte straddled by boundary
`splitBoundary (i / 7)`. -/
def splitBitsWitness (bytes : Var (fields modulusBytesLen) (F circomPrime))
    (env : ProverEnvironment (F circomPrime)) : Vector (F circomPrime) 203 :=
  Vector.ofFn fun i : Fin 203 =>
    let je : ℕ := splitByteLE (splitBoundary (i.val / 7))
    let y : ℕ :=
      if h : 511 - je < modulusBytesLen then
        (Expression.eval env.toEnvironment (bytes[511 - je]'h)).val
      else 0
    ((y / 2 ^ (i.val % 7) % 2 : ℕ) : F circomPrime)

end Bytes
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
