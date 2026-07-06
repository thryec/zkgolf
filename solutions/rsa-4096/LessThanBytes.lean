import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MainTheorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.BytesSplitLemmas
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.RangeCheck
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Cost

/-!
# Chunked prefix-compare (`LessThanBytes`)

Asserts `os2ip lhs < os2ip rhs` directly on the two 512-byte big-endian input
vectors (byteness is a trusted `IsOctetString` assumption), replacing the full
4096-bit borrow-chain `LessThanTight` (~8.5k score) with a 57-chunk
lexicographic compare (138 allocations + 181 rows):

* the 512 bytes are conceptually left-padded by four zero bytes and chunked
  big-endian into 57 affine chunks of 9 bytes (`chunkExpr`, each `< 2^72`);
* 56 prefix-equality flags `p_1 .. p_56` are witnessed (`p_0 := 1`,
  `p_57 := 0` are constants): `p_j = 1` certifies chunks `0 .. j−1` agree;
* a difference witness `d = δ − 1` is range-checked to 72 bits
  (`δ := d + 1 ∈ [1, 2^72]`);
* **equal-prefix rows** `p_{t+1}·(N_t − S_t) = 0` for `t = 0 .. 41`;
* **first-difference rows** `(p_j − p_{j+1})·(N_j − S_j − δ) = 0` for
  `j = 0 .. 56`.

Soundness needs *no* monotonicity or booleanity rows: take `k` minimal with
`p_{k+1} = 0` (exists because `p_57 = 0`). All flags `p_1 .. p_k` are then
nonzero, so the equal-prefix rows pin chunks `0 .. k−1` equal, and the `k`-th
first-difference row has nonzero multiplier `p_k − p_{k+1}`, pinning
`N_k = S_k + δ` over ℕ (no wraparound: all magnitudes `< 2^73 ≪ p`), i.e.
`N_k > S_k`. Lexicographic-to-numeric conversion finishes.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
namespace LessThanBytes

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Solution.RSASSAPKCS1v15_SHA256_4096_65537
open BytesLemmas
open BytesSplitLemmas
open Specs.RSASSAPKCS1v15

/-- `2^72` fits the field. -/
theorem two_pow_72_lt_circomPrime : (2 : ℕ) ^ 72 < circomPrime := by decide

/-- `2^73` fits the field. -/
theorem two_pow_73_lt_circomPrime : (2 : ℕ) ^ 73 < circomPrime := by decide

/-! ## Chunk values (ℕ) -/

/-- Total byte function of a 512-byte vector (0 out of range), indexed by
big-endian byte position. -/
def bfn (xs : Vector ℕ 512) : ℕ → ℕ := fun t => if h : t < 512 then xs[t]'h else 0

/-- The conceptual four-zero-byte left padding used to make `512` bytes into
`57 * 9 = 513` bytes. -/
def paddedBfn (bv : ℕ → ℕ) (t : ℕ) : ℕ :=
  if _h : 1 ≤ t ∧ t < 513 then bv (t - 1) else 0

/-- Natural value of big-endian 9-byte chunk `j` of the padded byte function
`bv` (byte `9j` is the most significant). -/
def chunkF (bv : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 9, paddedBfn bv (9 * j + (8 - i)) * 2 ^ (8 * i)

theorem bfn_lt_of_octet {xs : Vector ℕ 512} (h : IsOctetString xs) :
    ∀ t, t < 512 → bfn xs t < 256 := by
  intro t ht
  unfold bfn
  rw [dif_pos ht]
  exact h ⟨t, ht⟩

/-- A padded byte is still `< 256`. -/
theorem paddedBfn_lt {bv : ℕ → ℕ} (hbv : ∀ t, t < 512 → bv t < 256)
    {t : ℕ} (_ht : t < 513) :
    paddedBfn bv t < 256 := by
  unfold paddedBfn
  by_cases h : 1 ≤ t ∧ t < 513
  · rw [dif_pos h]
    exact hbv (t - 1) (by omega)
  · rw [dif_neg h]
    norm_num

/-- A padded 9-byte chunk is `< 2^72`. -/
theorem chunkF_lt {bv : ℕ → ℕ} (hbv : ∀ t, t < 512 → bv t < 256) {j : ℕ}
    (hj : j < 57) :
    chunkF bv j < 2 ^ 72 := by
  unfold chunkF
  have h := sum_range_lt_pow (B := 8) (n := 9)
    (fun i => paddedBfn bv (9 * j + (8 - i))) (fun i hi => by
      have hb := paddedBfn_lt hbv (t := 9 * j + (8 - i)) (by omega)
      simpa using hb)
  simpa [show 8 * 9 = 72 by norm_num] using h

/-! ## `os2ip` as a big-endian chunk sum -/

/-- The little-endian byte view of a big-endian byte vector, padded with four
zero high bytes. -/
def lePaddedByte (xs : Vector ℕ 512) (k : ℕ) : ℕ :=
  if _h : k < 512 then xs[511 - k]! else 0

/-- **Regrouping**: 9-byte chunks at base `2^72` recompose the base-`2^8` byte sum. -/
theorem twelve_byte_regroup (f : ℕ → ℕ) :
    ∀ n, (∑ c ∈ Finset.range n,
          (∑ i ∈ Finset.range 9, f (9 * c + i) * 2 ^ (8 * i)) * 2 ^ (72 * c))
      = ∑ k ∈ Finset.range (9 * n), f k * 2 ^ (8 * k) := by
  intro n
  induction n with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show 9 * (t + 1) = 9 * t + 9 by ring, Finset.sum_range_add]
    have htail :
        (∑ i ∈ Finset.range 9, f (9 * t + i) * 2 ^ (8 * i)) * 2 ^ (72 * t)
          = ∑ i ∈ Finset.range 9, f (9 * t + i) * 2 ^ (8 * (9 * t + i)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [mul_assoc, ← pow_add]
      rw [show 8 * i + 72 * t = 8 * (9 * t + i) by ring]
    rw [htail]

/-- `bfn` at an in-range big-endian position, `getElem!` form. -/
private theorem bfn_eq_getElem! (xs : Vector ℕ 512) (t : ℕ) (ht : t < 512) :
    bfn xs t = xs[t]! := by
  unfold bfn
  rw [dif_pos ht, getElem!_pos xs t ht]

/-- One little-endian 9-byte group is the big-endian chunk `56 − c`. -/
private theorem chunk_group_eq (xs : Vector ℕ 512) (c : ℕ) (hc : c < 57) :
    (∑ i ∈ Finset.range 9, lePaddedByte xs (9 * c + i) * 2 ^ (8 * i))
      = chunkF (bfn xs) (56 - c) := by
  unfold chunkF lePaddedByte paddedBfn bfn
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases hk : 9 * c + i < 512
  · have hp : 1 ≤ 9 * (56 - c) + (8 - i) ∧
        9 * (56 - c) + (8 - i) < 513 := by omega
    have hidx : 9 * (56 - c) + (8 - i) - 1 = 511 - (9 * c + i) := by omega
    have hidxlt : 511 - (9 * c + i) < 512 := by omega
    simp [hk, hp, hidx, getElem!_pos xs (511 - (9 * c + i)) hidxlt]
    intro hbad
    omega
  · have hp : ¬ (1 ≤ 9 * (56 - c) + (8 - i) ∧
        9 * (56 - c) + (8 - i) < 513) := by omega
    simp [hk, hp]

/-- `os2ip` as the base-`2^72` sum of big-endian chunks (`c` is the little-endian
chunk position; big-endian chunk `56 − c`). -/
theorem os2ip_eq_chunk_sum (xs : Vector ℕ 512) :
    os2ip xs = ∑ c ∈ Finset.range 57, chunkF (bfn xs) (56 - c) * 2 ^ (72 * c) := by
  have hre := twelve_byte_regroup (lePaddedByte xs) 57
  norm_num at hre
  rw [os2ip_vec_eq_sum_le]
  rw [show (∑ c ∈ Finset.range 57, chunkF (bfn xs) (56 - c) * 2 ^ (72 * c))
      = ∑ c ∈ Finset.range 57,
          (∑ i ∈ Finset.range 9, lePaddedByte xs (9 * c + i) * 2 ^ (8 * i)) * 2 ^ (72 * c) by
    apply Finset.sum_congr rfl
    intro c hc
    rw [Finset.mem_range] at hc
    rw [chunk_group_eq xs c hc]]
  rw [hre]
  rw [show (513 : ℕ) = 512 + 1 by norm_num, Finset.sum_range_add]
  have htail : (∑ x ∈ Finset.range 1, lePaddedByte xs (512 + x) * 2 ^ (8 * (512 + x))) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    simp [lePaddedByte, show ¬ 512 + x < 512 by omega]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_range] at hc
  simp [lePaddedByte, hc, getElem!_pos xs (511 - c) (by omega)]

/-! ## Lexicographic-to-numeric comparison -/

/-- Strict base-`2^72` comparison from a first difference at little-endian
position `K`: higher chunks equal, chunk `K` strictly larger, lower chunks of
the smaller side bounded. -/
theorem lex_sum_lt (C D : ℕ → ℕ) (K : ℕ) (hK : K < 57)
    (hbound : ∀ c, c < K → D c < 2 ^ 72)
    (hhigh : ∀ c, K < c → c < 57 → C c = D c)
    (hdiff : D K < C K) :
    (∑ c ∈ Finset.range 57, D c * 2 ^ (72 * c))
      < ∑ c ∈ Finset.range 57, C c * 2 ^ (72 * c) := by
  have hsplitD := Finset.sum_range_add_sum_Ico (fun c => D c * 2 ^ (72 * c))
    (show K + 1 ≤ 57 from by omega)
  have hsplitC := Finset.sum_range_add_sum_Ico (fun c => C c * 2 ^ (72 * c))
    (show K + 1 ≤ 57 from by omega)
  have htail : (∑ c ∈ Finset.Ico (K + 1) 57, C c * 2 ^ (72 * c))
      = ∑ c ∈ Finset.Ico (K + 1) 57, D c * 2 ^ (72 * c) := by
    apply Finset.sum_congr rfl
    intro c hc
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hc
    rw [hhigh c (by omega) h2]
  have hheadD := Finset.sum_range_succ (fun c => D c * 2 ^ (72 * c)) K
  have hheadC := Finset.sum_range_succ (fun c => C c * 2 ^ (72 * c)) K
  have hDlow : (∑ c ∈ Finset.range K, D c * 2 ^ (72 * c)) < 2 ^ (72 * K) :=
    sum_range_lt_pow (B := 72) D hbound
  have hmul : (D K + 1) * 2 ^ (72 * K) ≤ C K * 2 ^ (72 * K) :=
    Nat.mul_le_mul_right _ (by omega)
  have hClow : 0 ≤ ∑ c ∈ Finset.range K, C c * 2 ^ (72 * c) := Nat.zero_le _
  simp only [] at hsplitD hsplitC hheadD hheadC
  rw [← hsplitD, ← hsplitC, htail, hheadD, hheadC]
  have hexp : (D K + 1) * 2 ^ (72 * K) = D K * 2 ^ (72 * K) + 2 ^ (72 * K) := by ring
  omega

/-- Numeric strictness from a first big-endian chunk difference. -/
theorem os2ip_lt_of_first_diff (Sn Nn : Vector ℕ 512)
    (hSoct : IsOctetString Sn) (k : ℕ) (hk : k < 57)
    (hpre : ∀ t, t < k → chunkF (bfn Nn) t = chunkF (bfn Sn) t)
    (hdiff : chunkF (bfn Sn) k < chunkF (bfn Nn) k) :
    os2ip Sn < os2ip Nn := by
  rw [os2ip_eq_chunk_sum Sn, os2ip_eq_chunk_sum Nn]
  refine lex_sum_lt (fun c => chunkF (bfn Nn) (56 - c)) (fun c => chunkF (bfn Sn) (56 - c))
    (56 - k) (by omega) ?_ ?_ ?_
  · intro c _hc
    exact chunkF_lt (bfn_lt_of_octet hSoct) (by omega)
  · intro c h1 h2
    exact hpre (56 - c) (by omega)
  · show chunkF (bfn Sn) (56 - (56 - k)) < chunkF (bfn Nn) (56 - (56 - k))
    rw [show 56 - (56 - k) = k from by omega]
    exact hdiff

/-- Completeness inverse: a strict numeric comparison of octet strings yields a
first differing big-endian chunk, in `Nat.find` form (matching the circuit's
witness generators). -/
theorem exists_first_diff (Sn Nn : Vector ℕ 512)
    (_hSoct : IsOctetString Sn) (hNoct : IsOctetString Nn)
    (hlt : os2ip Sn < os2ip Nn) :
    ∃ hex : (∃ j, j < 57 ∧ chunkF (bfn Nn) j ≠ chunkF (bfn Sn) j),
      (∀ t, t < Nat.find hex → chunkF (bfn Nn) t = chunkF (bfn Sn) t) ∧
        chunkF (bfn Sn) (Nat.find hex) < chunkF (bfn Nn) (Nat.find hex) := by
  have hex : ∃ j, j < 57 ∧ chunkF (bfn Nn) j ≠ chunkF (bfn Sn) j := by
    by_contra hall
    push_neg at hall
    have heq : os2ip Sn = os2ip Nn := by
      rw [os2ip_eq_chunk_sum, os2ip_eq_chunk_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.mem_range] at hc
      rw [hall (56 - c) (by omega)]
    omega
  have hk57 : Nat.find hex < 57 := (Nat.find_spec hex).1
  have hkne : chunkF (bfn Nn) (Nat.find hex) ≠ chunkF (bfn Sn) (Nat.find hex) :=
    (Nat.find_spec hex).2
  have hpre : ∀ t, t < Nat.find hex → chunkF (bfn Nn) t = chunkF (bfn Sn) t := by
    intro t ht
    have hmin := Nat.find_min hex ht
    push_neg at hmin
    exact hmin (by omega)
  refine ⟨hex, hpre, ?_⟩
  rcases Nat.lt_or_ge (chunkF (bfn Sn) (Nat.find hex)) (chunkF (bfn Nn) (Nat.find hex)) with h | h
  · exact h
  · have hlt' : chunkF (bfn Nn) (Nat.find hex) < chunkF (bfn Sn) (Nat.find hex) := by omega
    have := os2ip_lt_of_first_diff Nn Sn hNoct (Nat.find hex) hk57
      (fun t ht => (hpre t ht).symm) hlt'
    omega

/-! ## Chunk expressions (affine) and witness helpers -/

/-- A padded byte expression: the first four conceptual bytes are zero. -/
def paddedByteExpr (bytes : Vector (Expression (F circomPrime)) 512) (t : ℕ) :
    Expression (F circomPrime) :=
  if h : 1 ≤ t ∧ t < 513 then bytes[t - 1]'(by omega) else 0

/-- Affine 9-byte big-endian chunk expression `j` of a padded 512-byte
expression vector. -/
def chunkExpr (bytes : Vector (Expression (F circomPrime)) 512) (j : ℕ) (_hj : j < 57) :
    Expression (F circomPrime) :=
  Fin.foldl 9 (fun acc i =>
    acc + paddedByteExpr bytes (9 * j + (8 - i.val))
      * (((2 : ℕ) ^ (8 * i.val) : ℕ) : F circomPrime)) 0

/-- The chunk expression evaluates to the cast of the ℕ chunk of the evaluated
bytes (a pure cast identity; no bounds needed). -/
theorem chunkExpr_eval (env : Environment (F circomPrime))
    (bytes : Vector (Expression (F circomPrime)) 512)
    (v : Vector (F circomPrime) 512)
    (hv : ∀ t (ht : t < 512), Expression.eval env (bytes[t]'ht) = v[t]'ht)
    (j : ℕ) (hj : j < 57) :
    Expression.eval env (chunkExpr bytes j hj)
      = ((chunkF (bfn (fieldBytesToNat v)) j : ℕ) : F circomPrime) := by
  unfold chunkExpr chunkF
  rw [eval_foldl_add]
  rw [← Fin.sum_univ_eq_sum_range
      (fun i => paddedBfn (bfn (fieldBytesToNat v)) (9 * j + (8 - i)) * 2 ^ (8 * i)),
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold paddedByteExpr paddedBfn bfn
  simp only [Expression.eval, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  by_cases h : 1 ≤ 9 * j + (8 - i.val) ∧ 9 * j + (8 - i.val) < 513
  · rw [dif_pos h, dif_pos h, hv (9 * j + (8 - i.val) - 1) (by omega)]
    simp only [fieldBytesToNat, Vector.getElem_map]
    rw [dif_pos (by omega : 9 * j + (8 - i.val) - 1 < 512)]
    rw [← ZMod.natCast_zmod_val (v[9 * j + (8 - i.val) - 1]'(by omega))]
    rfl
  · rw [dif_neg h, dif_neg h]
    simp only [Expression.eval, Nat.cast_zero, zero_mul]

/-- Byte function of an expression vector under an environment (0 out of
range). -/
def bfune (env : Environment (F circomPrime))
    (x : Vector (Expression (F circomPrime)) 512) : ℕ → ℕ :=
  fun t => if h : t < 512 then (Expression.eval env (x[t]'h)).val else 0

theorem bfune_eq_bfn (env : Environment (F circomPrime))
    (x : Vector (Expression (F circomPrime)) 512) (v : Vector (F circomPrime) 512)
    (hv : Vector.map (Expression.eval env) x = v) :
    bfune env x = bfn (fieldBytesToNat v) := by
  funext t
  unfold bfune bfn
  by_cases ht : t < 512
  · rw [dif_pos ht, dif_pos ht]
    simp only [fieldBytesToNat, Vector.getElem_map]
    rw [← hv, Vector.getElem_map]
  · rw [dif_neg ht, dif_neg ht]

/-- Witness value of the prefix-equality flag `p_j`: `1` iff big-endian chunks
`0 .. j−1` agree. -/
def flagWit (Nf Sf : ℕ → ℕ) (j : ℕ) : F circomPrime :=
  if ∀ t, t < j → chunkF Nf t = chunkF Sf t then 1 else 0

/-- Witness value of `δ − 1` (`δ` the first chunk difference; `0` if the inputs
are equal, which the honest prover never hits). -/
def deltaWit (Nf Sf : ℕ → ℕ) : ℕ :=
  if h : ∃ j, j < 57 ∧ chunkF Nf j ≠ chunkF Sf j
  then chunkF Nf (Nat.find h) - chunkF Sf (Nat.find h) - 1
  else 0

/-! ## The circuit -/

/-- Inputs of `LessThanBytes`: the big-endian byte strings `lhs` and `rhs`,
asserting `os2ip lhs < os2ip rhs`. -/
structure Inputs (F : Type) where
  lhs : Vector F 512
  rhs : Vector F 512
deriving ProvableStruct

/-- The `main` circuit: witness the 56 prefix-equality flags and the 72-bit
difference `δ − 1`, range-check the difference, and assert the equal-prefix and
first-difference rows. -/
def main (input : Var Inputs (F circomPrime)) : Circuit (F circomPrime) Unit := do
  let S := input.lhs
  let N := input.rhs

  -- 1. prefix-equality flags `p_1 .. p_56`
  let flags ← witnessVector 56 fun env =>
    Vector.ofFn fun j : Fin 56 =>
      flagWit (bfune env.toEnvironment N) (bfune env.toEnvironment S) (j.val + 1)

  -- 2. the difference witness `d = δ − 1`, range-checked to 72 bits
  let dv ← witnessVector 1 fun env =>
    Vector.ofFn fun _ : Fin 1 =>
      ((deltaWit (bfune env.toEnvironment N) (bfune env.toEnvironment S) : ℕ) : F circomPrime)
  RangeCheck.circuit 72 two_pow_72_lt_circomPrime (by norm_num) (dv[0]'(by omega))

  -- 3. equal-prefix rows `p_{t+1} · (N_t − S_t) = 0`, `t = 0 .. 41`
  let eqCs : Vector (Expression (F circomPrime)) 56 := Vector.mapFinRange 56 fun t =>
    (flags[t.val]'t.isLt)
      * (chunkExpr N t.val (by have := t.isLt; omega) - chunkExpr S t.val (by have := t.isLt; omega))
  Circuit.forEach eqCs assertZero

  -- 1. first-difference rows `(p_j − p_{j+1}) · (N_j − S_j − δ) = 0`, `j = 0 .. 56`
  let diffCs : Vector (Expression (F circomPrime)) 57 := Vector.mapFinRange 57 fun j =>
    ((if _h : j.val = 0 then (1 : Expression (F circomPrime))
        else flags[j.val - 1]'(by have := j.isLt; omega))
      - (if _h : j.val = 56 then (0 : Expression (F circomPrime))
        else flags[j.val]'(by have := j.isLt; omega)))
      * (chunkExpr N j.val j.isLt - chunkExpr S j.val j.isLt - ((dv[0]'(by omega)) + 1))
  Circuit.forEach diffCs assertZero

instance elaborated : ElaboratedCircuit (F circomPrime) Inputs unit main where
  -- flags : 56; d : 1; RangeCheck bits : 71
  localLength _ := 56 + 1 + 71
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, RangeCheck.circuit]

/-- Preconditions: both byte strings are octet strings. -/
def Assumptions (input : Inputs (F circomPrime)) : Prop :=
  IsOctetString (fieldBytesToNat input.lhs) ∧ IsOctetString (fieldBytesToNat input.rhs)

/-- Postcondition: `os2ip lhs < os2ip rhs`. -/
def Spec (input : Inputs (F circomPrime)) : Prop :=
  os2ip (fieldBytesToNat input.lhs) < os2ip (fieldBytesToNat input.rhs)

theorem soundness : FormalAssertion.Soundness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  simp only [circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    Nat.mul_zero, Nat.add_zero] at h_holds
  obtain ⟨h_range, h_eqp, h_diff⟩ := h_holds
  obtain ⟨hS_oct, hN_oct⟩ := h_assumptions
  refine ⟨?_, Or.inl rfl⟩
  -- nat-indexed row hypotheses (strip the `Fin` coercions)
  have h_eqp' : ∀ (t : ℕ) (ht : t < 56),
      env.get (i₀ + t)
          * (Expression.eval env (chunkExpr input_var_rhs t (by omega))
            + -Expression.eval env (chunkExpr input_var_lhs t (by omega))) = 0 :=
    fun t ht => h_eqp ⟨t, ht⟩
  have h_diff' : ∀ (j : ℕ) (hj : j < 57),
      (Expression.eval env
          (if _h : j = 0 then 1 else var { index := i₀ + (j - 1) } : Expression (F circomPrime))
          + -Expression.eval env
              (if _h : j = 56 then 0 else var { index := i₀ + j } : Expression (F circomPrime)))
        * (Expression.eval env (chunkExpr input_var_rhs j hj)
            + -Expression.eval env (chunkExpr input_var_lhs j hj)
            + -(env.get (i₀ + 56) + 1)) = 0 :=
    fun j hj => h_diff ⟨j, hj⟩
  -- evaluated inputs and their nat byte vectors
  have hS_e : ∀ (t : ℕ) (ht : t < 512),
      Expression.eval env (input_var_lhs[t]'ht) = input_lhs[t]'ht := by
    intro t ht
    rw [← h_input.1]
    simp [Vector.getElem_map]
  have hN_e : ∀ (t : ℕ) (ht : t < 512),
      Expression.eval env (input_var_rhs[t]'ht) = input_rhs[t]'ht := by
    intro t ht
    rw [← h_input.2]
    simp [Vector.getElem_map]
  set SN := fieldBytesToNat input_lhs with hSN
  set NN := fieldBytesToNat input_rhs with hNN
  -- chunk evaluation bridges
  have hCS_e : ∀ (j : ℕ) (hj : j < 57),
      Expression.eval env (chunkExpr input_var_lhs j hj)
        = ((chunkF (bfn SN) j : ℕ) : F circomPrime) :=
    fun j hj => chunkExpr_eval env input_var_lhs input_lhs hS_e j hj
  have hCN_e : ∀ (j : ℕ) (hj : j < 57),
      Expression.eval env (chunkExpr input_var_rhs j hj)
        = ((chunkF (bfn NN) j : ℕ) : F circomPrime) :=
    fun j hj => chunkExpr_eval env input_var_rhs input_rhs hN_e j hj
  -- chunk bounds
  have hCS_lt : ∀ j, j < 57 → chunkF (bfn SN) j < 2 ^ 72 :=
    fun j hj => chunkF_lt (bfn_lt_of_octet hS_oct) hj
  have hCN_lt : ∀ j, j < 57 → chunkF (bfn NN) j < 2 ^ 72 :=
    fun j hj => chunkF_lt (bfn_lt_of_octet hN_oct) hj
  -- nat flag values, with the constant endpoints folded in
  set F1 : ℕ → ℕ := fun j =>
    if j = 0 then 1 else if _h : j ≤ 56 then (env.get (i₀ + (j - 1))).val else 0 with hF1
  have hF1_57 : F1 57 = 0 := by simp [hF1]
  -- the first flag boundary
  have hex : ∃ j, j < 57 ∧ F1 (j + 1) = 0 := ⟨56, by omega, hF1_57⟩
  set k := Nat.find hex with hkdef
  have hk57 : k < 57 := (Nat.find_spec hex).1
  have hk0 : F1 (k + 1) = 0 := (Nat.find_spec hex).2
  have hpre_nz : ∀ t, t < k → F1 (t + 1) ≠ 0 := by
    intro t ht
    have hmin := Nat.find_min hex ht
    push_neg at hmin
    exact hmin (by omega)
  have hFk_nz : F1 k ≠ 0 := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hF1, hk]
    · have := hpre_nz (k - 1) (by omega)
      rwa [show k - 1 + 1 = k from by omega] at this
  -- the range-checked difference
  have hd_lt : (env.get (i₀ + 56)).val < 2 ^ 72 := h_range
  -- prefix chunks are equal (over ℕ)
  have hpre_nat : ∀ t, t < k → chunkF (bfn NN) t = chunkF (bfn SN) t := by
    intro t ht
    have ht56 : t < 56 := by omega
    have hrow := h_eqp' t ht56
    rw [hCN_e t (by omega), hCS_e t (by omega)] at hrow
    have hflag_nz : env.get (i₀ + t) ≠ 0 := by
      have hFval : F1 (t + 1) = (env.get (i₀ + t)).val := by
        simp only [hF1, if_neg (by omega : ¬ (t + 1 = 0)),
          dif_pos (by omega : t + 1 ≤ 56), Nat.add_sub_cancel]
      have hval_nz : (env.get (i₀ + t)).val ≠ 0 := by
        intro hv
        exact hpre_nz t ht (by rw [hFval, hv])
      intro hz
      exact hval_nz (by rw [hz, ZMod.val_zero])
    rcases mul_eq_zero.mp hrow with h | h
    · exact absurd h hflag_nz
    · have hcast : ((chunkF (bfn NN) t : ℕ) : F circomPrime)
          = ((chunkF (bfn SN) t : ℕ) : F circomPrime) := by linear_combination h
      have := congrArg ZMod.val hcast
      rwa [val_natCast_lt' (lt_trans (hCN_lt t (by omega)) two_pow_72_lt_circomPrime),
        val_natCast_lt' (lt_trans (hCS_lt t (by omega)) two_pow_72_lt_circomPrime)] at this
  -- the first-difference row at `k` pins `N_k = S_k + δ` over ℕ
  have hdiff_nat : chunkF (bfn SN) k < chunkF (bfn NN) k := by
    have hrow := h_diff' k hk57
    rw [hCN_e k hk57, hCS_e k hk57] at hrow
    -- evaluate the outgoing flag as zero and keep the incoming multiplier nonzero.
    have hpin_nz : Expression.eval env
        (if _h : k = 0 then 1 else
          var { index := i₀ + (k - 1) } : Expression (F circomPrime)) ≠ 0 := by
      split
      · simp [circuit_norm]
      · rename_i hkne
        have hFval : F1 k = (env.get (i₀ + (k - 1))).val := by
          simp only [hF1, if_neg hkne, dif_pos (by omega : k ≤ 56)]
        have hval_nz : (env.get (i₀ + (k - 1))).val ≠ 0 := by
          intro hv
          exact hFk_nz (by rw [hFval, hv])
        intro hz
        have hz' : env.get (i₀ + (k - 1)) = 0 := by
          simpa [Expression.eval] using hz
        exact hval_nz (by rw [hz', ZMod.val_zero])
    have hpout : Expression.eval env
        (if _h : k = 56 then 0 else
          var { index := i₀ + k } : Expression (F circomPrime)) = 0 := by
      split
      · simp [circuit_norm]
      · rename_i hkne
        show env.get (i₀ + k) = 0
        have hv : (env.get (i₀ + k)).val = 0 := by
          have := hk0
          simp only [hF1, if_neg (by omega : ¬ (k + 1 = 0)), dif_pos (by omega : k + 1 ≤ 56),
            Nat.add_sub_cancel] at this
          exact this
        exact (ZMod.val_eq_zero _).mp hv
    rw [hpout] at hrow
    have hmul_nz : Expression.eval env
        (if _h : k = 0 then 1 else
          var { index := i₀ + (k - 1) } : Expression (F circomPrime)) + -0 ≠ 0 := by
      simpa using hpin_nz
    rcases mul_eq_zero.mp hrow with h | h
    · exact absurd h hmul_nz
    · -- `cast N_k = cast S_k + d + 1` in the field, lift to ℕ
      have hd_cast : env.get (i₀ + 56) = (((env.get (i₀ + 56)).val : ℕ) : F circomPrime) :=
        (ZMod.natCast_zmod_val _).symm
      have hcast : ((chunkF (bfn NN) k : ℕ) : F circomPrime)
          = ((chunkF (bfn SN) k + (env.get (i₀ + 56)).val + 1 : ℕ) : F circomPrime) := by
        push_cast
        rw [← hd_cast]
        linear_combination h
      have hv := congrArg ZMod.val hcast
      rw [val_natCast_lt' (lt_trans (hCN_lt k hk57) two_pow_72_lt_circomPrime),
        val_natCast_lt' (lt_of_lt_of_le (by
          have := hCS_lt k hk57
          omega : chunkF (bfn SN) k + (env.get (i₀ + 56)).val + 1 < 2 ^ 73)
          two_pow_73_lt_circomPrime.le)] at hv
      omega
  exact os2ip_lt_of_first_diff SN NN hS_oct k hk57 hpre_nat hdiff_nat

theorem completeness : FormalAssertion.Completeness (F circomPrime) main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec]
  simp only [circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    Nat.mul_zero, Nat.add_zero] at h_env ⊢
  obtain ⟨h_fwit, h_dwit⟩ := h_env
  obtain ⟨hS_oct, hN_oct⟩ := h_assumptions
  set SN := fieldBytesToNat input_lhs with hSN
  set NN := fieldBytesToNat input_rhs with hNN
  -- the witness byte functions are the nat byte functions of the inputs
  have hNf : bfune env.toEnvironment input_var_rhs = bfn NN :=
    bfune_eq_bfn env.toEnvironment input_var_rhs input_rhs h_input.2
  have hSf : bfune env.toEnvironment input_var_lhs = bfn SN :=
    bfune_eq_bfn env.toEnvironment input_var_lhs input_lhs h_input.1
  -- witnessed flag / delta values
  have hflag : ∀ (t : ℕ) (ht : t < 56),
      env.get (i₀ + t) = flagWit (bfn NN) (bfn SN) (t + 1) := by
    intro t ht
    have h := h_fwit ⟨t, ht⟩
    rw [Vector.getElem_ofFn, hNf, hSf] at h
    exact h
  have hdval : env.get (i₀ + 56)
      = ((deltaWit (bfn NN) (bfn SN) : ℕ) : F circomPrime) := by
    have h := h_dwit 0
    rw [Vector.getElem_ofFn, hNf, hSf] at h
    exact h
  -- the first differing chunk
  obtain ⟨hex, hpre, hdiff⟩ := exists_first_diff SN NN hS_oct hN_oct h_spec
  set k := Nat.find hex with hkdef
  have hk57 : k < 57 := (Nat.find_spec hex).1
  have hCN_lt : ∀ j, j < 57 → chunkF (bfn NN) j < 2 ^ 72 :=
    fun j hj => chunkF_lt (bfn_lt_of_octet hN_oct) hj
  have hdelta : deltaWit (bfn NN) (bfn SN)
      = chunkF (bfn NN) k - chunkF (bfn SN) k - 1 := by
    unfold deltaWit
    rw [dif_pos hex]
  -- the flag witness is the prefix indicator `[j ≤ k]`
  have hflagWit : ∀ j : ℕ, flagWit (bfn NN) (bfn SN) j
      = if j ≤ k then 1 else 0 := by
    intro j
    unfold flagWit
    by_cases hj : j ≤ k
    · rw [if_pos (fun t ht => hpre t (by omega)), if_pos hj]
    · rw [if_neg (fun hall => (Nat.find_spec hex).2 (hall k (by omega))), if_neg hj]
  -- chunk evaluation bridges
  have hS_e : ∀ (t : ℕ) (ht : t < 512),
      Expression.eval env.toEnvironment (input_var_lhs[t]'ht) = input_lhs[t]'ht := by
    intro t ht
    rw [← h_input.1]
    simp [Vector.getElem_map]
  have hN_e : ∀ (t : ℕ) (ht : t < 512),
      Expression.eval env.toEnvironment (input_var_rhs[t]'ht) = input_rhs[t]'ht := by
    intro t ht
    rw [← h_input.2]
    simp [Vector.getElem_map]
  have hCS_e : ∀ (j : ℕ) (hj : j < 57),
      Expression.eval env.toEnvironment (chunkExpr input_var_lhs j hj)
        = ((chunkF (bfn SN) j : ℕ) : F circomPrime) :=
    fun j hj => chunkExpr_eval env.toEnvironment input_var_lhs input_lhs hS_e j hj
  have hCN_e : ∀ (j : ℕ) (hj : j < 57),
      Expression.eval env.toEnvironment (chunkExpr input_var_rhs j hj)
        = ((chunkF (bfn NN) j : ℕ) : F circomPrime) :=
    fun j hj => chunkExpr_eval env.toEnvironment input_var_rhs input_rhs hN_e j hj
  refine ⟨?_, ?_, ?_⟩
  · -- 72-bit range of the difference witness
    rw [hdval, hdelta]
    have hlt : chunkF (bfn NN) k - chunkF (bfn SN) k - 1 < 2 ^ 72 := by
      have := hCN_lt k hk57
      omega
    rw [val_natCast_lt' (lt_trans hlt two_pow_72_lt_circomPrime)]
    exact hlt
  · -- equal-prefix rows
    intro i
    rw [hflag i.val i.isLt, hflagWit, hCN_e i.val (by have := i.isLt; omega),
      hCS_e i.val (by have := i.isLt; omega)]
    by_cases hik : i.val + 1 ≤ k
    · rw [if_pos hik, hpre i.val (by omega)]
      ring
    · rw [if_neg hik]
      ring
  · -- first-difference rows
    intro i
    have hpin_e : Expression.eval env.toEnvironment
        (if _h : i.val = 0 then 1 else
          var { index := i₀ + (i.val - 1) } : Expression (F circomPrime))
        = if i.val ≤ k then 1 else 0 := by
      split
      · rename_i h0
        rw [if_pos (by omega)]
        simp [circuit_norm]
      · rename_i h0
        show env.get (i₀ + (i.val - 1)) = _
        rw [hflag (i.val - 1) (by have := i.isLt; omega), hflagWit,
          show i.val - 1 + 1 = i.val from by omega]
    have hpout_e : Expression.eval env.toEnvironment
        (if _h : i.val = 56 then 0 else
          var { index := i₀ + i.val } : Expression (F circomPrime))
        = if i.val + 1 ≤ k then 1 else 0 := by
      split
      · rename_i h0
        rw [if_neg (by omega)]
        simp [circuit_norm]
      · rename_i h0
        show env.get (i₀ + i.val) = _
        rw [hflag i.val (by have := i.isLt; omega), hflagWit]
    rw [hpin_e, hpout_e, hCN_e i.val i.isLt, hCS_e i.val i.isLt, hdval, hdelta]
    rcases Nat.lt_trichotomy i.val k with hik | hik | hik
    · rw [if_pos (by omega : i.val ≤ k), if_pos (by omega : i.val + 1 ≤ k)]
      ring
    · rw [if_pos (by omega : i.val ≤ k), if_neg (by omega : ¬ (i.val + 1 ≤ k))]
      have hnat : (chunkF (bfn NN) k - chunkF (bfn SN) k - 1)
          + chunkF (bfn SN) i.val + 1 = chunkF (bfn NN) i.val := by
        rw [hik]
        omega
      have hcast := congrArg (Nat.cast : ℕ → F circomPrime) hnat
      push_cast at hcast
      linear_combination hcast.symm
    · rw [if_neg (by omega : ¬ (i.val ≤ k)), if_neg (by omega : ¬ (i.val + 1 ≤ k))]
      ring

def circuit : FormalAssertion (F circomPrime) Inputs where
  main := main
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end LessThanBytes

/-! ## Cost / R1CS certificates -/

namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS
open Solution.RSASSAPKCS1v15_SHA256_4096_65537.CostInfra

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-- Padded byte expressions are affine when the real byte expressions are. -/
theorem affine_paddedByteExpr (bytes : Vector (Expression (F circomPrime)) 512)
    (hb : ∀ t (ht : t < 512), Affine (bytes[t]'ht)) (t : ℕ) :
    Affine (LessThanBytes.paddedByteExpr bytes t) := by
  unfold LessThanBytes.paddedByteExpr
  split
  · exact hb _ (by omega)
  · exact Affine.zero

/-- Chunk expressions are affine when the byte expressions are. -/
theorem affine_chunkExpr (bytes : Vector (Expression (F circomPrime)) 512)
    (hb : ∀ t (ht : t < 512), Affine (bytes[t]'ht)) (j : ℕ) (hj : j < 57) :
    Affine (LessThanBytes.chunkExpr bytes j hj) := by
  unfold LessThanBytes.chunkExpr
  refine affine_finFoldl' _ _ Affine.zero fun acc i hacc => ?_
  exact Affine.add hacc (Affine.mul_fconst _ (affine_paddedByteExpr bytes hb _))

/-- Cost of `LessThanBytes.main`: 56 flags + 1 difference cell + a 72-bit
implicit range check, with 56 equal-prefix + 57 first-difference rows:
`⟨128, 185⟩`. -/
theorem costIs_lessThanBytes (input : Var LessThanBytes.Inputs (F circomPrime)) :
    CostIs (LessThanBytes.main input) ⟨128, 185⟩ := by
  rw [show (⟨128, 185⟩ : Count)
        = ⟨56, 0⟩ + (⟨1, 0⟩ + (⟨72 - 1, 72⟩
            + (⟨56 * 0, 56 * 1⟩ + ⟨57 * 0, 57 * 1⟩))) from by congr 1]
  unfold LessThanBytes.main
  refine CostIs.bind (CostIs.witnessVector 56 _) fun flags => ?_
  refine CostIs.bind (CostIs.witnessVector 1 _) fun dv => ?_
  refine CostIs.bind (costIs_assertion_implicitRangeCheck 72
    LessThanBytes.two_pow_72_lt_circomPrime (by norm_num) _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact CostIs.forEach fun a n => CostIs.assertZero _ n

theorem costIs_assertion_lessThanBytes (b : Var LessThanBytes.Inputs (F circomPrime)) :
    CostIs (assertion LessThanBytes.circuit b) ⟨128, 185⟩ :=
  CostIs.assertion (fun n => costIs_lessThanBytes b n)

theorem isR1CS_lessThanBytes (input : Var LessThanBytes.Inputs (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThanBytes.main input) := by
  unfold LessThanBytes.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 56 _) fun nf => ?_
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 1 _) fun nd => ?_
  refine IsR1CSCirc.bind (isR1CS_assertion_implicitRangeCheck 72
    LessThanBytes.two_pow_72_lt_circomPrime (by norm_num) _
    (affineW_witnessVector_output _ _ _ 0 (by omega))) fun _ => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- equal-prefix rows: flag · (affine chunk difference)
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affine_chunkExpr _ (fun t ht => hr t ht) _ _)
        (affine_chunkExpr _ (fun t ht => hl t ht) _ _))
  -- first-difference rows: (affine flag difference) · (affine chunk/δ difference)
  refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
  refine IsR1CSCirc.assertZero ?_ k
  rw [Vector.getElem_mapFinRange]
  refine isR1CSRow_mul (Affine.sub ?_ ?_)
    (Affine.sub (Affine.sub (affine_chunkExpr _ (fun t ht => hr t ht) _ _)
      (affine_chunkExpr _ (fun t ht => hl t ht) _ _))
      (Affine.add (affineW_witnessVector_output _ _ _ 0 (by omega)) (Affine.const 1)))
  · split
    · exact Affine.const 1
    · exact affineW_witnessVector_output _ _ _ _ (by omega)
  · split
    · exact Affine.zero
    · exact affineW_witnessVector_output _ _ _ _ (by omega)

theorem isR1CS_assertion_lessThanBytes (b : Var LessThanBytes.Inputs (F circomPrime))
    (hl : AffineW b.lhs) (hr : AffineW b.rhs) :
    IsR1CSCirc (assertion LessThanBytes.circuit b) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThanBytes b hl hr n)

end GadgetCost

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
