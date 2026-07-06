import Solution.SHA256.SHA256Round
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256
namespace SHA256Rounds

/-!
# Helper definitions and lemmas for `SHA256Rounds`

The variable- and value-level descriptions of the 64-round accumulator, plus the
lemmas relating the `foldl` accumulator and the spec to them. These are gadget
support for `SHA256Rounds`; the gadget file keeps the six required declarations.
-/

/-- The variable-level state after `k` rounds. Used as the explicit `output` for the
    SHA256Rounds elaborated instance, mirroring how Keccak Permutation provides `stateVar`. -/
def stateVar (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) :
    ℕ → Var SHA256State (F p)
  | 0 => input_var_state
  | k + 1 =>
    let prev := stateVar i₀ input_var_state k
    #v[Vector.mapRange 32 fun j => var { index := i₀ + k * 195 + 162 + j },
       prev[0], prev[1], prev[2],
       Vector.mapRange 32 fun j => var { index := i₀ + k * 195 + 128 + j },
       prev[4], prev[5], prev[6]]

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- Generic version of `output_eq`: for any bound `k`, the `Fin.foldl k` over our round body
    equals `stateVar i₀ input_var_state k`. -/
lemma fin_foldl_eq_stateVar (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) (k : ℕ) :
    Fin.foldl k
      (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
        #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 195 + 162 + i_1 },
           acc[0], acc[1], acc[2],
           Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 195 + 128 + i_1 },
           acc[4], acc[5], acc[6]]) input_var_state =
      stateVar i₀ input_var_state k := by
  induction k with
  | zero => simp [stateVar, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [stateVar]
    rw [show Fin.foldl k
        (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
          #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 195 + 162 + i_1 },
             acc[0], acc[1], acc[2],
             Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 195 + 128 + i_1 },
             acc[4], acc[5], acc[6]]) input_var_state =
        Fin.foldl k
          (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
            #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 195 + 162 + i_1 },
               acc[0], acc[1], acc[2],
               Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 195 + 128 + i_1 },
               acc[4], acc[5], acc[6]]) input_var_state from rfl, ih]

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 64` equals `stateVar i₀ input_var_state k`.

    Uses `SHA256State (Expression (F p))` for the accumulator type (not the
    `Var SHA256State (F p)` alias) so the lemma's pattern matches `h_holds`
    syntactically — `rw` can't see through the alias. -/
lemma foldlAcc_eq_stateVar (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 64) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 64)
      (fun s (i : Fin 64) => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i.val]'i.isLt).toNat,
          w := input_var_schedule[i.val]'i.isLt })
      input_var_state ⟨k, h⟩ =
        stateVar i₀ input_var_state k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar _ _ _

/-- 63-round variant of `foldlAcc_eq_stateVar`, for the fused-final-round
    compression (`SHA256Rounds`'s inner 63-round fold, before the fused
    round-63 + Davies-Meyer tail). -/
lemma foldlAcc_eq_stateVar63 (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 63) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 63)
      (fun s (i : Fin 63) => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat,
          w := input_var_schedule[i.val]'(by have := i.isLt; omega) })
      input_var_state ⟨k, h⟩ =
        stateVar i₀ input_var_state k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar _ _ _

omit [Fact (p > 2 ^ 35)] in
/-- Helper: `constWord32 n` evaluated is always normalized (bits are 0 or 1). -/
lemma normalized_constWord32 (env : Environment (F p)) (n : ℕ) :
    Normalized (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) := by
  intro i
  have h : (n / 2^i.val % 2 : ℕ) = 0 ∨ (n / 2^i.val % 2 : ℕ) = 1 := by omega
  rcases h with h | h
  · left
    simp [constWord32, Expression.eval, h]
  · right
    simp [constWord32, Expression.eval, h]

/-- valueBits of `constWord32 n` equals `n` modulo `2^32`. -/
lemma valueBits_constWord32 (env : Environment (F p)) (n : ℕ) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) = n % 2^32 := by
  simp only [valueBits, constWord32]
  have h2 : ∀ i : Fin 32, ((n / 2^i.val % 2 : ℕ) : F p).val = n / 2^i.val % 2 := by
    intro i
    have hp : 2^35 < p := Fact.out
    have hle : (n / 2^i.val % 2 : ℕ) ≤ 1 := by omega
    have hlt : (n / 2^i.val % 2 : ℕ) < p := by omega
    exact ZMod.val_natCast_of_lt hlt
  have heq : (∑ i : Fin 32, (Vector.map (Expression.eval env)
        (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F p))))[i].val * 2^i.val)
      = ∑ i : Fin 32, (n / 2^i.val % 2) * 2^i.val := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [show (Vector.map (Expression.eval env)
          (Vector.ofFn (fun i : Fin 32 => Expression.const ((n / 2^i.val % 2 : ℕ) : F p))))[i] =
        ((n / 2^i.val % 2 : ℕ) : F p) from by
      simp [Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]]
    rw [h2 i]
  rw [heq]
  -- Standard bit-decomposition: ∑ i < 32, (n / 2^i % 2) * 2^i = n % 2^32
  have key : ∀ (m : ℕ), ∑ i : Fin m, (n / 2^i.val % 2) * 2^i.val = n % 2^m := by
    intro m
    induction m with
    | zero =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Nat.mod_one]
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      rw [ih, Nat.mod_pow_succ]
      ring
  exact key 32

/-- For `n < 2^32`, valueBits of `constWord32 n` is `n`. -/
lemma valueBits_constWord32_of_lt (env : Environment (F p)) {n : ℕ} (h : n < 2^32) :
    valueBits (Vector.map (Expression.eval env) (constWord32 (p:=p) n)) = n := by
  rw [valueBits_constWord32, Nat.mod_eq_of_lt h]

/-- The value-level state at the end of round `k`. -/
def valStateAfterRound (input_state : Vector ℕ 8)
    (input_schedule : Vector ℕ 64) : ℕ → Vector ℕ 8
  | 0 => input_state
  | k + 1 =>
    if h : k < 64 then
      let prev := valStateAfterRound input_state input_schedule k
      Specs.SHA256.sha256Round prev (Specs.SHA256.K[k]'h).toNat (input_schedule[k]'h)
    else
      valStateAfterRound input_state input_schedule k

/-- `sha256Compress` equals our `valStateAfterRound` at index 64. -/
lemma sha256Compress_eq_valStateAfterRound
    (input_state : Vector ℕ 8) (input_schedule : Vector ℕ 64) :
    Specs.SHA256.sha256Compress input_state input_schedule =
      valStateAfterRound input_state input_schedule 64 := by
  simp only [Specs.SHA256.sha256Compress]
  suffices h : ∀ k (hk : k ≤ 64),
      Fin.foldl k
        (fun s (i : Fin k) =>
          Specs.SHA256.sha256Round s
            (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat
            (input_schedule[i.val]'(by have := i.isLt; omega))) input_state =
        valStateAfterRound input_state input_schedule k by
    have := h 64 (le_refl 64)
    convert this using 1
  intro k hk
  induction k with
  | zero => simp [valStateAfterRound, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valStateAfterRound]
    rw [dif_pos (by omega : k < 64)]
    have hk' : k ≤ 64 := by omega
    specialize ih hk'
    rw [show Fin.foldl k
          (fun s (i : Fin k) =>
            Specs.SHA256.sha256Round s
              (Specs.SHA256.K[i.castSucc.val]'(by have := i.isLt; omega)).toNat
              (input_schedule[i.castSucc.val]'(by have := i.isLt; omega))) input_state =
        Fin.foldl k
          (fun s (i : Fin k) =>
            Specs.SHA256.sha256Round s
              (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat
              (input_schedule[i.val]'(by have := i.isLt; omega))) input_state from rfl, ih]
    simp [Fin.val_last]

/-- 62-round variant of `foldlAcc_eq_stateVar63`, for the doubly-peeled loop that
    stops before the final two rounds (w62/w63 wide-absorption integration,
    ported from bufferhe4d's 166,935 submission). -/
lemma foldlAcc_eq_stateVar62 (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 62) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 62)
      (fun s (i : Fin 62) => subcircuit SHA256Round.circuit
        { state := s,
          k := constWord32 (Specs.SHA256.K[i.val]'(by omega)).toNat,
          w := input_var_schedule[i.val]'(by omega) })
      input_var_state ⟨k, h⟩ =
        stateVar i₀ input_var_state k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVar _ _ _

/-! ## Pure ℕ-level split lemmas (no circuit content)

Splitting the 64-round compression into 62 uniform rounds plus two final rounds,
for the w62/w63 wide-absorption integration (ported from bufferhe4d's 166,935
submission). -/

/-- Recursion equation of `valStateAfterRound`: for `k < 64`, round `k + 1` peels
    off one `sha256Round` application at index `k`. -/
lemma valStateAfterRound_succ (s : Vector ℕ 8) (w : Vector ℕ 64)
    (k : ℕ) (hk : k < 64) :
    valStateAfterRound s w (k + 1) =
      Specs.SHA256.sha256Round (valStateAfterRound s w k)
        (Specs.SHA256.K[k]'hk).toNat (w[k]'hk) := by
  rw [valStateAfterRound, dif_pos hk]

/-- The full 64-round compression equals 63 rounds followed by one last
    `sha256Round` at index 63. -/
lemma sha256Compress_split_last (s : Vector ℕ 8) (w : Vector ℕ 64) :
    Specs.SHA256.sha256Compress s w =
      Specs.SHA256.sha256Round (valStateAfterRound s w 63)
        (Specs.SHA256.K[63]).toNat w[63] := by
  rw [sha256Compress_eq_valStateAfterRound]
  show valStateAfterRound s w (63 + 1) = _
  exact valStateAfterRound_succ s w 63 (by omega)

/-- The full 64-round compression equals 62 rounds followed by two last
    `sha256Round` applications at indices 62 and 63. -/
lemma sha256Compress_split_last2 (s : Vector ℕ 8) (w : Vector ℕ 64) :
    Specs.SHA256.sha256Compress s w =
      Specs.SHA256.sha256Round
        (Specs.SHA256.sha256Round (valStateAfterRound s w 62)
          (Specs.SHA256.K[62]).toNat w[62]) (Specs.SHA256.K[63]).toNat w[63] := by
  have h63 : valStateAfterRound s w 63 =
      Specs.SHA256.sha256Round (valStateAfterRound s w 62) (Specs.SHA256.K[62]).toNat w[62] :=
    valStateAfterRound_succ s w 62 (by omega)
  rw [sha256Compress_split_last, h63]

/-- `valStateAfterRound` at bound `m ≤ 64` depends only on the schedule words
    `< m`: two schedules agreeing there give equal states. -/
lemma valStateAfterRound_congr (s : Vector ℕ 8) (w w' : Vector ℕ 64) (m : ℕ) (hm : m ≤ 64)
    (h : ∀ j (hj : j < 64), j < m → w[j]'hj = w'[j]'hj) :
    valStateAfterRound s w m = valStateAfterRound s w' m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have hk : k < 64 := by omega
    have ih' := ih (by omega) (fun j hj hlt => h j hj (Nat.lt_succ_of_lt hlt))
    rw [valStateAfterRound_succ s w k hk, valStateAfterRound_succ s w' k hk, ih',
      h k hk (Nat.lt_succ_self k)]

/-- Indexing into `compressBlock`: entry `i` is the feed-forward `add32` of the
    input state with the compressed state over the message schedule. -/
lemma compressBlock_getElem (s : Vector ℕ 8) (b : Vector ℕ 16)
    (i : ℕ) (hi : i < 8) :
    (Specs.SHA256.compressBlock s b)[i] =
      add32 (s[i])
        ((Specs.SHA256.sha256Compress s (Specs.SHA256.messageSchedule b))[i]) := by
  simp only [Specs.SHA256.compressBlock, Vector.getElem_mapFinRange, Fin.getElem_fin]

end SHA256Rounds
end Solution.SHA256
end
