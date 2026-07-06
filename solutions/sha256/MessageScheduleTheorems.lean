import Solution.SHA256.ScheduleStep
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# Helper definitions and lemmas for `MessageSchedule`

The variable- and value-level schedule descriptions (`varSchedule` / `valSchedule`)
and the lemmas relating the `foldlRange` accumulator and the spec to them. The
per-step circuit now lives in the `ScheduleStep` gadget and `MessageSchedule.main`
inlines the fold over `subcircuit ScheduleStep.circuit`, so the bridges below are
phrased against that gadget. The gadget file keeps the six required declarations.
-/

namespace MessageSchedule

/-- Variable-level schedule after `k` expansion steps. Used as the explicit description
    of the foldlRange accumulator, mirroring `SHA256Rounds.stateVar`. -/
def varSchedule (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    ℕ → SHA256Schedule (Expression (F p))
  | 0 =>
    Vector.append input_var_block
      (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))
  | k + 1 =>
    if h : k < 48 then
      (varSchedule i₀ input_var_block k).set
        (k + 16) (varFromOffset (fields 32) (i₀ + k * 91 + 58)) (by omega)
    else
      varSchedule i₀ input_var_block k

/-- Value-level schedule after `k` expansion steps. -/
def valSchedule (input_block : Vector ℕ 16) : ℕ → Vector ℕ 64
  | 0 => Vector.mapFinRange 64 fun i => if h : i.val < 16 then input_block.get ⟨i.val, h⟩ else 0
  | k + 1 =>
    if h : k < 48 then
      let prev := valSchedule input_block k
      let wj := _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 prev[k + 16 - 2]) prev[k + 16 - 7])
        (_root_.add32 (Specs.SHA256.lowerSigma0 prev[k + 16 - 15]) prev[k + 16 - 16])
      prev.set (k + 16) wj (by omega)
    else
      valSchedule input_block k

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- `Specs.SHA256.messageSchedule` equals our `valSchedule` at index 48. -/
lemma messageSchedule_eq_valSchedule (input_block : Vector ℕ 16) :
    Specs.SHA256.messageSchedule input_block = valSchedule input_block 48 := by
  simp only [Specs.SHA256.messageSchedule]
  -- Generic step body, independent of the foldl bound, so the IH on `k` matches
  -- the new occurrence in `Fin.foldl_succ_last`.
  set body : Vector ℕ 64 → ℕ → Vector ℕ 64 := fun w n =>
    if h : n < 48 then
      have hj   : n + 16     < 64 := by omega
      let wj := _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 w[n + 16 - 2]) w[n + 16 - 7])
        (_root_.add32 (Specs.SHA256.lowerSigma0 w[n + 16 - 15]) w[n + 16 - 16])
      w.set (n + 16) wj hj
    else w with hbody_def
  set init : Vector ℕ 64 :=
    Vector.mapFinRange 64 fun i => if h : i.val < 16 then input_block.get ⟨i.val, h⟩ else 0
  -- Rephrase RHS bodies in terms of `body`.
  have hspec : Fin.foldl 48 (fun w (i : Fin 48) =>
      w.set (i.val + 16)
        (_root_.add32 (_root_.add32 (Specs.SHA256.lowerSigma1 w[i.val + 16 - 2]) w[i.val + 16 - 7])
          (_root_.add32 (Specs.SHA256.lowerSigma0 w[i.val + 16 - 15]) w[i.val + 16 - 16]))
        (by have := i.isLt; omega)) init =
      Fin.foldl 48 (fun w (i : Fin 48) => body w i.val) init := by
    congr 1; funext w i
    have hi : i.val < 48 := i.isLt
    simp only [hbody_def, dif_pos hi]
  rw [hspec]
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k (fun w (i : Fin k) => body w i.val) init =
        valSchedule input_block k by
    have h48 := h 48 (le_refl 48)
    convert h48 using 1
  intro k hk
  induction k with
  | zero => simp [valSchedule, Fin.foldl_zero, init]
  | succ k ih =>
    rw [Fin.foldl_succ_last, valSchedule]
    have hk' : k ≤ 48 := by omega
    specialize ih hk'
    rw [show (fun w (i : Fin k) => body w i.castSucc.val) =
           (fun w (i : Fin k) => body w i.val) from rfl, ih]
    simp only [Fin.val_last, hbody_def, dif_pos (show k < 48 from by omega)]

/-- The localLength of `ScheduleStep.circuit` is the constant 91. -/
@[simp] lemma scheduleStep_localLength (b : ScheduleStep.Inputs (Expression (F p))) :
    ScheduleStep.circuit.localLength b = 91 := rfl

/-- The output of `ScheduleStep.circuit` at offset `n` is the word at relative offset 58. -/
@[simp] lemma scheduleStep_output (b : ScheduleStep.Inputs (Expression (F p))) (n : ℕ) :
    ScheduleStep.circuit.output b n = varFromOffset (fields 32) (n + 58) := rfl

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- The 48-step `Fin.foldl` of the (circuit_norm–reduced) variable-level schedule body
    equals `varSchedule 48`. Used by the elaborated instance. -/
lemma finFoldl_eq_varSchedule_48 (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    Fin.foldl 48
      (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin 48) =>
        acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 91 + 58))
          (by have := i.isLt; omega))
      (Vector.append input_var_block
        (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
      varSchedule i₀ input_var_block 48 := by
  suffices h : ∀ k (hk : k ≤ 48),
      Fin.foldl k
        (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
          acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 91 + 58))
            (by have := i.isLt; omega))
        (Vector.append input_var_block
          (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
        (show Vector (fields 32 (Expression (F p))) (16 + 48) from
          varSchedule i₀ input_var_block k) by
    have := h 48 (le_refl 48)
    convert this using 2
  intro k hk
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk' : k ≤ 48 := by omega
    have hk'' : k < 48 := by omega
    specialize ih hk'
    rw [Fin.foldl_succ_last]
    rw [show Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            acc.set (i.castSucc.val + 16) (varFromOffset (fields 32) (i₀ + i.castSucc.val * 91 + 58))
              (by have := i.isLt; omega))
            _ =
        Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 91 + 58))
              (by have := i.isLt; omega))
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [varSchedule, dif_pos hk'']

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 48` equals `varSchedule i₀ input_var k`.
    Phrased against the inlined fold body (the `circuit_norm`-reduced
    `subcircuit ScheduleStep.circuit` then `set`). -/
lemma foldlAcc_eq_varSchedule (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p)))
    (k : ℕ) (h : k < 48) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 48)
      (fun (w : SHA256Schedule (Expression (F p))) (i : Fin 48) (n : ℕ) =>
        (Vector.set w (i.val + 16)
            (ScheduleStep.circuit.output
              ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
               w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩ n)
            (by omega),
          [Operation.subcircuit (ScheduleStep.circuit.toSubcircuit n
            ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
             w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩)]))
      (Vector.append input_var_block (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p)))))
      ⟨k, h⟩ =
        varSchedule i₀ input_var_block k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk : k < 48 := by omega
    specialize ih hk
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, varSchedule, dif_pos hk]
    simp only [Circuit.output, Circuit.localLength, scheduleStep_output, scheduleStep_localLength,
      circuit_norm]

/-! ## 46-step corollaries (ported from bufferhe4d's 166,935 submission)

`varSchedule` / `valSchedule` are step-count-parametric (their `k < 48` guard covers
every `k ≤ 46`), so the 46-step variant reuses them unchanged. Only the two fold
bridges below are hardwired to the fold bound (they mention `Fin 48` /
`Vector.finRange 48` in their statements), so we restate them at 46 — same proofs,
with the `dif_pos` guard `k < 48` discharged from `k < 46` by `omega`.
-/

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- One expansion step leaves all slots other than `k + 16` unchanged. -/
lemma valSchedule_succ_getElem_ne (input_block : Vector ℕ 16) (k : ℕ) (hk : k < 48)
    (j : ℕ) (hj : j < 64) (hne : k + 16 ≠ j) :
    (valSchedule input_block (k + 1))[j]'hj = (valSchedule input_block k)[j]'hj := by
  simp only [valSchedule, dif_pos hk]
  exact Vector.getElem_set_ne (by omega) hj hne

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- For indices `< 62`, the spec-level schedule agrees with `valSchedule` at 46: steps
    46 and 47 only write slots 62 and 63. This is the per-index spec bridge for the
    46-step variant (the analogue of `messageSchedule_eq_valSchedule`). -/
lemma messageSchedule_getElem_eq_valSchedule_46 (input_block : Vector ℕ 16)
    (j : ℕ) (hj : j < 62) :
    (Specs.SHA256.messageSchedule input_block)[j]'(by omega) =
      (valSchedule input_block 46)[j]'(by omega) := by
  have h47 : (valSchedule input_block 48)[j]'(by omega) =
      (valSchedule input_block 47)[j]'(by omega) :=
    valSchedule_succ_getElem_ne input_block 47 (by omega) j (by omega) (by omega)
  have h46 : (valSchedule input_block 47)[j]'(by omega) =
      (valSchedule input_block 46)[j]'(by omega) :=
    valSchedule_succ_getElem_ne input_block 46 (by omega) j (by omega) (by omega)
  rw [messageSchedule_eq_valSchedule]
  exact h47.trans h46

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- One expansion step writes slot `k + 16` with the step recurrence value. -/
lemma valSchedule_succ_getElem_self (input_block : Vector ℕ 16) (k : ℕ) (hk : k < 48) :
    (valSchedule input_block (k + 1))[k + 16]'(by omega) =
      _root_.add32
        (_root_.add32 (Specs.SHA256.lowerSigma1 ((valSchedule input_block k)[k + 16 - 2]'(by omega)))
          ((valSchedule input_block k)[k + 16 - 7]'(by omega)))
        (_root_.add32 (Specs.SHA256.lowerSigma0 ((valSchedule input_block k)[k + 16 - 15]'(by omega)))
          ((valSchedule input_block k)[k + 16 - 16]'(by omega))) := by
  simp only [valSchedule, dif_pos hk]
  rw [Vector.getElem_set_self]

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- Spec bridge for schedule word 62: `messageSchedule[62]` is the mod-`2^32`
    reduction of the exact ℕ step sum over words 60/55/47/46 — matching the
    `ScheduleStepLast` output value for `⟨w60, w55, w47, w46⟩`. -/
lemma messageSchedule_getElem_62 (input_block : Vector ℕ 16) :
    (Specs.SHA256.messageSchedule input_block)[62]'(by norm_num) =
      (Specs.SHA256.lowerSigma1 ((Specs.SHA256.messageSchedule input_block)[60]'(by norm_num))
       + (Specs.SHA256.messageSchedule input_block)[55]'(by norm_num)
       + Specs.SHA256.lowerSigma0 ((Specs.SHA256.messageSchedule input_block)[47]'(by norm_num))
       + (Specs.SHA256.messageSchedule input_block)[46]'(by norm_num)) % 2 ^ 32 := by
  have h60 := messageSchedule_getElem_eq_valSchedule_46 input_block 60 (by norm_num)
  have h55 := messageSchedule_getElem_eq_valSchedule_46 input_block 55 (by norm_num)
  have h47 := messageSchedule_getElem_eq_valSchedule_46 input_block 47 (by norm_num)
  have h46 := messageSchedule_getElem_eq_valSchedule_46 input_block 46 (by norm_num)
  have hlhs : (valSchedule input_block 48)[62]'(by norm_num)
      = (valSchedule input_block 47)[62]'(by norm_num) :=
    valSchedule_succ_getElem_ne input_block 47 (by norm_num) 62 (by norm_num) (by norm_num)
  have hself : (valSchedule input_block 47)[62]'(by norm_num)
      = _root_.add32
          (_root_.add32 (Specs.SHA256.lowerSigma1 ((valSchedule input_block 46)[60]'(by norm_num)))
            ((valSchedule input_block 46)[55]'(by norm_num)))
          (_root_.add32 (Specs.SHA256.lowerSigma0 ((valSchedule input_block 46)[47]'(by norm_num)))
            ((valSchedule input_block 46)[46]'(by norm_num))) :=
    valSchedule_succ_getElem_self input_block 46 (by norm_num)
  rw [h60, h55, h47, h46, messageSchedule_eq_valSchedule, hlhs, hself]
  unfold _root_.add32
  omega

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- Spec bridge for schedule word 63: `messageSchedule[63]` is the mod-`2^32`
    reduction of the exact ℕ step sum over words 61/56/48/47. -/
lemma messageSchedule_getElem_63 (input_block : Vector ℕ 16) :
    (Specs.SHA256.messageSchedule input_block)[63]'(by norm_num) =
      (Specs.SHA256.lowerSigma1 ((Specs.SHA256.messageSchedule input_block)[61]'(by norm_num))
       + (Specs.SHA256.messageSchedule input_block)[56]'(by norm_num)
       + Specs.SHA256.lowerSigma0 ((Specs.SHA256.messageSchedule input_block)[48]'(by norm_num))
       + (Specs.SHA256.messageSchedule input_block)[47]'(by norm_num)) % 2 ^ 32 := by
  have h61 := messageSchedule_getElem_eq_valSchedule_46 input_block 61 (by norm_num)
  have h56 := messageSchedule_getElem_eq_valSchedule_46 input_block 56 (by norm_num)
  have h48 := messageSchedule_getElem_eq_valSchedule_46 input_block 48 (by norm_num)
  have h47 := messageSchedule_getElem_eq_valSchedule_46 input_block 47 (by norm_num)
  have n61 : (valSchedule input_block 47)[61]'(by norm_num) = (valSchedule input_block 46)[61]'(by norm_num) :=
    valSchedule_succ_getElem_ne input_block 46 (by norm_num) 61 (by norm_num) (by norm_num)
  have n56 : (valSchedule input_block 47)[56]'(by norm_num) = (valSchedule input_block 46)[56]'(by norm_num) :=
    valSchedule_succ_getElem_ne input_block 46 (by norm_num) 56 (by norm_num) (by norm_num)
  have n48 : (valSchedule input_block 47)[48]'(by norm_num) = (valSchedule input_block 46)[48]'(by norm_num) :=
    valSchedule_succ_getElem_ne input_block 46 (by norm_num) 48 (by norm_num) (by norm_num)
  have n47 : (valSchedule input_block 47)[47]'(by norm_num) = (valSchedule input_block 46)[47]'(by norm_num) :=
    valSchedule_succ_getElem_ne input_block 46 (by norm_num) 47 (by norm_num) (by norm_num)
  have hself : (valSchedule input_block 48)[63]'(by norm_num)
      = _root_.add32
          (_root_.add32 (Specs.SHA256.lowerSigma1 ((valSchedule input_block 47)[61]'(by norm_num)))
            ((valSchedule input_block 47)[56]'(by norm_num)))
          (_root_.add32 (Specs.SHA256.lowerSigma0 ((valSchedule input_block 47)[48]'(by norm_num)))
            ((valSchedule input_block 47)[47]'(by norm_num))) :=
    valSchedule_succ_getElem_self input_block 47 (by norm_num)
  rw [h61, h56, h48, h47, messageSchedule_eq_valSchedule, hself, n61, n56, n48, n47]
  unfold _root_.add32
  omega

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] in
/-- The 46-step `Fin.foldl` of the (circuit_norm–reduced) variable-level schedule body
    equals `varSchedule 46`. Used by the `elaborated46` instance. -/
lemma finFoldl_eq_varSchedule_46 (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p))) :
    Fin.foldl 46
      (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin 46) =>
        acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 91 + 58))
          (by have := i.isLt; omega))
      (Vector.append input_var_block
        (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
      varSchedule i₀ input_var_block 46 := by
  suffices h : ∀ k (hk : k ≤ 46),
      Fin.foldl k
        (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
          acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 91 + 58))
            (by have := i.isLt; omega))
        (Vector.append input_var_block
          (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))) =
        (show Vector (fields 32 (Expression (F p))) (16 + 48) from
          varSchedule i₀ input_var_block k) by
    have := h 46 (by omega)
    convert this using 2
  intro k hk
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk' : k ≤ 46 := by omega
    have hk'' : k < 48 := by omega
    specialize ih hk'
    rw [Fin.foldl_succ_last]
    rw [show Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            acc.set (i.castSucc.val + 16) (varFromOffset (fields 32) (i₀ + i.castSucc.val * 91 + 58))
              (by have := i.isLt; omega))
            _ =
        Fin.foldl k
          (fun (acc : SHA256Schedule (Expression (F p))) (i : Fin k) =>
            acc.set (i.val + 16) (varFromOffset (fields 32) (i₀ + i.val * 91 + 58))
              (by have := i.isLt; omega))
            _ from rfl, ih]
    simp only [Fin.val_last]
    rw [varSchedule, dif_pos hk'']

/-- 46-step variant of `foldlAcc_eq_varSchedule`, for the fold that stops after
    producing `w[61]` (slots 62/63 keep the accumulator's initial zero words). -/
lemma foldlAcc_eq_varSchedule46 (i₀ : ℕ) (input_var_block : SHA256Block (Expression (F p)))
    (k : ℕ) (h : k < 46) :
    Circuit.FoldlM.foldlAcc i₀ (Vector.finRange 46)
      (fun (w : SHA256Schedule (Expression (F p))) (i : Fin 46) (n : ℕ) =>
        (Vector.set w (i.val + 16)
            (ScheduleStep.circuit.output
              ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
               w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩ n)
            (by omega),
          [Operation.subcircuit (ScheduleStep.circuit.toSubcircuit n
            ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
             w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩)]))
      (Vector.append input_var_block (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p)))))
      ⟨k, h⟩ =
        varSchedule i₀ input_var_block k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  induction k with
  | zero => simp [varSchedule, Fin.foldl_zero]
  | succ k ih =>
    have hk : k < 46 := by omega
    specialize ih hk
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, varSchedule, dif_pos (show k < 48 by omega)]
    simp only [Circuit.output, Circuit.localLength, scheduleStep_output, scheduleStep_localLength,
      circuit_norm]

end MessageSchedule
end Solution.SHA256
end
