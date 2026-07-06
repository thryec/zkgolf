import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEqXV

/-!
# Grouped base-`2^B` equality with **two-sided** per-coefficient windows (`GroupedEqD`)

`GroupedEqD` is `GroupedEqXV` with the per-coefficient bounds generalized from
one-sided (`coeff.val < Nf j`) to **two-sided signed windows**: each coefficient
difference `lhs_j − rhs_j` is assumed to be the field image of an integer in
`(−NfN j, NfP j)` (`V.Nf` plays `NfP`, the positive flank; `VR.Nf` plays `NfN`,
the negative flank). The *circuit* is identical to `GroupedEqXV`'s — the same
`G − 2` graduated affine carry range checks (offsets `VR.OFFf`, widths `V.Wf`)
plus one final mod-`p` `polyEval` row — only the soundness/completeness reading
changes: the carry chain pins the **ℤ-valued** difference polynomial to zero.

This matters for balanced-digit operands: with signed residue digits the
difference flanks `NfP/NfN` are far narrower than any one-sided window
containing the two-sided spread, so the carry widths (≈ `log₂(offP + offN)`)
shrink accordingly.

The proof mirrors `GroupedEqXV`'s architecture with the coefficient digits
lifted to ℤ (`zsval`: `val` below the positive threshold, `val − p` above).
Two structural simplifications fall out of the two-sided reading:

* soundness: the per-boundary ℕ-lift (`per_index_lift2`) becomes a single
  ℤ-cast injectivity step on the difference identity;
* completeness: the honest ℤ prefix differences are **exactly divisible** by
  the boundary weights (the top difference is `0` by the spec, and higher
  groups only add multiples), so the honest carries are exact quotients — the
  remainder-matching argument of `GroupedEqXV` disappears.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {L : ℕ} [NeZero L]

namespace GroupedEqD

open GroupedEqX (groupExprW groupExprW_eval InputsX CoeffsX)
open GroupedEqXV (carryExpr carryLoop widthAllocFrom widthConsFrom)

/-! ## ℤ-lift helpers -/

/-- Signed window reading of a field element: `val` below the positive
threshold `N`, `val − p` at or above it (the negative flank). -/
def zsval (N : ℕ) (x : F p) : ℤ :=
  if x.val < N then (x.val : ℤ) else (x.val : ℤ) - (p : ℤ)

/-- `zsval` is a section of the field cast. -/
lemma zsval_cast (N : ℕ) (x : F p) : ((zsval N x : ℤ) : F p) = x := by
  unfold zsval
  split
  · rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_self, sub_zero]

/-- Uniqueness of the windowed ℤ-lift: any integer in the window `(−Nn, N)`
casting to `x` is `zsval N x`, provided the window fits the field. -/
lemma zsval_eq_of_window {N Nn : ℕ} {x : F p} {z : ℤ}
    (hcast : ((z : ℤ) : F p) = x) (hlo : -(Nn : ℤ) < z) (hhi : z < (N : ℤ))
    (hNp : N + Nn ≤ p) : zsval N x = z := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases hz : 0 ≤ z
  · -- z ∈ [0, N): the val is z itself
    have hzN : z.toNat < N := by omega
    have hcast2 : ((z.toNat : ℕ) : F p) = x := by
      rw [← hcast]
      conv_rhs => rw [← Int.toNat_of_nonneg hz]
      rw [Int.cast_natCast]
    have hxval : x.val = z.toNat := by
      rw [← hcast2, ZMod.val_natCast_of_lt (by omega)]
    unfold zsval
    rw [hxval, if_pos hzN]
    omega
  · -- z ∈ (−Nn, 0): the val is z + p, at or above the threshold
    push_neg at hz
    have hzp : (0 : ℤ) ≤ z + p := by omega
    have hcast2 : (((z + p).toNat : ℕ) : F p) = x := by
      rw [← hcast]
      have h2 : ((z : ℤ) : F p) = (((z + p).toNat : ℤ) : F p) := by
        rw [Int.toNat_of_nonneg hzp]
        push_cast
        rw [ZMod.natCast_self]
        ring
      rw [h2, Int.cast_natCast]
    have hlt : (z + p).toNat < p := by omega
    have hxval : x.val = (z + p).toNat := by
      rw [← hcast2, ZMod.val_natCast_of_lt hlt]
    unfold zsval
    rw [hxval, if_neg (by omega)]
    omega

/-- ℤ-cast injectivity on a `p`-window: two integers with equal field images
and difference bounded by `p` in both directions are equal. -/
lemma intCast_inj_of_lt {x y : ℤ} (h : ((x : ℤ) : F p) = (y : F p))
    (h1 : x - y < p) (h2 : y - x < p) : x = y := by
  have hd : (p : ℤ) ∣ (x - y) := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
  obtain ⟨c, hc⟩ := hd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h3 : (p : ℤ) * c < p := by rw [← hc]; exact h1
  have h4 : -(p : ℤ) < p * c := by
    have : -(x - y) < p := by omega
    rw [hc] at this
    omega
  have hc1 : c < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hc2 : -1 < c := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hc0 : c = 0 := by omega
  rw [hc0, mul_zero] at hc
  omega

/-- A multiple of `p` bounded by `p` in both directions is zero. -/
lemma int_eq_zero_of_dvd_of_lt {x : ℤ} (hd : (p : ℤ) ∣ x)
    (h1 : x < p) (h2 : -x < p) : x = 0 := by
  obtain ⟨c, hc⟩ := hd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h3 : (p : ℤ) * c < p := by rw [← hc]; exact h1
  have h4 : -((p : ℤ) * c) < p := by rw [← hc]; exact h2
  have hc1 : c < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hc2 : -1 < c := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hc0 : c = 0 := by omega
  rw [hc0, mul_zero] at hc
  omega

/-- Mixed-radix flattening over ℤ (clone of `group_flatten_sched`). -/
lemma group_flatten_schedZ (B : ℕ) (gf posOf : ℕ → ℕ) (f : ℕ → ℤ)
    (hpos0 : posOf 0 = 0) (hposS : ∀ k, posOf (k + 1) = posOf k + gf k) :
    ∀ G : ℕ, (∑ j ∈ Finset.range G,
        (∑ i ∈ Finset.range (gf j), f (posOf j + i) * 2 ^ (B * i)) * 2 ^ (B * posOf j))
      = ∑ t ∈ Finset.range (posOf G), f t * 2 ^ (B * t) := by
  intro G
  induction G with
  | zero => rw [hpos0]; simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hposS n, Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show B * (posOf n + i) = B * i + B * posOf n from by ring, pow_add]
    ring

/-- Zero-tail extension over ℤ (clone of `GroupedEq.sum_extend_zero`). -/
lemma sum_extend_zeroZ (B N M : ℕ) (f : ℕ → ℤ) (hNM : N ≤ M)
    (hf : ∀ t, N ≤ t → f t = 0) :
    (∑ t ∈ Finset.range N, f t * 2 ^ (B * t)) = ∑ t ∈ Finset.range M, f t * 2 ^ (B * t) := by
  apply Finset.sum_subset
    (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hNM))
  intro x _ hx
  simp only [Finset.mem_range, not_lt] at hx
  rw [hf x hx, zero_mul]

/-- Mixed-radix carry telescoping over ℤ (clone of `carry_telescope_e`). -/
lemma carry_telescope_eZ (e : ℕ → ℕ) (C : ℕ → ℤ) :
    ∀ n : ℕ,
      (∑ k ∈ Finset.range n, (if k = 0 then 0 else C (k - 1)) * 2 ^ (e k))
        + (if n = 0 then 0 else C (n - 1) * 2 ^ (e n))
      = ∑ k ∈ Finset.range n, C k * 2 ^ (e (k + 1)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [if_neg (by omega : n + 1 ≠ 0)] at *
      rw [if_neg (by omega : n ≠ 0)] at ih ⊢
      simp only [Nat.add_sub_cancel] at *
      linarith

/-- Split a four-term no-wrap sum bound into its component bounds. -/
private lemma sum4_lt {a b c d q : ℕ} (h : a + b + c + d < q) :
    a < q ∧ b < q ∧ c < q ∧ d < q := by omega

/-- Split a five-term no-wrap sum bound into its component bounds. -/
private lemma sum5_lt {a b c d e q : ℕ} (h : a + b + c + d + e < q) :
    a < q ∧ b < q ∧ c < q ∧ d < q ∧ e < q := by omega

/-! ## Hypotheses -/

/-- Hypotheses for the two-sided graduated grouping: exactly the `GroupedEqXV`
schedule conditions with `V.Nf` read as the strict *positive* difference-flank
bound `NfP` and `VR.Nf` as the strict *negative* flank bound `NfN`, plus the
window-fits-field condition needed for the ℤ-lift to be well-defined. -/
def GVDHyps (p L : ℕ) (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ)
    (V VR : GroupedEqV.VParams) : Prop :=
  GroupedEqXV.GVXHyps p L B gf posOf G V VR ∧
  ∀ j, j < L → V.Nf j + VR.Nf j ≤ p

/-! ## The `main` circuit (identical to `GroupedEqXV.main`) -/

/-- The `main` circuit of `GroupedEqD`: range-check the affinely determined
offset carries at the `G−2` checked group boundaries — each at its own width —
then assert only the final mod-`p` `polyEval` row. Structurally identical to
`GroupedEqXV.main`. -/
def main (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (InputsX L) (F p)) :
    Circuit (F p) Unit := do
  let Pc := input.lhs
  let Sc := input.rhs
  carryLoop B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 Pc Sc (G - 2) 0
  assertZero
    (MulMod.polyEvalExpr
      (Vector.ofFn fun j : Fin L => Pc[j.val]'j.isLt - Sc[j.val]'j.isLt)
      ((2 : F p) ^ B))

instance elaborated (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsX L) unit (main B gf posOf G V VR hgv) where
  localLength _ := widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm,
      GroupedEqXV.carryLoop_localLength B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1
        input.lhs input.rhs]
  subcircuitsConsistent := by
    intro input offset
    have key : ∀ off, Operations.forAll off { subcircuit := fun off {n} _ => n = off }
        ((carryLoop B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 input.lhs input.rhs
          (G - 2) 0).operations off) :=
      fun off => GroupedEqXV.carryLoop_subcircuitsConsistent B gf posOf VR.OFFf V.Wf
        hgv.1.2.2.2.1 _ _ _ _ off
    simp only [main, circuit_norm]
    ring_nf
    apply key
  channelsLawful := by
    intro input offset
    simp only [main, Circuit.bind_operations_eq]
    refine Operations.channelsLawful_append_of_channelsLawful
      (GroupedEqXV.carryLoop_channelsLawful B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 _ _ _ _ _) ?_
    simp only [circuit_norm]

/-! ## Assumptions and Spec -/

/-- Per-position preconditions: each coefficient difference is the field image
of an integer in the two-sided window `(−NfN k, NfP k)`. -/
def Assumptions (NfP NfN : ℕ → ℕ) (input : InputsX L (F p)) : Prop :=
  ∀ k : Fin L, ∃ z : ℤ,
    ((z : ℤ) : F p) = input.lhs[k.val] - input.rhs[k.val] ∧
    -(NfN k.val : ℤ) < z ∧ z < (NfP k.val : ℤ)

/-- Postcondition: the ℤ-valued difference polynomial (coefficients read
through the windowed lift `zsval`) vanishes. -/
def Spec (B : ℕ) (NfP : ℕ → ℕ) (input : InputsX L (F p)) : Prop :=
  (∑ k : Fin L,
    zsval (NfP k.val) (input.lhs[k.val] - input.rhs[k.val]) * 2 ^ (B * k.val)) = 0

set_option maxHeartbeats 4000000 in
/-- The `GroupedEqD` formal assertion: two coefficient sequences whose
differences sit in per-position two-sided windows encode the same ℤ value in
base `2^B`, at the graduated cost `Σ_k (Wf k − 1)` carry witnesses plus one
final mod-`p` row. -/
def circuit (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (InputsX L) where
    main := main B gf posOf G V VR hgv
    Assumptions := Assumptions V.Nf VR.Nf
    Spec := Spec B V.Nf
    soundness := by
      obtain ⟨⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, htrunc⟩, hNfp⟩ := hgv
      circuit_proof_start
      obtain ⟨h_loop, h_lin⟩ := h_holds
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have h_range := GroupedEqXV.carryLoop_soundness B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs input_var.rhs (G - 2) 0 i₀ h_loop
      -- window facts, re-indexed over plain ℕ positions
      have hAs : ∀ (k : ℕ) (h : k < L), ∃ z : ℤ,
          ((z : ℤ) : F p) = input.lhs[k]'h - input.rhs[k]'h ∧
          -(VR.Nf k : ℤ) < z ∧ z < (V.Nf k : ℤ) :=
        fun k h => h_assumptions ⟨k, h⟩
      -- signed difference digits (vanish beyond L)
      set Dz : ℕ → ℤ := fun k => if h : k < L
        then zsval (V.Nf k) (input.lhs[k]'h - input.rhs[k]'h) else 0 with hDz
      have hDz_hi : ∀ k, Dz k < (V.Nf k : ℤ) := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzhi
        · have := (hNf1 k).1
          exact_mod_cast this
      have hDz_lo : ∀ k, -(VR.Nf k : ℤ) < Dz k := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzlo
        · have := (hNf1 k).2
          have h0 : (0 : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast this
          omega
      -- group difference digits
      set QD : ℕ → ℤ := fun j => ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i)
        with hQD
      have hQD_app : ∀ j, QD j = ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- effective offsets (0 at the top) and carries (0 at the top)
      set OFFe : ℕ → ℕ := fun k => if k = G - 1 then 0 else VR.OFFf k with hOFFe
      set Cn : ℕ → ℕ := fun k => if k = G - 1 then 0
        else (Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs input_var.rhs k)).val
        with hCn
      have hCn_lt : ∀ k, k < G - 2 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        simpa using h_range k hk
      -- group digit bounds
      have hSfP : ∀ k, QD k
          ≤ ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ) := by
        intro k
        rw [hQD_app]
        push_cast
        apply Finset.sum_le_sum
        intro i _
        have h1 := hDz_hi (posOf k + i)
        have h2 := (hNf1 (posOf k + i)).1
        have hle : Dz (posOf k + i) ≤ ((V.Nf (posOf k + i) - 1 : ℕ) : ℤ) := by omega
        exact mul_le_mul_of_nonneg_right hle (by positivity)
      have hSfN : ∀ k, -((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
          ≤ QD k := by
        intro k
        rw [hQD_app]
        push_cast
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro i _
        have h1 := hDz_lo (posOf k + i)
        have h2 := (hNf1 (posOf k + i)).2
        have hle : -((VR.Nf (posOf k + i) - 1 : ℕ) : ℤ) ≤ Dz (posOf k + i) := by omega
        calc -(((VR.Nf (posOf k + i) - 1 : ℕ) : ℤ) * 2 ^ (B * i))
            = (-((VR.Nf (posOf k + i) - 1 : ℕ) : ℤ)) * 2 ^ (B * i) := by ring
          _ ≤ Dz (posOf k + i) * 2 ^ (B * i) :=
              mul_le_mul_of_nonneg_right hle (by positivity)
      have hpBg : ∀ k, k < G - 1 → 2 ^ (B * gf k) < p := fun k hk =>
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
          (sum5_lt (hper k hk).2.2).2.2.1
      have hbase_ne : ∀ k, k < G - 1 → ((2 : F p) ^ (B * gf k) ≠ 0) := by
        intro k hk
        have hnat : (((2 ^ (B * gf k) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * gf k) : ℕ) : F p).val) = 2 ^ (B * gf k) :=
            ZMod.val_natCast_of_lt (hpBg k hk)
          rw [hzero, ZMod.val_zero] at hval
          have : 0 < 2 ^ (B * gf k) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      -- eval bridges
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hDz_cast : ∀ (j : ℕ) (hj : j < L),
          ((Dz j : ℤ) : F p)
            = Expression.eval env (input_var.lhs[j]'hj)
              - Expression.eval env (input_var.rhs[j]'hj) := by
        intro j hj
        simp only [hDz, dif_pos hj]
        rw [zsval_cast, ha_e j hj, hb_e j hj]
      have hGD_e : ∀ j : ℕ,
          Expression.eval env (groupExprW B L gf posOf input_var.lhs j)
            - Expression.eval env (groupExprW B L gf posOf input_var.rhs j)
          = ((QD j : ℤ) : F p) := by
        intro j
        rw [groupExprW_eval, groupExprW_eval, hQD_app, ← Finset.sum_sub_distrib, Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [pow_mul]
        by_cases h : posOf j + i < L
        · rw [dif_pos h, dif_pos h, ← sub_mul]
          congr 1
          rw [hDz_cast (posOf j + i) h]
        · rw [dif_neg h, dif_neg h]
          simp only [hDz, dif_neg h]
          simp
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        rw [ZMod.natCast_zmod_val]
      -- per-group ℤ equation (interior boundaries only; the top is the mod-p rider)
      have h_idx : ∀ k, k < G - 2 →
          QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
            + (OFFe k : ℤ) * 2 ^ (B * gf k)
          = (Cn k : ℤ) * 2 ^ (B * gf k) + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) := by
        intro k hk
        have hktop : ¬ k = G - 1 := by omega
        have hOFFk : OFFe k = VR.OFFf k := by simp only [hOFFe, if_neg hktop]
        -- the field identity from the carry expression
        have hfield : ((QD k : ℤ) : F p)
            + (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p))
            + ((OFFe k : ℕ) : F p) * (2 ^ (B * gf k) : F p)
            = ((Cn k : ℕ) : F p) * (2 ^ (B * gf k) : F p)
              + (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p)) := by
          rw [hOFFk]
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            have hcarry := hcarry_eval 0 (by omega)
            simp only [↓reduceIte]
            rw [← hGD_e 0, ← hcarry]
            simp [carryExpr, Expression.eval]
            field_simp [hbase_ne 0 (by omega)]
            ring_nf
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            have hcarry := hcarry_eval (j + 1) (by omega)
            have hprev := hcarry_eval j (by omega)
            have hOFFj : OFFe j = VR.OFFf j := by
              simp only [hOFFe, if_neg (by omega : ¬ j = G - 1)]
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.succ_sub_one,
              Nat.add_sub_cancel, hOFFj]
            rw [← hGD_e (j + 1), ← hcarry]
            simp [carryExpr, Expression.eval, hprev]
            field_simp [hbase_ne (j + 1) (by omega)]
            ring_nf
        -- ℤ-lift via cast injectivity on the window
        have hnw := (hper k (by omega)).2.2
        have hcin_ub : (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ)) ≤ 2 ^ V.Wf (k - 1) := by
          split
          · positivity
          · have := hCn_lt (k - 1) (by omega)
            have : Cn (k - 1) ≤ 2 ^ V.Wf (k - 1) := by omega
            exact_mod_cast this
        have hcin_lb : (0 : ℤ) ≤ (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ)) := by
          split
          · omega
          · positivity
        have hoffp_ub : (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) ≤ 2 ^ V.Wf (k - 1) := by
          split
          · positivity
          · have hoe : OFFe (k - 1) = VR.OFFf (k - 1) := by
              simp only [hOFFe, if_neg (by omega : ¬ k - 1 = G - 1)]
            rw [hoe]
            have := (hper (k - 1) (by omega)).1
            have : VR.OFFf (k - 1) ≤ 2 ^ V.Wf (k - 1) := by omega
            exact_mod_cast this
        have hoffp_lb : (0 : ℤ) ≤ (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) := by
          split
          · omega
          · positivity
        have hcast_eq : (((QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)) : ℤ) : F p)
            = ((((Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))) : ℤ) : F p) := by
          push_cast
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            simpa using hfield
          · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
            have h := hfield
            rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)] at h
            push_cast at h ⊢
            convert h using 2 <;> push_cast <;> ring
        -- magnitude bounds for the injectivity window
        have hQDub := hSfP k
        have hQDlb := hSfN k
        have hCk : (Cn k : ℤ) * 2 ^ (B * gf k)
            ≤ ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by
          push_cast
          have h1 : (Cn k : ℤ) ≤ 2 ^ V.Wf k := by
            have := hCn_lt k hk
            have : Cn k ≤ 2 ^ V.Wf k := by omega
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        have hOFFk_mul : (OFFe k : ℤ) * 2 ^ (B * gf k)
            = ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by
          rw [hOFFk]
          push_cast
          ring
        have hnwZ : ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
            + ((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
            + ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ)
            + ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) + ((2 ^ V.Wf (k - 1) : ℕ) : ℤ)
            < (p : ℤ) := by
          exact_mod_cast hnw
        have hWprev_cast : ((2 ^ V.Wf (k - 1) : ℕ) : ℤ) = (2 : ℤ) ^ V.Wf (k - 1) := by
          push_cast
          ring
        refine intCast_inj_of_lt hcast_eq ?_ ?_
        · -- LHS − RHS < p
          have hRHS_nonneg : (0 : ℤ) ≤ (Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) := by
            have : (0 : ℤ) ≤ (Cn k : ℤ) * 2 ^ (B * gf k) := by positivity
            omega
          have hLHS_ub : QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)
              ≤ ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
                + 2 ^ V.Wf (k - 1) + ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by
            rw [hOFFk_mul]
            omega
          rw [hWprev_cast] at hnwZ
          have hSR0 : (0 : ℤ)
              ≤ ((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ) := by
            positivity
          have hCk0 : (0 : ℤ) ≤ ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by positivity
          omega
        · -- RHS − LHS < p
          have hLHS_lb : -((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
              ≤ QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
                + (OFFe k : ℤ) * 2 ^ (B * gf k) := by
            have h1 : (0 : ℤ) ≤ (OFFe k : ℤ) * 2 ^ (B * gf k) := by positivity
            omega
          have hRHS_ub : (Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))
              ≤ ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ) + 2 ^ V.Wf (k - 1) := by
            omega
          rw [hWprev_cast] at hnwZ
          have hSL0 : (0 : ℤ)
              ≤ ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ) := by
            positivity
          have hOFF0 : (0 : ℤ) ≤ ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by positivity
          omega
      -- the ℤ difference polynomial and its position form
      set PVZ : ℤ := ∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t) with hPVZ
      set n0 := G - 2 with hn0
      have hn0_pos : 1 ≤ n0 := by omega
      have hposn0_lt : posOf n0 < L := lt_of_le_of_lt (hposMono n0 (G - 1) (by omega)) hlast
      rw [show G - 3 = n0 - 1 from by omega] at htrunc
      set Wz : ℤ := 2 ^ (B * posOf n0) with hWz
      set SDlow : ℤ := ∑ k ∈ Finset.range n0, QD k * 2 ^ (B * posOf k) with hSDlow
      set TD : ℤ := ∑ t ∈ Finset.range (L - posOf n0), Dz (posOf n0 + t) * 2 ^ (B * t) with hTD
      have hF1 : PVZ = SDlow + Wz * TD := by
        rw [hPVZ]
        have hsplit : (∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t))
            = (∑ t ∈ Finset.range (posOf n0), Dz t * 2 ^ (B * t))
              + ∑ i ∈ Finset.range (L - posOf n0), Dz (posOf n0 + i) * 2 ^ (B * (posOf n0 + i)) := by
          conv_lhs => rw [show L = posOf n0 + (L - posOf n0) from by omega]
          rw [Finset.sum_range_add]
        rw [hsplit]
        congr 1
        · rw [hSDlow, ← group_flatten_schedZ B gf posOf Dz hpos0 hposS n0]
        · rw [hTD, hWz, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show B * (posOf n0 + i) = B * posOf n0 + B * i from by ring, pow_add]
          ring
      -- telescope the per-boundary identities
      have hsumlow : (∑ k ∈ Finset.range n0,
            (QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)) * 2 ^ (B * posOf k))
          = ∑ k ∈ Finset.range n0,
              ((Cn k : ℤ) * 2 ^ (B * gf k)
                + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))) * 2 ^ (B * posOf k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [h_idx k hk]
      have hLHSlow : (∑ k ∈ Finset.range n0,
            (QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)) * 2 ^ (B * posOf k))
          = SDlow
            + (∑ k ∈ Finset.range n0,
                (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ)) * 2 ^ (B * posOf k))
            + (∑ k ∈ Finset.range n0, (OFFe k : ℤ) * 2 ^ (B * posOf (k + 1))) := by
        rw [hSDlow, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [he k, pow_add]
        ring
      have hRHSlow : (∑ k ∈ Finset.range n0,
            ((Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))) * 2 ^ (B * posOf k))
          = (∑ k ∈ Finset.range n0, (Cn k : ℤ) * 2 ^ (B * posOf (k + 1)))
            + (∑ k ∈ Finset.range n0,
                (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) * 2 ^ (B * posOf k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [he k, pow_add]
        ring
      have htelC := carry_telescope_eZ (fun k => B * posOf k) (fun k => (Cn k : ℤ)) n0
      simp only [] at htelC
      rw [if_neg (by omega : ¬ (n0 = 0)), ← hWz] at htelC
      have htelO := carry_telescope_eZ (fun k => B * posOf k) (fun k => (OFFe k : ℤ)) n0
      simp only [] at htelO
      rw [if_neg (by omega : ¬ (n0 = 0)), ← hWz] at htelO
      have hdagger : SDlow + (OFFe (n0 - 1) : ℤ) * Wz = (Cn (n0 - 1) : ℤ) * Wz := by
        have key := hsumlow
        rw [hLHSlow, hRHSlow] at key
        linarith
      -- the final mod-p row pins the ℤ polynomial mod p
      have hPV_cast : ((PVZ : ℤ) : F p)
          = (∑ i : Fin L, Expression.eval env (input_var.lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
            - (∑ i : Fin L, Expression.eval env (input_var.rhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val) := by
        rw [← Finset.sum_sub_distrib, hPVZ,
          ← Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t)), Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [hDz_cast i.val i.isLt, ← pow_mul]
        ring
      have hMODP : ((PVZ : ℤ) : F p) = 0 := by
        have hd := GroupedEqXV.polyEvalExpr_diff_eval B env input_var.lhs input_var.rhs
        rw [h_lin] at hd
        rw [hPV_cast, ← hd]
      have hdvd : (p : ℤ) ∣ PVZ := by
        rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      -- factor out the boundary weight
      have hfact : PVZ = Wz * ((Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD) := by
        rw [hF1]
        have := hdagger
        ring_nf
        ring_nf at this
        linarith
      have hp2 : 2 < p := Fact.out
      have hdvdX : (p : ℤ) ∣ ((Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD) := by
        rw [hfact] at hdvd
        have h1 : p ∣ (Wz * ((Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD)).natAbs := by
          have h := Int.natAbs_dvd_natAbs.mpr hdvd
          rwa [Int.natAbs_natCast] at h
        rw [Int.natAbs_mul] at h1
        rcases ((Fact.out : p.Prime).dvd_mul).mp h1 with hl | hr
        · exfalso
          have hWabs : Wz.natAbs = 2 ^ (B * posOf n0) := by
            rw [hWz]
            simp [Int.natAbs_pow]
          rw [hWabs] at hl
          have h2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hl
          have := Nat.le_of_dvd (by norm_num) h2
          omega
        · exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hr)
      -- tail bounds
      have hTD_ub : TD
          < ((∑ t ∈ Finset.range (L - posOf n0), V.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ) := by
        rw [hTD]
        push_cast
        apply Finset.sum_lt_sum_of_nonempty
        · rw [Finset.nonempty_range_iff]
          omega
        · intro t _
          exact mul_lt_mul_of_pos_right (hDz_hi (posOf n0 + t)) (by positivity)
      have hTD_lb : -((∑ t ∈ Finset.range (L - posOf n0), VR.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ)
          < TD := by
        rw [hTD]
        push_cast
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_lt_sum_of_nonempty
        · rw [Finset.nonempty_range_iff]
          omega
        · intro t _
          have h1 := hDz_lo (posOf n0 + t)
          calc -(((VR.Nf (posOf n0 + t) : ℕ) : ℤ) * 2 ^ (B * t))
              = (-((VR.Nf (posOf n0 + t) : ℕ) : ℤ)) * 2 ^ (B * t) := by ring
            _ < Dz (posOf n0 + t) * 2 ^ (B * t) :=
                mul_lt_mul_of_pos_right h1 (by positivity)
      have hOFF_lt : OFFe (n0 - 1) < 2 ^ V.Wf (n0 - 1) := by
        have hOFFn0 : OFFe (n0 - 1) = VR.OFFf (n0 - 1) := by
          simp only [hOFFe, if_neg (by omega : ¬ n0 - 1 = G - 1)]
        rw [hOFFn0]
        have := (hper (n0 - 1) (by omega)).1
        omega
      have hCn_lt_b : Cn (n0 - 1) < 2 ^ V.Wf (n0 - 1) := hCn_lt (n0 - 1) (by omega)
      have htruncZ : ((2 ^ V.Wf (n0 - 1) : ℕ) : ℤ)
          + ((∑ t ∈ Finset.range (L - posOf n0), V.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ)
          + ((∑ t ∈ Finset.range (L - posOf n0), VR.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ)
          < (p : ℤ) := by
        exact_mod_cast htrunc
      have hX0 : (Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD = 0 := by
        apply int_eq_zero_of_dvd_of_lt hdvdX
        · have h1 : (Cn (n0 - 1) : ℤ) < ((2 ^ V.Wf (n0 - 1) : ℕ) : ℤ) := by
            exact_mod_cast hCn_lt_b
          have h2 : (0 : ℤ) ≤ (OFFe (n0 - 1) : ℤ) := by positivity
          omega
        · have h1 : (OFFe (n0 - 1) : ℤ) < ((2 ^ V.Wf (n0 - 1) : ℕ) : ℤ) := by
            exact_mod_cast hOFF_lt
          have h2 : (0 : ℤ) ≤ (Cn (n0 - 1) : ℤ) := by positivity
          omega
      have hPVZ0 : PVZ = 0 := by
        rw [hfact, hX0, mul_zero]
      -- conclude the Spec
      refine ⟨?_, GroupedEqXV.carryLoop_requirements B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs input_var.rhs _ _ _⟩
      show (∑ k : Fin L,
          zsval (V.Nf k.val) (input.lhs[k.val] - input.rhs[k.val]) * 2 ^ (B * k.val)) = 0
      rw [show (∑ k : Fin L,
          zsval (V.Nf k.val) (input.lhs[k.val] - input.rhs[k.val]) * 2 ^ (B * k.val))
        = ∑ k : Fin L, Dz k.val * 2 ^ (B * k.val) from by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          simp only [hDz, dif_pos k.isLt]]
      rw [Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t)), ← hPVZ]
      exact hPVZ0
    completeness := by
      obtain ⟨⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, _⟩, hNfp⟩ := hgv
      circuit_proof_start
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have hpBg : ∀ k, k < G - 1 → 2 ^ (B * gf k) < p := fun k hk =>
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
          (sum5_lt (hper k hk).2.2).2.2.1
      have hAs : ∀ (k : ℕ) (h : k < L), ∃ z : ℤ,
          ((z : ℤ) : F p) = input.lhs[k]'h - input.rhs[k]'h ∧
          -(VR.Nf k : ℤ) < z ∧ z < (V.Nf k : ℤ) :=
        fun k h => h_assumptions ⟨k, h⟩
      -- signed difference digits
      set Dz : ℕ → ℤ := fun k => if h : k < L
        then zsval (V.Nf k) (input.lhs[k]'h - input.rhs[k]'h) else 0 with hDz
      have hDz_hi : ∀ k, Dz k < (V.Nf k : ℤ) := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzhi
        · have := (hNf1 k).1
          exact_mod_cast this
      have hDz_lo : ∀ k, -(VR.Nf k : ℤ) < Dz k := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzlo
        · have := (hNf1 k).2
          have h0 : (0 : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast this
          omega
      set QD : ℕ → ℤ := fun j => ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i)
        with hQD
      have hQD_app : ∀ j, QD j = ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- ℤ prefix sums and boundary weights
      set SD : ℕ → ℤ := fun k => ∑ j ∈ Finset.range (k + 1), QD j * 2 ^ (B * posOf j) with hSD
      set Dkz : ℕ → ℤ := fun k => 2 ^ (B * posOf (k + 1)) with hDkz
      have hSD_app : ∀ k, SD k = ∑ j ∈ Finset.range (k + 1), QD j * 2 ^ (B * posOf j) :=
        fun _ => rfl
      have hDkz_app : ∀ k, Dkz k = 2 ^ (B * posOf (k + 1)) := fun _ => rfl
      have hDkz_pos : ∀ k, (0 : ℤ) < Dkz k := by
        intro k
        rw [hDkz_app]
        positivity
      -- the spec pins the top prefix to zero
      have hPVZ0 : (∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t)) = 0 := by
        have hs : (∑ k : Fin L,
            zsval (V.Nf k.val) (input.lhs[k.val] - input.rhs[k.val]) * 2 ^ (B * k.val)) = 0 :=
          h_spec
        rw [show (∑ k : Fin L,
            zsval (V.Nf k.val) (input.lhs[k.val] - input.rhs[k.val]) * 2 ^ (B * k.val))
          = ∑ k : Fin L, Dz k.val * 2 ^ (B * k.val) from by
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            simp only [hDz, dif_pos k.isLt]] at hs
        rwa [Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t))] at hs
      have hSD_top : SD (G - 1) = 0 := by
        rw [hSD_app, show G - 1 + 1 = G from by omega]
        rw [show (∑ j ∈ Finset.range G, QD j * 2 ^ (B * posOf j))
            = ∑ t ∈ Finset.range (posOf G), Dz t * 2 ^ (B * t) from by
          rw [← group_flatten_schedZ B gf posOf Dz hpos0 hposS G]]
        rw [← sum_extend_zeroZ B L (posOf G) Dz hCov
          (fun t ht => by simp only [hDz, dif_neg (by omega : ¬ t < L)])]
        exact hPVZ0
      -- exact divisibility of the interior prefixes
      have hdvd_diff : ∀ k j, k ≤ j → (Dkz k) ∣ (SD j - SD k) := by
        intro k j hkj
        induction j with
        | zero =>
          have : k = 0 := by omega
          subst this
          simp
        | succ n ih =>
          rcases Nat.lt_or_ge k (n + 1) with hlt | hge
          · have hstep : SD (n + 1) = SD n + QD (n + 1) * 2 ^ (B * posOf (n + 1)) := by
              rw [hSD_app, hSD_app, Finset.sum_range_succ]
            have h1 := ih (by omega)
            have h2 : (Dkz k) ∣ QD (n + 1) * 2 ^ (B * posOf (n + 1)) := by
              rw [hDkz_app]
              exact Dvd.dvd.mul_left
                (pow_dvd_pow 2 (Nat.mul_le_mul_left B (hposMono (k + 1) (n + 1) (by omega)))) _
            have : SD (n + 1) - SD k
                = (SD n - SD k) + QD (n + 1) * 2 ^ (B * posOf (n + 1)) := by
              rw [hstep]
              ring
            rw [this]
            exact dvd_add h1 h2
          · have : k = n + 1 := by omega
            subst this
            simp
      have hdvd : ∀ k, k ≤ G - 1 → (Dkz k) ∣ SD k := by
        intro k hk
        have h1 := hdvd_diff k (G - 1) hk
        rw [hSD_top] at h1
        have : (Dkz k) ∣ (-(SD k)) := by simpa using h1
        simpa using this.neg_right
      -- exact quotients
      set q : ℕ → ℤ := fun k => SD k / Dkz k with hq
      have hq_mul : ∀ k, k ≤ G - 1 → q k * Dkz k = SD k := by
        intro k hk
        simp only [hq]
        exact Int.ediv_mul_cancel (hdvd k hk)
      -- prefix bounds via the ℕ prefix lemma on the flank parts
      have hOFFrec : ∀ k, k < G - 1 →
          (if k = 0 then 0 else V.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i))
            ≤ (V.OFFf k + 1) * 2 ^ (B * gf k) :=
        fun k hk => (hper k hk).2.1.1
      have hOFFrecR : ∀ k, k < G - 1 →
          (if k = 0 then 0 else VR.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i))
            ≤ (VR.OFFf k + 1) * 2 ^ (B * gf k) :=
        fun k hk => (hper k hk).2.1.2
      have hSD_ub : ∀ k, k < G - 1 → SD k < (V.OFFf k + 1 : ℤ) * Dkz k := by
        intro k hk
        have hfP_lt : ∀ t, (Dz t).toNat < V.Nf t := by
          intro t
          have h1 := hDz_hi t
          have h2 := (hNf1 t).1
          omega
        have hgrp := GroupedEqXV.prefix_div_le_sched B gf posOf V.OFFf V.Nf (G - 1)
          he hOFFrec (fun t => (Dz t).toNat) hfP_lt k hk
        have hle : SD k ≤ ((∑ j ∈ Finset.range (k + 1),
            (∑ i ∈ Finset.range (gf j), (Dz (posOf j + i)).toNat * 2 ^ (B * i))
              * 2 ^ (B * posOf j) : ℕ) : ℤ) := by
          rw [hSD_app]
          push_cast
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hQD_app]
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (Int.self_le_toNat _) (by positivity)
        calc SD k ≤ _ := hle
          _ < ((V.OFFf k + 1) * 2 ^ (B * posOf (k + 1)) : ℕ) := by exact_mod_cast hgrp
          _ = (V.OFFf k + 1 : ℤ) * Dkz k := by
              rw [hDkz_app]
              push_cast
              ring
      have hSD_lb : ∀ k, k < G - 1 → -((VR.OFFf k + 1 : ℤ) * Dkz k) < SD k := by
        intro k hk
        have hfN_lt : ∀ t, (-(Dz t)).toNat < VR.Nf t := by
          intro t
          have h1 := hDz_lo t
          have h2 := (hNf1 t).2
          omega
        have hgrp := GroupedEqXV.prefix_div_le_sched B gf posOf VR.OFFf VR.Nf (G - 1)
          he hOFFrecR (fun t => (-(Dz t)).toNat) hfN_lt k hk
        have hle : -(SD k) ≤ ((∑ j ∈ Finset.range (k + 1),
            (∑ i ∈ Finset.range (gf j), (-(Dz (posOf j + i))).toNat * 2 ^ (B * i))
              * 2 ^ (B * posOf j) : ℕ) : ℤ) := by
          rw [hSD_app, ← Finset.sum_neg_distrib]
          push_cast
          apply Finset.sum_le_sum
          intro j _
          rw [show -(QD j * 2 ^ (B * posOf j)) = (-(QD j)) * 2 ^ (B * posOf j) from by ring]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hQD_app, ← Finset.sum_neg_distrib]
          apply Finset.sum_le_sum
          intro i _
          rw [show -(Dz (posOf j + i) * 2 ^ (B * i)) = (-(Dz (posOf j + i))) * 2 ^ (B * i) from by
            ring]
          exact mul_le_mul_of_nonneg_right (Int.self_le_toNat _) (by positivity)
        have h2 : -(SD k) < (VR.OFFf k + 1 : ℤ) * Dkz k := by
          calc -(SD k) ≤ _ := hle
            _ < ((VR.OFFf k + 1) * 2 ^ (B * posOf (k + 1)) : ℕ) := by exact_mod_cast hgrp
            _ = (VR.OFFf k + 1 : ℤ) * Dkz k := by
                rw [hDkz_app]
                push_cast
                ring
        omega
      have hq_ub : ∀ k, k < G - 1 → q k ≤ (V.OFFf k : ℤ) := by
        intro k hk
        have h1 := hSD_ub k hk
        rw [← hq_mul k (by omega)] at h1
        have h2 := hDkz_pos k
        nlinarith
      have hq_lb : ∀ k, k < G - 1 → -(VR.OFFf k : ℤ) ≤ q k := by
        intro k hk
        have h1 := hSD_lb k hk
        rw [← hq_mul k (by omega)] at h1
        have h2 := hDkz_pos k
        nlinarith
      -- honest carries
      set Cn : ℕ → ℕ := fun k => ((VR.OFFf k : ℤ) + q k).toNat with hCn
      have hCnZ : ∀ k, k < G - 1 → (Cn k : ℤ) = (VR.OFFf k : ℤ) + q k := by
        intro k hk
        simp only [hCn]
        have := hq_lb k hk
        omega
      have hrange : ∀ k, k < G - 1 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        have h1 := hq_ub k hk
        have h2 := hq_lb k hk
        have h3 := (hper k hk).1
        have h4 : (Cn k : ℤ) < ((2 ^ V.Wf k : ℕ) : ℤ) := by
          rw [hCnZ k hk]
          have : ((VR.OFFf k + V.OFFf k : ℕ) : ℤ) < ((2 ^ V.Wf k : ℕ) : ℤ) := by
            exact_mod_cast h3
          push_cast at this ⊢
          omega
        exact_mod_cast h4
      -- honest per-boundary identity over ℤ
      have hqstep : ∀ k, k < G - 1 →
          q k * 2 ^ (B * gf k) = (if k = 0 then (0 : ℤ) else q (k - 1)) + QD k := by
        intro k hk
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [if_pos rfl, zero_add]
          have h1 := hq_mul 0 (by omega)
          have hSD0 : SD 0 = QD 0 := by
            rw [hSD_app]
            simp [hpos0]
          have hDk0 : Dkz 0 = (2 : ℤ) ^ (B * gf 0) := by
            rw [hDkz_app, hposS 0, hpos0]
            norm_num
          rw [hSD0, hDk0] at h1
          exact h1
        · rw [if_neg (by omega : ¬ k = 0)]
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [show j + 1 - 1 = j from rfl]
          have h1 := hq_mul (j + 1) (by omega)
          have h0 := hq_mul j (by omega)
          have hstep : SD (j + 1) = SD j + QD (j + 1) * 2 ^ (B * posOf (j + 1)) := by
            rw [hSD_app, hSD_app, Finset.sum_range_succ]
          rw [hstep, ← h0] at h1
          have hDsplit : Dkz (j + 1) = 2 ^ (B * posOf (j + 1)) * 2 ^ (B * gf (j + 1)) := by
            rw [hDkz_app, he (j + 1), pow_add]
          have hDj : Dkz j = (2 : ℤ) ^ (B * posOf (j + 1)) := hDkz_app j
          rw [hDsplit, hDj] at h1
          have hpow_pos : (0 : ℤ) < 2 ^ (B * posOf (j + 1)) := by positivity
          have hcancel : q (j + 1) * 2 ^ (B * gf (j + 1)) * 2 ^ (B * posOf (j + 1))
              = (q j + QD (j + 1)) * 2 ^ (B * posOf (j + 1)) := by
            rw [add_mul]
            linarith [h1]
          have := mul_right_cancel₀ (ne_of_gt hpow_pos) hcancel
          linarith
      have hidxZ : ∀ k, k < G - 1 →
          QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
            + (VR.OFFf k : ℤ) * 2 ^ (B * gf k)
          = (Cn k : ℤ) * 2 ^ (B * gf k)
            + (if k = 0 then (0 : ℤ) else (VR.OFFf (k - 1) : ℤ)) := by
        intro k hk
        have hqs := hqstep k hk
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          simp only [↓reduceIte] at hqs ⊢
          rw [hCnZ 0 hk, add_mul]
          linarith
        · rw [if_neg (by omega : ¬ k = 0)] at hqs ⊢
          rw [if_neg (by omega : ¬ k = 0)]
          rw [hCnZ k hk, hCnZ (k - 1) (by omega), add_mul]
          linarith
      -- eval bridges
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hDz_cast : ∀ (j : ℕ) (hj : j < L),
          ((Dz j : ℤ) : F p)
            = Expression.eval env.toEnvironment (input_var.lhs[j]'hj)
              - Expression.eval env.toEnvironment (input_var.rhs[j]'hj) := by
        intro j hj
        simp only [hDz, dif_pos hj]
        rw [zsval_cast, ha_e j hj, hb_e j hj]
      have hGD_e : ∀ j : ℕ,
          Expression.eval env.toEnvironment (groupExprW B L gf posOf input_var.lhs j)
            - Expression.eval env.toEnvironment (groupExprW B L gf posOf input_var.rhs j)
          = ((QD j : ℤ) : F p) := by
        intro j
        rw [groupExprW_eval, groupExprW_eval, hQD_app, ← Finset.sum_sub_distrib, Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [pow_mul]
        by_cases h : posOf j + i < L
        · rw [dif_pos h, dif_pos h, ← sub_mul]
          congr 1
          rw [hDz_cast (posOf j + i) h]
        · rw [dif_neg h, dif_neg h]
          simp only [hDz, dif_neg h]
          simp
      have hbase_ne : ∀ k, k < G - 1 → ((2 : F p) ^ (B * gf k) ≠ 0) := by
        intro k hk
        have hnat : (((2 ^ (B * gf k) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * gf k) : ℕ) : F p).val) = 2 ^ (B * gf k) :=
            ZMod.val_natCast_of_lt (hpBg k hk)
          rw [hzero, ZMod.val_zero] at hval
          have : 0 < 2 ^ (B * gf k) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env.toEnvironment
            (carryExpr B gf posOf VR.OFFf input_var.lhs input_var.rhs k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        induction k with
        | zero =>
            have hnatk := hidxZ 0 (by omega)
            simp only [↓reduceIte] at hnatk
            have hcast := congrArg (Int.cast : ℤ → F p) hnatk
            push_cast at hcast
            rw [← hGD_e 0] at hcast
            simp [carryExpr, Expression.eval]
            field_simp [hbase_ne 0 (by omega)]
            linear_combination hcast
        | succ j ih =>
            have hprev := ih (by omega)
            have hnatk := hidxZ (j + 1) (by omega)
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.add_sub_cancel] at hnatk
            have hcast := congrArg (Int.cast : ℤ → F p) hnatk
            push_cast at hcast
            rw [← hGD_e (j + 1)] at hcast
            simp [carryExpr, Expression.eval, hprev]
            field_simp [hbase_ne (j + 1) (by omega)]
            linear_combination hcast
      refine ⟨?_, ?_⟩
      · -- the loop's range checks
        refine GroupedEqXV.carryLoop_completeness B gf posOf VR.OFFf V.Wf hWok env
          input_var.lhs input_var.rhs (G - 2) 0 i₀ fun i hi => ?_
        rw [Nat.zero_add, hcarry_eval i (by omega),
          ZMod.val_natCast_of_lt (lt_trans (hrange i (by omega)) (hWok i).2)]
        exact hrange i (by omega)
      · -- final mod-p row: the honest ℤ value is zero
        have hPV_cast : ((∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t) : ℤ) : F p)
            = (∑ i : Fin L, Expression.eval env.toEnvironment
                  (input_var.lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
              - (∑ i : Fin L, Expression.eval env.toEnvironment
                  (input_var.rhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val) := by
          rw [← Finset.sum_sub_distrib,
            ← Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t)), Int.cast_sum]
          apply Finset.sum_congr rfl
          intro i _
          push_cast
          rw [hDz_cast i.val i.isLt, ← pow_mul]
          ring
        have hd := GroupedEqXV.polyEvalExpr_diff_eval B env.toEnvironment
          input_var.lhs input_var.rhs
        rw [← hPV_cast, hPVZ0, Int.cast_zero] at hd
        try simp only [circuit_norm]
        exact hd

/-- Projection: the assertion's `Assumptions` field. -/
lemma circuit_assumptions_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit (L := L) B gf posOf G V VR hgv hB1).Assumptions = Assumptions V.Nf VR.Nf := rfl

/-- Projection: the assertion's `Spec` field. -/
lemma circuit_spec_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit (L := L) B gf posOf G V VR hgv hB1).Spec = Spec B V.Nf := rfl

/-- Projection: the assertion has no requirement channels. -/
lemma circuit_channels_req_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuit (L := L) B gf posOf G V VR hgv hB1).channelsWithRequirements = [] := rfl

/-! ## Definitional-top variant (`mainD`/`circuitD`)

`circuitD` is `circuit` with the final mod-`p` row eliminated by construction:
the rhs top coefficient is replaced by the affine reconstruction
`GroupedEqXV.topExprD`, so the deleted row evaluates to `0` in every
environment (`GroupedEqXV.polyEvalExpr_rhsD_eval`). -/

/-- The `main` circuit of the definitional-top variant: only the graduated
carry range checks — no final row. -/
def mainD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR) [Fact (p > 2)]
    (input : Var (InputsX L) (F p)) : Circuit (F p) Unit :=
  carryLoop B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1 input.lhs
    (GroupedEqXV.rhsD B input.lhs input.rhs) (G - 2) 0

instance elaboratedD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (InputsX L) unit (mainD B gf posOf G V VR hgv) where
  localLength _ := widthAllocFrom V.Wf (G - 2) 0
  localLength_eq := by
    intro input offset
    unfold mainD
    exact GroupedEqXV.carryLoop_localLength B gf posOf VR.OFFf V.Wf hgv.1.2.2.2.1
      input.lhs (GroupedEqXV.rhsD B input.lhs input.rhs) (G - 2) 0 offset
  subcircuitsConsistent := by
    intro input offset
    unfold mainD
    exact GroupedEqXV.carryLoop_subcircuitsConsistent B gf posOf VR.OFFf V.Wf
      hgv.1.2.2.2.1 _ _ _ _ offset
  channelsLawful := by
    intro input offset
    unfold mainD
    exact GroupedEqXV.carryLoop_channelsLawful B gf posOf VR.OFFf V.Wf
      hgv.1.2.2.2.1 _ _ _ _ offset

/-- Per-position preconditions of the definitional-top variant: each difference
against the *reconstructed* rhs is the field image of an integer in the
two-sided window `(−NfN k, NfP k)`. -/
def AssumptionsD (B : ℕ) (NfP NfN : ℕ → ℕ) (input : InputsX L (F p)) : Prop :=
  ∀ k : Fin L, ∃ z : ℤ,
    ((z : ℤ) : F p) = input.lhs[k.val]
        - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k.val] ∧
    -(NfN k.val : ℤ) < z ∧ z < (NfP k.val : ℤ)

/-- Postcondition: the ℤ-valued difference polynomial against the reconstructed
rhs (coefficients read through the windowed lift `zsval`) vanishes. -/
def SpecD (B : ℕ) (NfP : ℕ → ℕ) (input : InputsX L (F p)) : Prop :=
  (∑ k : Fin L,
    zsval (NfP k.val) (input.lhs[k.val]
      - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k.val]) * 2 ^ (B * k.val)) = 0

set_option maxHeartbeats 4000000 in
/-- The definitional-top `GroupedEqD` formal assertion: identical windowed ℤ
reading, but the final mod-`p` row is eliminated by construction — the rhs top
coefficient is the affine reconstruction `topExprD`, so the row is a tautology
and only the `Σ_k (Wf k − 1)` graduated carry witnesses remain. -/
def circuitD (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR) (hB1 : 1 ≤ B)
    [Fact (p > 2)] : FormalAssertion (F p) (InputsX L) where
    main := mainD B gf posOf G V VR hgv
    Assumptions := AssumptionsD B V.Nf VR.Nf
    Spec := SpecD B V.Nf
    soundness := by
      obtain ⟨⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, htrunc⟩, hNfp⟩ := hgv
      circuit_proof_start
      unfold mainD at h_holds
      have h_loop := h_holds
      have h_lin := GroupedEqXV.polyEvalExpr_rhsD_eval (L := L) B env
        input_var.lhs input_var.rhs
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have h_range := GroupedEqXV.carryLoop_soundness B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) (G - 2) 0 i₀ h_loop
      -- window facts, re-indexed over plain ℕ positions
      have hAs : ∀ (k : ℕ) (h : k < L), ∃ z : ℤ,
          ((z : ℤ) : F p) = input.lhs[k]'h - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k]'h ∧
          -(VR.Nf k : ℤ) < z ∧ z < (V.Nf k : ℤ) :=
        fun k h => h_assumptions ⟨k, h⟩
      -- signed difference digits (vanish beyond L)
      set Dz : ℕ → ℤ := fun k => if h : k < L
        then zsval (V.Nf k) (input.lhs[k]'h - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k]'h) else 0 with hDz
      have hDz_hi : ∀ k, Dz k < (V.Nf k : ℤ) := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzhi
        · have := (hNf1 k).1
          exact_mod_cast this
      have hDz_lo : ∀ k, -(VR.Nf k : ℤ) < Dz k := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzlo
        · have := (hNf1 k).2
          have h0 : (0 : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast this
          omega
      -- group difference digits
      set QD : ℕ → ℤ := fun j => ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i)
        with hQD
      have hQD_app : ∀ j, QD j = ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- effective offsets (0 at the top) and carries (0 at the top)
      set OFFe : ℕ → ℕ := fun k => if k = G - 1 then 0 else VR.OFFf k with hOFFe
      set Cn : ℕ → ℕ := fun k => if k = G - 1 then 0
        else (Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) k)).val
        with hCn
      have hCn_lt : ∀ k, k < G - 2 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        simpa using h_range k hk
      -- group digit bounds
      have hSfP : ∀ k, QD k
          ≤ ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ) := by
        intro k
        rw [hQD_app]
        push_cast
        apply Finset.sum_le_sum
        intro i _
        have h1 := hDz_hi (posOf k + i)
        have h2 := (hNf1 (posOf k + i)).1
        have hle : Dz (posOf k + i) ≤ ((V.Nf (posOf k + i) - 1 : ℕ) : ℤ) := by omega
        exact mul_le_mul_of_nonneg_right hle (by positivity)
      have hSfN : ∀ k, -((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
          ≤ QD k := by
        intro k
        rw [hQD_app]
        push_cast
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_le_sum
        intro i _
        have h1 := hDz_lo (posOf k + i)
        have h2 := (hNf1 (posOf k + i)).2
        have hle : -((VR.Nf (posOf k + i) - 1 : ℕ) : ℤ) ≤ Dz (posOf k + i) := by omega
        calc -(((VR.Nf (posOf k + i) - 1 : ℕ) : ℤ) * 2 ^ (B * i))
            = (-((VR.Nf (posOf k + i) - 1 : ℕ) : ℤ)) * 2 ^ (B * i) := by ring
          _ ≤ Dz (posOf k + i) * 2 ^ (B * i) :=
              mul_le_mul_of_nonneg_right hle (by positivity)
      have hpBg : ∀ k, k < G - 1 → 2 ^ (B * gf k) < p := fun k hk =>
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
          (sum5_lt (hper k hk).2.2).2.2.1
      have hbase_ne : ∀ k, k < G - 1 → ((2 : F p) ^ (B * gf k) ≠ 0) := by
        intro k hk
        have hnat : (((2 ^ (B * gf k) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * gf k) : ℕ) : F p).val) = 2 ^ (B * gf k) :=
            ZMod.val_natCast_of_lt (hpBg k hk)
          rw [hzero, ZMod.val_zero] at hval
          have : 0 < 2 ^ (B * gf k) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      -- eval bridges
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env ((GroupedEqXV.rhsD B input_var.lhs input_var.rhs)[j]'hj) = (GroupedEqXV.rhsValD B input.lhs input.rhs)[j]'hj := by
        exact GroupedEqXV.rhsD_eval_bridge B env input_var.lhs input_var.rhs input.lhs input.rhs
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
      have hDz_cast : ∀ (j : ℕ) (hj : j < L),
          ((Dz j : ℤ) : F p)
            = Expression.eval env (input_var.lhs[j]'hj)
              - Expression.eval env ((GroupedEqXV.rhsD B input_var.lhs input_var.rhs)[j]'hj) := by
        intro j hj
        simp only [hDz, dif_pos hj]
        rw [zsval_cast, ha_e j hj, hb_e j hj]
      have hGD_e : ∀ j : ℕ,
          Expression.eval env (groupExprW B L gf posOf input_var.lhs j)
            - Expression.eval env (groupExprW B L gf posOf (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) j)
          = ((QD j : ℤ) : F p) := by
        intro j
        rw [groupExprW_eval, groupExprW_eval, hQD_app, ← Finset.sum_sub_distrib, Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [pow_mul]
        by_cases h : posOf j + i < L
        · rw [dif_pos h, dif_pos h, ← sub_mul]
          congr 1
          rw [hDz_cast (posOf j + i) h]
        · rw [dif_neg h, dif_neg h]
          simp only [hDz, dif_neg h]
          simp
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env (carryExpr B gf posOf VR.OFFf input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        simp only [hCn, if_neg (by omega : ¬ k = G - 1)]
        rw [ZMod.natCast_zmod_val]
      -- per-group ℤ equation (interior boundaries only; the top is the mod-p rider)
      have h_idx : ∀ k, k < G - 2 →
          QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
            + (OFFe k : ℤ) * 2 ^ (B * gf k)
          = (Cn k : ℤ) * 2 ^ (B * gf k) + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) := by
        intro k hk
        have hktop : ¬ k = G - 1 := by omega
        have hOFFk : OFFe k = VR.OFFf k := by simp only [hOFFe, if_neg hktop]
        -- the field identity from the carry expression
        have hfield : ((QD k : ℤ) : F p)
            + (if k = 0 then (0 : F p) else ((Cn (k - 1) : ℕ) : F p))
            + ((OFFe k : ℕ) : F p) * (2 ^ (B * gf k) : F p)
            = ((Cn k : ℕ) : F p) * (2 ^ (B * gf k) : F p)
              + (if k = 0 then (0 : F p) else ((OFFe (k - 1) : ℕ) : F p)) := by
          rw [hOFFk]
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            have hcarry := hcarry_eval 0 (by omega)
            simp only [↓reduceIte]
            rw [← hGD_e 0, ← hcarry]
            simp [carryExpr, Expression.eval]
            field_simp [hbase_ne 0 (by omega)]
            ring_nf
          · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
            have hcarry := hcarry_eval (j + 1) (by omega)
            have hprev := hcarry_eval j (by omega)
            have hOFFj : OFFe j = VR.OFFf j := by
              simp only [hOFFe, if_neg (by omega : ¬ j = G - 1)]
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.succ_sub_one,
              Nat.add_sub_cancel, hOFFj]
            rw [← hGD_e (j + 1), ← hcarry]
            simp [carryExpr, Expression.eval, hprev]
            field_simp [hbase_ne (j + 1) (by omega)]
            ring_nf
        -- ℤ-lift via cast injectivity on the window
        have hnw := (hper k (by omega)).2.2
        have hcin_ub : (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ)) ≤ 2 ^ V.Wf (k - 1) := by
          split
          · positivity
          · have := hCn_lt (k - 1) (by omega)
            have : Cn (k - 1) ≤ 2 ^ V.Wf (k - 1) := by omega
            exact_mod_cast this
        have hcin_lb : (0 : ℤ) ≤ (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ)) := by
          split
          · omega
          · positivity
        have hoffp_ub : (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) ≤ 2 ^ V.Wf (k - 1) := by
          split
          · positivity
          · have hoe : OFFe (k - 1) = VR.OFFf (k - 1) := by
              simp only [hOFFe, if_neg (by omega : ¬ k - 1 = G - 1)]
            rw [hoe]
            have := (hper (k - 1) (by omega)).1
            have : VR.OFFf (k - 1) ≤ 2 ^ V.Wf (k - 1) := by omega
            exact_mod_cast this
        have hoffp_lb : (0 : ℤ) ≤ (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) := by
          split
          · omega
          · positivity
        have hcast_eq : (((QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)) : ℤ) : F p)
            = ((((Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))) : ℤ) : F p) := by
          push_cast
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            simpa using hfield
          · rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)]
            have h := hfield
            rw [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 0)] at h
            push_cast at h ⊢
            convert h using 2 <;> push_cast <;> ring
        -- magnitude bounds for the injectivity window
        have hQDub := hSfP k
        have hQDlb := hSfN k
        have hCk : (Cn k : ℤ) * 2 ^ (B * gf k)
            ≤ ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by
          push_cast
          have h1 : (Cn k : ℤ) ≤ 2 ^ V.Wf k := by
            have := hCn_lt k hk
            have : Cn k ≤ 2 ^ V.Wf k := by omega
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        have hOFFk_mul : (OFFe k : ℤ) * 2 ^ (B * gf k)
            = ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by
          rw [hOFFk]
          push_cast
          ring
        have hnwZ : ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
            + ((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
            + ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ)
            + ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) + ((2 ^ V.Wf (k - 1) : ℕ) : ℤ)
            < (p : ℤ) := by
          exact_mod_cast hnw
        have hWprev_cast : ((2 ^ V.Wf (k - 1) : ℕ) : ℤ) = (2 : ℤ) ^ V.Wf (k - 1) := by
          push_cast
          ring
        refine intCast_inj_of_lt hcast_eq ?_ ?_
        · -- LHS − RHS < p
          have hRHS_nonneg : (0 : ℤ) ≤ (Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) := by
            have : (0 : ℤ) ≤ (Cn k : ℤ) * 2 ^ (B * gf k) := by positivity
            omega
          have hLHS_ub : QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)
              ≤ ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
                + 2 ^ V.Wf (k - 1) + ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by
            rw [hOFFk_mul]
            omega
          rw [hWprev_cast] at hnwZ
          have hSR0 : (0 : ℤ)
              ≤ ((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ) := by
            positivity
          have hCk0 : (0 : ℤ) ≤ ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by positivity
          omega
        · -- RHS − LHS < p
          have hLHS_lb : -((∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ)
              ≤ QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
                + (OFFe k : ℤ) * 2 ^ (B * gf k) := by
            have h1 : (0 : ℤ) ≤ (OFFe k : ℤ) * 2 ^ (B * gf k) := by positivity
            omega
          have hRHS_ub : (Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))
              ≤ ((2 ^ V.Wf k * 2 ^ (B * gf k) : ℕ) : ℤ) + 2 ^ V.Wf (k - 1) := by
            omega
          rw [hWprev_cast] at hnwZ
          have hSL0 : (0 : ℤ)
              ≤ ((∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i) : ℕ) : ℤ) := by
            positivity
          have hOFF0 : (0 : ℤ) ≤ ((VR.OFFf k * 2 ^ (B * gf k) : ℕ) : ℤ) := by positivity
          omega
      -- the ℤ difference polynomial and its position form
      set PVZ : ℤ := ∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t) with hPVZ
      set n0 := G - 2 with hn0
      have hn0_pos : 1 ≤ n0 := by omega
      have hposn0_lt : posOf n0 < L := lt_of_le_of_lt (hposMono n0 (G - 1) (by omega)) hlast
      rw [show G - 3 = n0 - 1 from by omega] at htrunc
      set Wz : ℤ := 2 ^ (B * posOf n0) with hWz
      set SDlow : ℤ := ∑ k ∈ Finset.range n0, QD k * 2 ^ (B * posOf k) with hSDlow
      set TD : ℤ := ∑ t ∈ Finset.range (L - posOf n0), Dz (posOf n0 + t) * 2 ^ (B * t) with hTD
      have hF1 : PVZ = SDlow + Wz * TD := by
        rw [hPVZ]
        have hsplit : (∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t))
            = (∑ t ∈ Finset.range (posOf n0), Dz t * 2 ^ (B * t))
              + ∑ i ∈ Finset.range (L - posOf n0), Dz (posOf n0 + i) * 2 ^ (B * (posOf n0 + i)) := by
          conv_lhs => rw [show L = posOf n0 + (L - posOf n0) from by omega]
          rw [Finset.sum_range_add]
        rw [hsplit]
        congr 1
        · rw [hSDlow, ← group_flatten_schedZ B gf posOf Dz hpos0 hposS n0]
        · rw [hTD, hWz, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show B * (posOf n0 + i) = B * posOf n0 + B * i from by ring, pow_add]
          ring
      -- telescope the per-boundary identities
      have hsumlow : (∑ k ∈ Finset.range n0,
            (QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)) * 2 ^ (B * posOf k))
          = ∑ k ∈ Finset.range n0,
              ((Cn k : ℤ) * 2 ^ (B * gf k)
                + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))) * 2 ^ (B * posOf k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [h_idx k hk]
      have hLHSlow : (∑ k ∈ Finset.range n0,
            (QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
              + (OFFe k : ℤ) * 2 ^ (B * gf k)) * 2 ^ (B * posOf k))
          = SDlow
            + (∑ k ∈ Finset.range n0,
                (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ)) * 2 ^ (B * posOf k))
            + (∑ k ∈ Finset.range n0, (OFFe k : ℤ) * 2 ^ (B * posOf (k + 1))) := by
        rw [hSDlow, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [he k, pow_add]
        ring
      have hRHSlow : (∑ k ∈ Finset.range n0,
            ((Cn k : ℤ) * 2 ^ (B * gf k)
              + (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ))) * 2 ^ (B * posOf k))
          = (∑ k ∈ Finset.range n0, (Cn k : ℤ) * 2 ^ (B * posOf (k + 1)))
            + (∑ k ∈ Finset.range n0,
                (if k = 0 then (0 : ℤ) else (OFFe (k - 1) : ℤ)) * 2 ^ (B * posOf k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [he k, pow_add]
        ring
      have htelC := carry_telescope_eZ (fun k => B * posOf k) (fun k => (Cn k : ℤ)) n0
      simp only [] at htelC
      rw [if_neg (by omega : ¬ (n0 = 0)), ← hWz] at htelC
      have htelO := carry_telescope_eZ (fun k => B * posOf k) (fun k => (OFFe k : ℤ)) n0
      simp only [] at htelO
      rw [if_neg (by omega : ¬ (n0 = 0)), ← hWz] at htelO
      have hdagger : SDlow + (OFFe (n0 - 1) : ℤ) * Wz = (Cn (n0 - 1) : ℤ) * Wz := by
        have key := hsumlow
        rw [hLHSlow, hRHSlow] at key
        linarith
      -- the final mod-p row pins the ℤ polynomial mod p
      have hPV_cast : ((PVZ : ℤ) : F p)
          = (∑ i : Fin L, Expression.eval env (input_var.lhs[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val)
            - (∑ i : Fin L, Expression.eval env ((GroupedEqXV.rhsD B input_var.lhs input_var.rhs)[i.val]'i.isLt) * ((2 : F p) ^ B) ^ i.val) := by
        rw [← Finset.sum_sub_distrib, hPVZ,
          ← Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t)), Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [hDz_cast i.val i.isLt, ← pow_mul]
        ring
      have hMODP : ((PVZ : ℤ) : F p) = 0 := by
        have hd := GroupedEqXV.polyEvalExpr_diff_eval B env input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs)
        rw [h_lin] at hd
        rw [hPV_cast, ← hd]
      have hdvd : (p : ℤ) ∣ PVZ := by
        rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      -- factor out the boundary weight
      have hfact : PVZ = Wz * ((Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD) := by
        rw [hF1]
        have := hdagger
        ring_nf
        ring_nf at this
        linarith
      have hp2 : 2 < p := Fact.out
      have hdvdX : (p : ℤ) ∣ ((Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD) := by
        rw [hfact] at hdvd
        have h1 : p ∣ (Wz * ((Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD)).natAbs := by
          have h := Int.natAbs_dvd_natAbs.mpr hdvd
          rwa [Int.natAbs_natCast] at h
        rw [Int.natAbs_mul] at h1
        rcases ((Fact.out : p.Prime).dvd_mul).mp h1 with hl | hr
        · exfalso
          have hWabs : Wz.natAbs = 2 ^ (B * posOf n0) := by
            rw [hWz]
            simp [Int.natAbs_pow]
          rw [hWabs] at hl
          have h2 : p ∣ 2 := (Fact.out : p.Prime).dvd_of_dvd_pow hl
          have := Nat.le_of_dvd (by norm_num) h2
          omega
        · exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hr)
      -- tail bounds
      have hTD_ub : TD
          < ((∑ t ∈ Finset.range (L - posOf n0), V.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ) := by
        rw [hTD]
        push_cast
        apply Finset.sum_lt_sum_of_nonempty
        · rw [Finset.nonempty_range_iff]
          omega
        · intro t _
          exact mul_lt_mul_of_pos_right (hDz_hi (posOf n0 + t)) (by positivity)
      have hTD_lb : -((∑ t ∈ Finset.range (L - posOf n0), VR.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ)
          < TD := by
        rw [hTD]
        push_cast
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_lt_sum_of_nonempty
        · rw [Finset.nonempty_range_iff]
          omega
        · intro t _
          have h1 := hDz_lo (posOf n0 + t)
          calc -(((VR.Nf (posOf n0 + t) : ℕ) : ℤ) * 2 ^ (B * t))
              = (-((VR.Nf (posOf n0 + t) : ℕ) : ℤ)) * 2 ^ (B * t) := by ring
            _ < Dz (posOf n0 + t) * 2 ^ (B * t) :=
                mul_lt_mul_of_pos_right h1 (by positivity)
      have hOFF_lt : OFFe (n0 - 1) < 2 ^ V.Wf (n0 - 1) := by
        have hOFFn0 : OFFe (n0 - 1) = VR.OFFf (n0 - 1) := by
          simp only [hOFFe, if_neg (by omega : ¬ n0 - 1 = G - 1)]
        rw [hOFFn0]
        have := (hper (n0 - 1) (by omega)).1
        omega
      have hCn_lt_b : Cn (n0 - 1) < 2 ^ V.Wf (n0 - 1) := hCn_lt (n0 - 1) (by omega)
      have htruncZ : ((2 ^ V.Wf (n0 - 1) : ℕ) : ℤ)
          + ((∑ t ∈ Finset.range (L - posOf n0), V.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ)
          + ((∑ t ∈ Finset.range (L - posOf n0), VR.Nf (posOf n0 + t) * 2 ^ (B * t) : ℕ) : ℤ)
          < (p : ℤ) := by
        exact_mod_cast htrunc
      have hX0 : (Cn (n0 - 1) : ℤ) - (OFFe (n0 - 1) : ℤ) + TD = 0 := by
        apply int_eq_zero_of_dvd_of_lt hdvdX
        · have h1 : (Cn (n0 - 1) : ℤ) < ((2 ^ V.Wf (n0 - 1) : ℕ) : ℤ) := by
            exact_mod_cast hCn_lt_b
          have h2 : (0 : ℤ) ≤ (OFFe (n0 - 1) : ℤ) := by positivity
          omega
        · have h1 : (OFFe (n0 - 1) : ℤ) < ((2 ^ V.Wf (n0 - 1) : ℕ) : ℤ) := by
            exact_mod_cast hOFF_lt
          have h2 : (0 : ℤ) ≤ (Cn (n0 - 1) : ℤ) := by positivity
          omega
      have hPVZ0 : PVZ = 0 := by
        rw [hfact, hX0, mul_zero]
      -- conclude the Spec
      refine ⟨?_, GroupedEqXV.carryLoop_requirements B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) _ _ _⟩
      show (∑ k : Fin L,
          zsval (V.Nf k.val) (input.lhs[k.val] - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k.val]) * 2 ^ (B * k.val)) = 0
      rw [show (∑ k : Fin L,
          zsval (V.Nf k.val) (input.lhs[k.val] - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k.val]) * 2 ^ (B * k.val))
        = ∑ k : Fin L, Dz k.val * 2 ^ (B * k.val) from by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
          simp only [hDz, dif_pos k.isLt]]
      rw [Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t)), ← hPVZ]
      exact hPVZ0
    completeness := by
      obtain ⟨⟨hpos0, hposS, hgf1, hWok, hNf1, hper, hG3, hlast, hCov, _⟩, hNfp⟩ := hgv
      circuit_proof_start
      have hM : 0 < L := Nat.pos_of_neZero L
      have hG1 : 0 < G := by omega
      have hposMono : ∀ a b, a ≤ b → posOf a ≤ posOf b :=
        fun a b hab => monotone_nat_of_le_succ (fun k => by rw [hposS k]; omega) hab
      have he : ∀ k, B * posOf (k + 1) = B * posOf k + B * gf k :=
        fun k => by rw [hposS k, Nat.mul_add]
      have hpBg : ∀ k, k < G - 1 → 2 ^ (B * gf k) < p := fun k hk =>
        lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
          (sum5_lt (hper k hk).2.2).2.2.1
      have hAs : ∀ (k : ℕ) (h : k < L), ∃ z : ℤ,
          ((z : ℤ) : F p) = input.lhs[k]'h - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k]'h ∧
          -(VR.Nf k : ℤ) < z ∧ z < (V.Nf k : ℤ) :=
        fun k h => h_assumptions ⟨k, h⟩
      -- signed difference digits
      set Dz : ℕ → ℤ := fun k => if h : k < L
        then zsval (V.Nf k) (input.lhs[k]'h - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k]'h) else 0 with hDz
      have hDz_hi : ∀ k, Dz k < (V.Nf k : ℤ) := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzhi
        · have := (hNf1 k).1
          exact_mod_cast this
      have hDz_lo : ∀ k, -(VR.Nf k : ℤ) < Dz k := by
        intro k
        simp only [hDz]
        split
        · rename_i h
          obtain ⟨z, hzc, hzlo, hzhi⟩ := hAs k h
          rw [zsval_eq_of_window hzc hzlo hzhi (hNfp k h)]
          exact hzlo
        · have := (hNf1 k).2
          have h0 : (0 : ℤ) < (VR.Nf k : ℤ) := by exact_mod_cast this
          omega
      set QD : ℕ → ℤ := fun j => ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i)
        with hQD
      have hQD_app : ∀ j, QD j = ∑ i ∈ Finset.range (gf j), Dz (posOf j + i) * 2 ^ (B * i) :=
        fun _ => rfl
      -- ℤ prefix sums and boundary weights
      set SD : ℕ → ℤ := fun k => ∑ j ∈ Finset.range (k + 1), QD j * 2 ^ (B * posOf j) with hSD
      set Dkz : ℕ → ℤ := fun k => 2 ^ (B * posOf (k + 1)) with hDkz
      have hSD_app : ∀ k, SD k = ∑ j ∈ Finset.range (k + 1), QD j * 2 ^ (B * posOf j) :=
        fun _ => rfl
      have hDkz_app : ∀ k, Dkz k = 2 ^ (B * posOf (k + 1)) := fun _ => rfl
      have hDkz_pos : ∀ k, (0 : ℤ) < Dkz k := by
        intro k
        rw [hDkz_app]
        positivity
      -- the spec pins the top prefix to zero
      have hPVZ0 : (∑ t ∈ Finset.range L, Dz t * 2 ^ (B * t)) = 0 := by
        have hs : (∑ k : Fin L,
            zsval (V.Nf k.val) (input.lhs[k.val] - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k.val]) * 2 ^ (B * k.val)) = 0 :=
          h_spec
        rw [show (∑ k : Fin L,
            zsval (V.Nf k.val) (input.lhs[k.val] - (GroupedEqXV.rhsValD B input.lhs input.rhs)[k.val]) * 2 ^ (B * k.val))
          = ∑ k : Fin L, Dz k.val * 2 ^ (B * k.val) from by
            apply Finset.sum_congr rfl
            intro k _
            congr 1
            simp only [hDz, dif_pos k.isLt]] at hs
        rwa [Fin.sum_univ_eq_sum_range (fun t => Dz t * 2 ^ (B * t))] at hs
      have hSD_top : SD (G - 1) = 0 := by
        rw [hSD_app, show G - 1 + 1 = G from by omega]
        rw [show (∑ j ∈ Finset.range G, QD j * 2 ^ (B * posOf j))
            = ∑ t ∈ Finset.range (posOf G), Dz t * 2 ^ (B * t) from by
          rw [← group_flatten_schedZ B gf posOf Dz hpos0 hposS G]]
        rw [← sum_extend_zeroZ B L (posOf G) Dz hCov
          (fun t ht => by simp only [hDz, dif_neg (by omega : ¬ t < L)])]
        exact hPVZ0
      -- exact divisibility of the interior prefixes
      have hdvd_diff : ∀ k j, k ≤ j → (Dkz k) ∣ (SD j - SD k) := by
        intro k j hkj
        induction j with
        | zero =>
          have : k = 0 := by omega
          subst this
          simp
        | succ n ih =>
          rcases Nat.lt_or_ge k (n + 1) with hlt | hge
          · have hstep : SD (n + 1) = SD n + QD (n + 1) * 2 ^ (B * posOf (n + 1)) := by
              rw [hSD_app, hSD_app, Finset.sum_range_succ]
            have h1 := ih (by omega)
            have h2 : (Dkz k) ∣ QD (n + 1) * 2 ^ (B * posOf (n + 1)) := by
              rw [hDkz_app]
              exact Dvd.dvd.mul_left
                (pow_dvd_pow 2 (Nat.mul_le_mul_left B (hposMono (k + 1) (n + 1) (by omega)))) _
            have : SD (n + 1) - SD k
                = (SD n - SD k) + QD (n + 1) * 2 ^ (B * posOf (n + 1)) := by
              rw [hstep]
              ring
            rw [this]
            exact dvd_add h1 h2
          · have : k = n + 1 := by omega
            subst this
            simp
      have hdvd : ∀ k, k ≤ G - 1 → (Dkz k) ∣ SD k := by
        intro k hk
        have h1 := hdvd_diff k (G - 1) hk
        rw [hSD_top] at h1
        have : (Dkz k) ∣ (-(SD k)) := by simpa using h1
        simpa using this.neg_right
      -- exact quotients
      set q : ℕ → ℤ := fun k => SD k / Dkz k with hq
      have hq_mul : ∀ k, k ≤ G - 1 → q k * Dkz k = SD k := by
        intro k hk
        simp only [hq]
        exact Int.ediv_mul_cancel (hdvd k hk)
      -- prefix bounds via the ℕ prefix lemma on the flank parts
      have hOFFrec : ∀ k, k < G - 1 →
          (if k = 0 then 0 else V.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range (gf k), (V.Nf (posOf k + i) - 1) * 2 ^ (B * i))
            ≤ (V.OFFf k + 1) * 2 ^ (B * gf k) :=
        fun k hk => (hper k hk).2.1.1
      have hOFFrecR : ∀ k, k < G - 1 →
          (if k = 0 then 0 else VR.OFFf (k - 1)) + 1
              + (∑ i ∈ Finset.range (gf k), (VR.Nf (posOf k + i) - 1) * 2 ^ (B * i))
            ≤ (VR.OFFf k + 1) * 2 ^ (B * gf k) :=
        fun k hk => (hper k hk).2.1.2
      have hSD_ub : ∀ k, k < G - 1 → SD k < (V.OFFf k + 1 : ℤ) * Dkz k := by
        intro k hk
        have hfP_lt : ∀ t, (Dz t).toNat < V.Nf t := by
          intro t
          have h1 := hDz_hi t
          have h2 := (hNf1 t).1
          omega
        have hgrp := GroupedEqXV.prefix_div_le_sched B gf posOf V.OFFf V.Nf (G - 1)
          he hOFFrec (fun t => (Dz t).toNat) hfP_lt k hk
        have hle : SD k ≤ ((∑ j ∈ Finset.range (k + 1),
            (∑ i ∈ Finset.range (gf j), (Dz (posOf j + i)).toNat * 2 ^ (B * i))
              * 2 ^ (B * posOf j) : ℕ) : ℤ) := by
          rw [hSD_app]
          push_cast
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hQD_app]
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (Int.self_le_toNat _) (by positivity)
        calc SD k ≤ _ := hle
          _ < ((V.OFFf k + 1) * 2 ^ (B * posOf (k + 1)) : ℕ) := by exact_mod_cast hgrp
          _ = (V.OFFf k + 1 : ℤ) * Dkz k := by
              rw [hDkz_app]
              push_cast
              ring
      have hSD_lb : ∀ k, k < G - 1 → -((VR.OFFf k + 1 : ℤ) * Dkz k) < SD k := by
        intro k hk
        have hfN_lt : ∀ t, (-(Dz t)).toNat < VR.Nf t := by
          intro t
          have h1 := hDz_lo t
          have h2 := (hNf1 t).2
          omega
        have hgrp := GroupedEqXV.prefix_div_le_sched B gf posOf VR.OFFf VR.Nf (G - 1)
          he hOFFrecR (fun t => (-(Dz t)).toNat) hfN_lt k hk
        have hle : -(SD k) ≤ ((∑ j ∈ Finset.range (k + 1),
            (∑ i ∈ Finset.range (gf j), (-(Dz (posOf j + i))).toNat * 2 ^ (B * i))
              * 2 ^ (B * posOf j) : ℕ) : ℤ) := by
          rw [hSD_app, ← Finset.sum_neg_distrib]
          push_cast
          apply Finset.sum_le_sum
          intro j _
          rw [show -(QD j * 2 ^ (B * posOf j)) = (-(QD j)) * 2 ^ (B * posOf j) from by ring]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [hQD_app, ← Finset.sum_neg_distrib]
          apply Finset.sum_le_sum
          intro i _
          rw [show -(Dz (posOf j + i) * 2 ^ (B * i)) = (-(Dz (posOf j + i))) * 2 ^ (B * i) from by
            ring]
          exact mul_le_mul_of_nonneg_right (Int.self_le_toNat _) (by positivity)
        have h2 : -(SD k) < (VR.OFFf k + 1 : ℤ) * Dkz k := by
          calc -(SD k) ≤ _ := hle
            _ < ((VR.OFFf k + 1) * 2 ^ (B * posOf (k + 1)) : ℕ) := by exact_mod_cast hgrp
            _ = (VR.OFFf k + 1 : ℤ) * Dkz k := by
                rw [hDkz_app]
                push_cast
                ring
        omega
      have hq_ub : ∀ k, k < G - 1 → q k ≤ (V.OFFf k : ℤ) := by
        intro k hk
        have h1 := hSD_ub k hk
        rw [← hq_mul k (by omega)] at h1
        have h2 := hDkz_pos k
        nlinarith
      have hq_lb : ∀ k, k < G - 1 → -(VR.OFFf k : ℤ) ≤ q k := by
        intro k hk
        have h1 := hSD_lb k hk
        rw [← hq_mul k (by omega)] at h1
        have h2 := hDkz_pos k
        nlinarith
      -- honest carries
      set Cn : ℕ → ℕ := fun k => ((VR.OFFf k : ℤ) + q k).toNat with hCn
      have hCnZ : ∀ k, k < G - 1 → (Cn k : ℤ) = (VR.OFFf k : ℤ) + q k := by
        intro k hk
        simp only [hCn]
        have := hq_lb k hk
        omega
      have hrange : ∀ k, k < G - 1 → Cn k < 2 ^ V.Wf k := by
        intro k hk
        have h1 := hq_ub k hk
        have h2 := hq_lb k hk
        have h3 := (hper k hk).1
        have h4 : (Cn k : ℤ) < ((2 ^ V.Wf k : ℕ) : ℤ) := by
          rw [hCnZ k hk]
          have : ((VR.OFFf k + V.OFFf k : ℕ) : ℤ) < ((2 ^ V.Wf k : ℕ) : ℤ) := by
            exact_mod_cast h3
          push_cast at this ⊢
          omega
        exact_mod_cast h4
      -- honest per-boundary identity over ℤ
      have hqstep : ∀ k, k < G - 1 →
          q k * 2 ^ (B * gf k) = (if k = 0 then (0 : ℤ) else q (k - 1)) + QD k := by
        intro k hk
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [if_pos rfl, zero_add]
          have h1 := hq_mul 0 (by omega)
          have hSD0 : SD 0 = QD 0 := by
            rw [hSD_app]
            simp [hpos0]
          have hDk0 : Dkz 0 = (2 : ℤ) ^ (B * gf 0) := by
            rw [hDkz_app, hposS 0, hpos0]
            norm_num
          rw [hSD0, hDk0] at h1
          exact h1
        · rw [if_neg (by omega : ¬ k = 0)]
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          rw [show j + 1 - 1 = j from rfl]
          have h1 := hq_mul (j + 1) (by omega)
          have h0 := hq_mul j (by omega)
          have hstep : SD (j + 1) = SD j + QD (j + 1) * 2 ^ (B * posOf (j + 1)) := by
            rw [hSD_app, hSD_app, Finset.sum_range_succ]
          rw [hstep, ← h0] at h1
          have hDsplit : Dkz (j + 1) = 2 ^ (B * posOf (j + 1)) * 2 ^ (B * gf (j + 1)) := by
            rw [hDkz_app, he (j + 1), pow_add]
          have hDj : Dkz j = (2 : ℤ) ^ (B * posOf (j + 1)) := hDkz_app j
          rw [hDsplit, hDj] at h1
          have hpow_pos : (0 : ℤ) < 2 ^ (B * posOf (j + 1)) := by positivity
          have hcancel : q (j + 1) * 2 ^ (B * gf (j + 1)) * 2 ^ (B * posOf (j + 1))
              = (q j + QD (j + 1)) * 2 ^ (B * posOf (j + 1)) := by
            rw [add_mul]
            linarith [h1]
          have := mul_right_cancel₀ (ne_of_gt hpow_pos) hcancel
          linarith
      have hidxZ : ∀ k, k < G - 1 →
          QD k + (if k = 0 then (0 : ℤ) else (Cn (k - 1) : ℤ))
            + (VR.OFFf k : ℤ) * 2 ^ (B * gf k)
          = (Cn k : ℤ) * 2 ^ (B * gf k)
            + (if k = 0 then (0 : ℤ) else (VR.OFFf (k - 1) : ℤ)) := by
        intro k hk
        have hqs := hqstep k hk
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          simp only [↓reduceIte] at hqs ⊢
          rw [hCnZ 0 hk, add_mul]
          linarith
        · rw [if_neg (by omega : ¬ k = 0)] at hqs ⊢
          rw [if_neg (by omega : ¬ k = 0)]
          rw [hCnZ k hk, hCnZ (k - 1) (by omega), add_mul]
          linarith
      -- eval bridges
      have ha_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
        intro j hj
        rw [← h_input]
        simp [Vector.getElem_map]
      have hb_e : ∀ (j : ℕ) (hj : j < L),
          Expression.eval env.toEnvironment ((GroupedEqXV.rhsD B input_var.lhs input_var.rhs)[j]'hj) = (GroupedEqXV.rhsValD B input.lhs input.rhs)[j]'hj := by
        exact GroupedEqXV.rhsD_eval_bridge B env.toEnvironment input_var.lhs input_var.rhs input.lhs input.rhs
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
          (fun j hj => by rw [← h_input]; simp [Vector.getElem_map])
      have hDz_cast : ∀ (j : ℕ) (hj : j < L),
          ((Dz j : ℤ) : F p)
            = Expression.eval env.toEnvironment (input_var.lhs[j]'hj)
              - Expression.eval env.toEnvironment ((GroupedEqXV.rhsD B input_var.lhs input_var.rhs)[j]'hj) := by
        intro j hj
        simp only [hDz, dif_pos hj]
        rw [zsval_cast, ha_e j hj, hb_e j hj]
      have hGD_e : ∀ j : ℕ,
          Expression.eval env.toEnvironment (groupExprW B L gf posOf input_var.lhs j)
            - Expression.eval env.toEnvironment (groupExprW B L gf posOf (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) j)
          = ((QD j : ℤ) : F p) := by
        intro j
        rw [groupExprW_eval, groupExprW_eval, hQD_app, ← Finset.sum_sub_distrib, Int.cast_sum]
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        rw [pow_mul]
        by_cases h : posOf j + i < L
        · rw [dif_pos h, dif_pos h, ← sub_mul]
          congr 1
          rw [hDz_cast (posOf j + i) h]
        · rw [dif_neg h, dif_neg h]
          simp only [hDz, dif_neg h]
          simp
      have hbase_ne : ∀ k, k < G - 1 → ((2 : F p) ^ (B * gf k) ≠ 0) := by
        intro k hk
        have hnat : (((2 ^ (B * gf k) : ℕ) : F p) ≠ 0) := by
          intro hzero
          have hval : (((2 ^ (B * gf k) : ℕ) : F p).val) = 2 ^ (B * gf k) :=
            ZMod.val_natCast_of_lt (hpBg k hk)
          rw [hzero, ZMod.val_zero] at hval
          have : 0 < 2 ^ (B * gf k) := Nat.two_pow_pos _
          omega
        simpa [Nat.cast_pow] using hnat
      have hcarry_eval : ∀ k, k < G - 1 →
          Expression.eval env.toEnvironment
            (carryExpr B gf posOf VR.OFFf input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) k)
            = ((Cn k : ℕ) : F p) := by
        intro k hk
        induction k with
        | zero =>
            have hnatk := hidxZ 0 (by omega)
            simp only [↓reduceIte] at hnatk
            have hcast := congrArg (Int.cast : ℤ → F p) hnatk
            push_cast at hcast
            rw [← hGD_e 0] at hcast
            simp [carryExpr, Expression.eval]
            field_simp [hbase_ne 0 (by omega)]
            linear_combination hcast
        | succ j ih =>
            have hprev := ih (by omega)
            have hnatk := hidxZ (j + 1) (by omega)
            simp only [if_neg (by omega : ¬ j + 1 = 0), Nat.add_sub_cancel] at hnatk
            have hcast := congrArg (Int.cast : ℤ → F p) hnatk
            push_cast at hcast
            rw [← hGD_e (j + 1)] at hcast
            simp [carryExpr, Expression.eval, hprev]
            field_simp [hbase_ne (j + 1) (by omega)]
            linear_combination hcast
      unfold mainD
      refine GroupedEqXV.carryLoop_completeness B gf posOf VR.OFFf V.Wf hWok env
        input_var.lhs (GroupedEqXV.rhsD B input_var.lhs input_var.rhs) (G - 2) 0 i₀ fun i hi => ?_
      rw [Nat.zero_add, hcarry_eval i (by omega),
        ZMod.val_natCast_of_lt (lt_trans (hrange i (by omega)) (hWok i).2)]
      exact hrange i (by omega)

/-- Projection: the definitional-top assertion's `Assumptions` field. -/
lemma circuitD_assumptions_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuitD (L := L) B gf posOf G V VR hgv hB1).Assumptions
      = AssumptionsD B V.Nf VR.Nf := rfl

/-- Projection: the definitional-top assertion's `Spec` field. -/
lemma circuitD_spec_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuitD (L := L) B gf posOf G V VR hgv hB1).Spec = SpecD B V.Nf := rfl

/-- Projection: the definitional-top assertion has no requirement channels. -/
lemma circuitD_channels_req_eq (B : ℕ) (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GVDHyps p L B gf posOf G V VR)
    (hB1 : 1 ≤ B) [Fact (p > 2)] :
    (circuitD (L := L) B gf posOf G V VR hgv hB1).channelsWithRequirements = [] := rfl

end GroupedEqD

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
