import Solution.RSASSAPKCS1v15_SHA256_4096_65537.LessThanSel
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.GroupedEq
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Cost

/-!
# Grouped one-hot selector comparison — `LessThanSelG`

Drop-in replacement for `LessThanSel` (same `Inputs`, same `Assumptions`, same
`Spec`) that runs the lexicographic comparison at *super-limb* granularity:
`gl` consecutive limbs are packed into one field element
`Q_j = Σ_{i<gl} limb_{gl·j+i} · 2^(B·i) < 2^(B·gl)` (affine in the limbs, no
extra witnesses), and the one-hot selector, the prefix-gated equality battery,
the strict-less row, and the gap range check all operate on the
`G = ⌈m/gl⌉` group digits at base `2^(B·gl)`:

* witness a one-hot selector `s` over the `G` groups (booleanity + `Σ s = 1`),
* gating rows `(QB_j − QA_j) · (Σ_{t<j} s_t) = 0` force group equality above
  the selected group (one row per group instead of one per limb),
* a single witnessed difference cell `d` with one `B·gl`-bit range check and
  selection rows `s_j · (QB_j − QA_j − 1 − d) = 0` force
  `QA_k + 1 + d = QB_k` at the selected group `k`.

Normalized limbs give `Q_j < 2^(B·gl)`, so the group digits are genuine
base-`2^(B·gl)` digits and `Σ_j Q_j·2^(B·gl·j) = Σ_t limb_t·2^(B·t)`
(`GroupedEq.group_flatten`); the partial top group (`m = gl·(G−1) + r`) is
padded with `0` via the guarded `dif` idiom. Grouping requires the no-wrap
headroom `2^(B·gl+1) < p` (`GHyps`, decidable at concrete parameters).

Cost: `G + 1 + (B·gl − 1)` witnesses and `G + 1 + (G−1) + G + B·gl` rows
(= 139 / 225 at `m = 171`, `B = 24`, `gl = 4`), versus `195 / 537` for
`LessThanSel` at the same instance.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace LessThanSelG

/-! ## Group counting -/

/-- Number of groups of `gl` consecutive limbs covering the `m` limbs:
`⌈m/gl⌉`. -/
def numGroups (m gl : ℕ) : ℕ := (m + (gl - 1)) / gl

private lemma ceil_mul_ge (a g : ℕ) (hg : 1 ≤ g) : a ≤ g * ((a + (g - 1)) / g) := by
  have hdm := Nat.div_add_mod (a + (g - 1)) g
  have hr : (a + (g - 1)) % g < g := Nat.mod_lt _ (by omega)
  generalize hX : g * ((a + (g - 1)) / g) = X at hdm ⊢
  omega

/-- Coverage: `m ≤ gl · G`. -/
lemma numGroups_mul_ge (m gl : ℕ) (hgl : 1 ≤ gl) : m ≤ gl * numGroups m gl :=
  ceil_mul_ge m gl hgl

/-- There is at least one group. -/
lemma numGroups_pos (m gl : ℕ) [NeZero m] (hgl : 1 ≤ gl) : 0 < numGroups m gl := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have h := numGroups_mul_ge m gl hgl
  rcases Nat.eq_zero_or_pos (numGroups m gl) with h0 | hpos
  · rw [h0, Nat.mul_zero] at h; omega
  · exact hpos

/-- There are no more groups than limbs. -/
lemma numGroups_le (m gl : ℕ) (hgl : 1 ≤ gl) : numGroups m gl ≤ m := by
  unfold numGroups
  rw [Nat.div_le_iff_le_mul_add_pred hgl]
  have h := Nat.le_mul_of_pos_left m hgl
  omega

/-! ## The group-sum expression -/

/-- The `j`-th group-sum expression `Σ_{i<gl} x[gl·j+i] · 2^(B·i)` (affine in
the limb expressions; limbs beyond index `m−1` are padded with `0`). -/
def groupExpr (B gl : ℕ) (x : Var (BigInt m) (F p)) (j : ℕ) :
    Expression (F p) :=
  MulMod.polyEvalExpr
    (Vector.ofFn fun i : Fin gl =>
      if h : gl * j + i.val < m then x[gl * j + i.val]'h else 0)
    ((2 : F p) ^ B)

omit [NeZero m] in
/-- Evaluation of the group-sum expression. -/
lemma groupExpr_eval (env : Environment (F p)) (B gl : ℕ)
    (x : Var (BigInt m) (F p)) (j : ℕ) :
    Expression.eval env (groupExpr B gl x j)
      = ∑ i ∈ Finset.range gl,
          (if h : gl * j + i < m then Expression.eval env (x[gl * j + i]'h) else 0)
            * ((2 : F p) ^ B) ^ i := by
  rw [groupExpr, MulMod.polyEvalExpr_eval,
    ← Fin.sum_univ_eq_sum_range (fun i =>
      (if h : gl * j + i < m then Expression.eval env (x[gl * j + i]'h) else 0)
        * ((2 : F p) ^ B) ^ i)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Vector.getElem_ofFn]
  by_cases h : gl * j + i.val < m
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rfl

/-! ## Grouping hypotheses -/

/-- Field-size hypotheses for grouping at group length `gl`: `gl ≥ 1`, and the
strict-less row's ℕ-lift does not wrap (`2^(B·gl+1) < p` covers one super-limb
digit plus the gap witness). Decidable at concrete parameters. -/
def GHyps (p B gl : ℕ) : Prop := 1 ≤ gl ∧ 2 ^ (B * gl + 1) < p

/-! ## The `main` circuit -/

/-- The most-significant group index at which the evaluated group digits differ
(0 when they agree everywhere). Witness-generator helper. -/
private def diffIdx (B gl : ℕ) (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) : ℕ :=
  Nat.findGreatest
    (fun j => if j < numGroups m gl then
      Expression.eval env (groupExpr B gl a j) ≠ Expression.eval env (groupExpr B gl b j)
      else False)
    (numGroups m gl - 1)

/-- Sum of the first `i` selector cells, as a (linear) expression. -/
private def prefixSum {n : ℕ} (s : Vector (Expression (F p)) n) :
    ℕ → Expression (F p)
  | 0 => 0
  | i + 1 => prefixSum s i + (if h : i < n then s[i]'h else 0)

/-- The `main` circuit of `LessThanSelG`. -/
def main (P : BigIntParams p m) (gl : ℕ) (hgp : GHyps p P.B gl) [Fact (p > 2)]
    (input : Var (LessThanSel.Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  -- 1. one-hot selector at the most-significant differing group
  let s ← witnessVector (numGroups m gl) fun env =>
    Vector.ofFn fun j : Fin (numGroups m gl) =>
      if j.val = diffIdx P.B gl env.toEnvironment a b then (1 : F p) else 0

  -- booleanity of each selector cell
  let boolCs : Vector (Expression (F p)) (numGroups m gl) :=
    Vector.mapFinRange (numGroups m gl) fun k =>
      (s[k.val]'k.isLt) * ((s[k.val]'k.isLt) - 1)
  Circuit.forEach boolCs assertZero

  -- exactly one selected
  assertZero (prefixSum s (numGroups m gl) - 1)

  -- 2. grouped gating: every group above the selected one is equal
  let gateCs : Vector (Expression (F p)) (numGroups m gl - 1) :=
    Vector.mapFinRange (numGroups m gl - 1) fun k =>
      (groupExpr P.B gl b (k.val + 1) - groupExpr P.B gl a (k.val + 1))
        * prefixSum s (k.val + 1)
  Circuit.forEach gateCs assertZero

  -- 3. the strict difference at the selected group
  let d ← witnessVector 1 fun env =>
    let j := diffIdx P.B gl env.toEnvironment a b
    Vector.ofFn fun _ : Fin 1 =>
      (((Expression.eval env.toEnvironment (groupExpr P.B gl b j)).val
        - 1 - (Expression.eval env.toEnvironment (groupExpr P.B gl a j)).val : ℕ) : F p)

  let selCs : Vector (Expression (F p)) (numGroups m gl) :=
    Vector.mapFinRange (numGroups m gl) fun k =>
      (s[k.val]'k.isLt) * (groupExpr P.B gl b k.val - groupExpr P.B gl a k.val
        - (1 : Expression (F p)) - (d[0]'(by omega)))
  Circuit.forEach selCs assertZero

  -- 4. d < 2^(B·gl)
  RangeCheck.circuit (P.B * gl)
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ (P.B * gl))) hgp.2)
    (le_trans P.hB1 (Nat.le_mul_of_pos_right P.B hgp.1)) (d[0]'(by omega))

instance elaborated (P : BigIntParams p m) (gl : ℕ) (hgp : GHyps p P.B gl)
    [Fact (p > 2)] :
    ElaboratedCircuit (F p) (LessThanSel.Inputs m) unit (main P gl hgp) where
  -- s : G witnesses; d : 1 witness; range-check bits : B·gl − 1
  localLength _ := numGroups m gl + 1 + (P.B * gl - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
    simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated]

/-! ## ℕ-level cores (clean contexts) -/

/-- Lexicographic comparison core: digits equal above `k`, strictly smaller at
`k`, arbitrary (but bounded) below `k`. -/
private lemma selector_sound_core {B : ℕ} (m : ℕ) (An Bn : ℕ → ℕ) (k dv : ℕ)
    (hk : k < m)
    (hA : ∀ i, i < m → An i < 2 ^ B) (hB : ∀ i, i < m → Bn i < 2 ^ B)
    (heqAbove : ∀ i, k < i → i < m → An i = Bn i)
    (hsel : An k + 1 + dv = Bn k) :
    (∑ i ∈ Finset.range m, An i * 2 ^ (B * i))
      < ∑ i ∈ Finset.range m, Bn i * 2 ^ (B * i) := by
  induction m with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rcases Nat.lt_or_ge k n with hkn | hkn
    · -- the top digit is above `k`, hence equal on both sides
      have htop : An n = Bn n := heqAbove n hkn (by omega)
      have hih := ih hkn (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega))
        (fun i hi hi' => heqAbove i hi (by omega))
      rw [htop]
      omega
    · -- `k = n` is the top digit: strict difference there wins
      have hkeq : k = n := by omega
      rw [hkeq] at hsel
      have hlow : (∑ i ∈ Finset.range n, An i * 2 ^ (B * i)) < 2 ^ (B * n) := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact sum_lt_pow (fun i : Fin n => An i.val) (fun i => hA i.val (by omega))
      have hBk : Bn n * 2 ^ (B * n)
          = An n * 2 ^ (B * n) + 2 ^ (B * n) + dv * 2 ^ (B * n) := by
        rw [← hsel]; ring
      omega

/-- One-hot extraction: boolean cells with field sum `1` have exactly one `1`. -/
private lemma onehot_core {n : ℕ} (nlt : n < p) (sv : ℕ → F p)
    (hbool : ∀ i, i < n → sv i = 0 ∨ sv i = 1)
    (hsum : (∑ i ∈ Finset.range n, sv i) = 1) :
    ∃ k, k < n ∧ sv k = 1 ∧ ∀ j, j < n → j ≠ k → sv j = 0 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hval_le : ∀ i, i < n → (sv i).val ≤ 1 := by
    intro i hi
    rcases hbool i hi with h | h <;> simp [h, ZMod.val_one]
  have hN_le : (∑ i ∈ Finset.range n, (sv i).val) ≤ n := by
    calc (∑ i ∈ Finset.range n, (sv i).val)
        ≤ ∑ _i ∈ Finset.range n, 1 :=
          Finset.sum_le_sum fun i hi => hval_le i (Finset.mem_range.mp hi)
      _ = n := by simp
  have hcast : ((∑ i ∈ Finset.range n, (sv i).val : ℕ) : F p)
      = ∑ i ∈ Finset.range n, sv i := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => ZMod.natCast_zmod_val (sv i)
  have hN : (∑ i ∈ Finset.range n, (sv i).val) = 1 := by
    have h1 : ((∑ i ∈ Finset.range n, (sv i).val : ℕ) : F p) = ((1 : ℕ) : F p) := by
      rw [hcast, hsum]; norm_num
    have h2 := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt (lt_of_le_of_lt hN_le nlt),
      ZMod.val_natCast_of_lt (Fact.out : 1 < p)] at h2
  have hex : ∃ k, k < n ∧ (sv k).val = 1 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i ∈ Finset.range n, (sv i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have := hval_le i hi'
      have := h i hi'
      omega
    omega
  obtain ⟨k, hkn, hk1⟩ := hex
  refine ⟨k, hkn, ?_, ?_⟩
  · rcases hbool k hkn with h | h
    · rw [h, ZMod.val_zero] at hk1; omega
    · exact h
  · intro j hj hjk
    have hsplit : (sv k).val + ∑ i ∈ (Finset.range n).erase k, (sv i).val
        = ∑ i ∈ Finset.range n, (sv i).val :=
      Finset.add_sum_erase (Finset.range n) (fun i => (sv i).val)
        (Finset.mem_range.mpr hkn)
    have hrest : (∑ i ∈ (Finset.range n).erase k, (sv i).val) = 0 := by omega
    have hmem : j ∈ (Finset.range n).erase k :=
      Finset.mem_erase.mpr ⟨hjk, Finset.mem_range.mpr hj⟩
    have hjval : (sv j).val = 0 := by
      by_contra hne
      have hposj : 0 < (sv j).val := Nat.pos_of_ne_zero hne
      have hle : (sv j).val ≤ ∑ i ∈ (Finset.range n).erase k, (sv i).val :=
        Finset.single_le_sum (f := fun i => (sv i).val)
          (fun i _ => Nat.zero_le _) hmem
      omega
    exact (ZMod.val_eq_zero _).mp hjval

/-- Prefix sums of a one-hot family: `1` above the hot index, `0` at or below. -/
private lemma onehot_prefix {n : ℕ} (sv : ℕ → F p) (k : ℕ)
    (hk : sv k = 1) (hother : ∀ j, j < n → j ≠ k → sv j = 0) (_hkn : k < n) :
    ∀ i, i ≤ n → (∑ j ∈ Finset.range i, sv j) = if k < i then 1 else 0 := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    rw [Finset.sum_range_succ, ih (by omega)]
    by_cases hkt : k < t
    · rw [if_pos hkt, if_pos (by omega), hother t (by omega) (by omega)]
      ring
    · by_cases hkt' : k = t
      · rw [if_neg hkt, if_pos (by omega), ← hkt', hk]
        ring
      · rw [if_neg hkt, if_neg (by omega), hother t (by omega) (by omega)]
        ring

/-- Existence of the most-significant differing digit when the values differ,
with the larger value winning there. -/
private lemma msd_exists {B : ℕ} (m : ℕ) (An Bn : ℕ → ℕ)
    (hA : ∀ i, i < m → An i < 2 ^ B) (hB : ∀ i, i < m → Bn i < 2 ^ B)
    (hlt : (∑ i ∈ Finset.range m, An i * 2 ^ (B * i))
      < ∑ i ∈ Finset.range m, Bn i * 2 ^ (B * i)) :
    ∃ k, k < m ∧ An k < Bn k ∧ ∀ i, k < i → i < m → An i = Bn i := by
  induction m with
  | zero => simp at hlt
  | succ n ih =>
    rcases Nat.lt_trichotomy (An n) (Bn n) with hn | hn | hn
    · exact ⟨n, by omega, hn, fun i hi hi' => by omega⟩
    · -- equal top digits: recurse on the prefix
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hn] at hlt
      have hlt' : (∑ i ∈ Finset.range n, An i * 2 ^ (B * i))
          < ∑ i ∈ Finset.range n, Bn i * 2 ^ (B * i) := by omega
      obtain ⟨k, hk, hklt, hkeq⟩ := ih (fun i hi => hA i (by omega))
        (fun i hi => hB i (by omega)) hlt'
      refine ⟨k, by omega, hklt, ?_⟩
      intro i hi hi'
      rcases Nat.lt_or_ge i n with h | h
      · exact hkeq i hi h
      · rw [show i = n by omega, hn]
    · -- `An n > Bn n` contradicts the value inequality
      exfalso
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at hlt
      have hlowB : (∑ i ∈ Finset.range n, Bn i * 2 ^ (B * i)) < 2 ^ (B * n) := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact sum_lt_pow (fun i : Fin n => Bn i.val) (fun i => hB i.val (by omega))
      have hmul : (Bn n + 1) * 2 ^ (B * n) ≤ An n * 2 ^ (B * n) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega

/-- `Nat.findGreatest` on `n - 1` hits exactly the witness `k < n` when nothing
above `k` satisfies the predicate. -/
private lemma findGreatest_eq_of_top {P : ℕ → Prop} [DecidablePred P] {n k : ℕ}
    (hkn : k < n) (hPk : P k) (hnot : ∀ j, k < j → j < n → ¬P j) :
    Nat.findGreatest P (n - 1) = k := by
  have hfle : Nat.findGreatest P (n - 1) ≤ n - 1 := Nat.findGreatest_le (n - 1)
  have hkf : k ≤ Nat.findGreatest P (n - 1) := Nat.le_findGreatest (by omega) hPk
  rcases Nat.eq_or_lt_of_le hkf with heq | hlt
  · exact heq.symm
  · exact absurd (Nat.findGreatest_spec (by omega : k ≤ n - 1) hPk)
      (hnot _ hlt (by omega))

/-! ## Evaluation bridges -/

/-- Evaluating `prefixSum` gives the sum of the evaluated cells. -/
private lemma eval_prefixSum {n : ℕ} (env : Environment (F p))
    (s : Vector (Expression (F p)) n) :
    ∀ i, i ≤ n → Expression.eval env (prefixSum s i)
      = ∑ j ∈ Finset.range i, Expression.eval env (s[j]!) := by
  intro i
  induction i with
  | zero => intro _; simp [prefixSum, circuit_norm]
  | succ t ih =>
    intro ht
    have htn : t < n := ht
    rw [Finset.sum_range_succ, ← ih (by omega)]
    simp only [prefixSum, dif_pos htn]
    rw [getElem!_pos s t htn]
    simp [circuit_norm]

/-- Evaluating `prefixSum` on the witnessed selector cells gives the plain
environment sum. -/
private lemma eval_prefixSum_get {n : ℕ} (env : Environment (F p)) (off : ℕ) :
    ∀ i, i ≤ n → Expression.eval env
      (prefixSum (Vector.mapRange n fun t => var (F := F p) { index := off + t }) i)
      = ∑ j ∈ Finset.range i, env.get (off + j) := by
  intro i hi
  rw [eval_prefixSum env _ i hi]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := by
    have := Finset.mem_range.mp hj
    omega
  rw [getElem!_pos _ j hjn]
  simp [circuit_norm]

/-- `prefixSum` over affine cells is affine: it is a plain sum of selector cells.
Exported for the R1CS certificate. -/
theorem affine_prefixSum {n : ℕ} (s : Vector (Expression (F p)) n)
    (hs : Challenge.CostR1CS.AffineW s) :
    ∀ i, Challenge.CostR1CS.Affine (prefixSum s i) := by
  intro i
  induction i with
  | zero =>
    simp only [prefixSum]
    exact Challenge.CostR1CS.Affine.zero
  | succ t ih =>
    simp only [prefixSum]
    refine Challenge.CostR1CS.Affine.add ih ?_
    split
    · exact hs t ‹_›
    · exact Challenge.CostR1CS.Affine.zero

/-! ## The two proofs (standalone; never structure fields) -/

theorem soundness (P : BigIntParams p m) (gl : ℕ) (hgp : GHyps p P.B gl)
    [Fact (p > 2)] :
    FormalAssertion.Soundness (F p) (main P gl hgp)
      (LessThanSel.Assumptions P.B) (LessThanSel.Spec P.B) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  circuit_proof_start
  simp only [circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    Nat.mul_zero, Nat.add_zero, true_implies] at h_holds ⊢
  obtain ⟨h_bool, h_sum, h_gate, h_sel, h_range⟩ := h_holds
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
  have hgl : 1 ≤ gl := hgp.1
  have hp2 : 2 ^ (B * gl + 1) < p := hgp.2
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hG1 : 0 < numGroups m gl := numGroups_pos m gl hgl
  have hCov : m ≤ gl * numGroups m gl := numGroups_mul_ge m gl hgl
  have hGm : numGroups m gl ≤ m := numGroups_le m gl hgl
  set G := numGroups m gl with hGdef
  have hpBg : 2 ^ (B * gl) < p := by
    have hps : 2 ^ (B * gl + 1) = 2 ^ (B * gl) * 2 := pow_succ 2 (B * gl)
    omega
  -- ℕ-indexed views of the constraint rows
  have h_bool' : ∀ (j : ℕ), j < G →
      env.get (i₀ + j) * (env.get (i₀ + j) + -1) = 0 :=
    fun j hj => h_bool ⟨j, hj⟩
  have h_gate' : ∀ (j : ℕ) (hj : j < G - 1),
      (Expression.eval env (groupExpr B gl input_var.rhs (j + 1))
        + -Expression.eval env (groupExpr B gl input_var.lhs (j + 1)))
      * Expression.eval env
          (prefixSum (Vector.mapRange G fun t => var { index := i₀ + t }) (j + 1)) = 0 :=
    fun j hj => h_gate ⟨j, hj⟩
  have h_sel' : ∀ (j : ℕ) (hj : j < G),
      env.get (i₀ + j) * (Expression.eval env (groupExpr B gl input_var.rhs j)
        + -Expression.eval env (groupExpr B gl input_var.lhs j)
        + -1 + -env.get (i₀ + G)) = 0 :=
    fun j hj => h_sel ⟨j, hj⟩
  -- input-limb evaluations
  have ha_e : ∀ (j : ℕ) (hj : j < m),
      Expression.eval env (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
    intro j hj
    rw [← h_input]
    simp [Vector.getElem_map]
  have hb_e : ∀ (j : ℕ) (hj : j < m),
      Expression.eval env (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
    intro j hj
    rw [← h_input]
    simp [Vector.getElem_map]
  -- ℕ-indexed limb digit functions and their group digits
  set An : ℕ → ℕ := fun t => if h : t < m then (input.lhs[t]'h).val else 0 with hAn
  set Bn : ℕ → ℕ := fun t => if h : t < m then (input.rhs[t]'h).val else 0 with hBn
  set QA : ℕ → ℕ := fun j => ∑ i ∈ Finset.range gl, An (gl * j + i) * 2 ^ (B * i) with hQA
  set QB : ℕ → ℕ := fun j => ∑ i ∈ Finset.range gl, Bn (gl * j + i) * 2 ^ (B * i) with hQB
  have hQA_app : ∀ j, QA j = ∑ i ∈ Finset.range gl, An (gl * j + i) * 2 ^ (B * i) :=
    fun _ => rfl
  have hQB_app : ∀ j, QB j = ∑ i ∈ Finset.range gl, Bn (gl * j + i) * 2 ^ (B * i) :=
    fun _ => rfl
  have hAn_lt : ∀ t, An t < 2 ^ B := by
    intro t
    simp only [hAn]
    split
    · rename_i h; exact ha_norm ⟨t, h⟩
    · exact Nat.two_pow_pos B
  have hBn_lt : ∀ t, Bn t < 2 ^ B := by
    intro t
    simp only [hBn]
    split
    · rename_i h; exact hb_norm ⟨t, h⟩
    · exact Nat.two_pow_pos B
  have hQA_lt : ∀ j, QA j < 2 ^ (B * gl) := by
    intro j
    rw [hQA_app j, ← Fin.sum_univ_eq_sum_range (fun i => An (gl * j + i) * 2 ^ (B * i))]
    exact sum_lt_pow (fun i : Fin gl => An (gl * j + i.val))
      (fun i => hAn_lt (gl * j + i.val))
  have hQB_lt : ∀ j, QB j < 2 ^ (B * gl) := by
    intro j
    rw [hQB_app j, ← Fin.sum_univ_eq_sum_range (fun i => Bn (gl * j + i) * 2 ^ (B * i))]
    exact sum_lt_pow (fun i : Fin gl => Bn (gl * j + i.val))
      (fun i => hBn_lt (gl * j + i.val))
  -- eval bridges: the group-sum expressions evaluate to the ℕ group digits
  have hGA_e : ∀ j : ℕ,
      Expression.eval env (groupExpr B gl input_var.lhs j) = ((QA j : ℕ) : F p) := by
    intro j
    rw [groupExpr_eval, hQA_app j, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul]
    congr 1
    · by_cases h : gl * j + i < m
      · rw [dif_pos h, ha_e _ h]
        simp only [hAn, dif_pos h]
        rw [ZMod.natCast_zmod_val]
      · rw [dif_neg h]
        simp only [hAn, dif_neg h]
        simp
    · push_cast
      rw [pow_mul]
  have hGB_e : ∀ j : ℕ,
      Expression.eval env (groupExpr B gl input_var.rhs j) = ((QB j : ℕ) : F p) := by
    intro j
    rw [groupExpr_eval, hQB_app j, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul]
    congr 1
    · by_cases h : gl * j + i < m
      · rw [dif_pos h, hb_e _ h]
        simp only [hBn, dif_pos h]
        rw [ZMod.natCast_zmod_val]
      · rw [dif_neg h]
        simp only [hBn, dif_neg h]
        simp
    · push_cast
      rw [pow_mul]
  -- selector cells are boolean
  have hbool : ∀ j, j < G → env.get (i₀ + j) = 0 ∨ env.get (i₀ + j) = 1 := by
    intro j hj
    rcases mul_eq_zero.mp (h_bool' j hj) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  -- the selector cells sum to 1
  have hsum1 : (∑ j ∈ Finset.range G, env.get (i₀ + j)) = 1 := by
    rw [eval_prefixSum_get env i₀ G (le_refl G)] at h_sum
    linear_combination h_sum
  -- G < p, so the field sum determines the one-hot count
  have hmp : m < p := by
    have h1 : m + 1 ≤ 2 ^ (2 * B) * (m + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  have hGp : G < p := lt_of_le_of_lt hGm hmp
  obtain ⟨k, hkm, hk1, hk0⟩ :=
    onehot_core hGp (fun j => env.get (i₀ + j)) hbool hsum1
  have hk1' : env.get (i₀ + k) = 1 := hk1
  have hpre : ∀ i, i ≤ G →
      (∑ j ∈ Finset.range i, env.get (i₀ + j)) = if k < i then 1 else 0 :=
    onehot_prefix (fun j => env.get (i₀ + j)) k hk1 hk0 hkm
  -- group digits above the selected one agree
  have heqAbove_nat : ∀ i, k < i → i < G → QA i = QB i := by
    intro i hki hi
    have hi1 : i - 1 < G - 1 := by omega
    have hg := h_gate' (i - 1) hi1
    simp only [show i - 1 + 1 = i from by omega] at hg
    rw [eval_prefixSum_get env i₀ i (by omega), hpre i (by omega), if_pos hki,
      hGA_e i, hGB_e i, mul_one] at hg
    have hfe : ((QB i : ℕ) : F p) = ((QA i : ℕ) : F p) := by linear_combination hg
    have hval := congrArg ZMod.val hfe
    rw [ZMod.val_natCast_of_lt (lt_trans (hQB_lt i) hpBg),
      ZMod.val_natCast_of_lt (lt_trans (hQA_lt i) hpBg)] at hval
    omega
  -- the selected group satisfies `QA k + 1 + d = QB k`
  have hselk := h_sel' k hkm
  rw [hGA_e k, hGB_e k, hk1', one_mul] at hselk
  have hd : (env.get (i₀ + G)).val < 2 ^ (B * gl) := h_range
  have hQAk_val : (((QA k : ℕ) : F p)).val = QA k :=
    ZMod.val_natCast_of_lt (lt_trans (hQA_lt k) hpBg)
  have hQBk_val : (((QB k : ℕ) : F p)).val = QB k :=
    ZMod.val_natCast_of_lt (lt_trans (hQB_lt k) hpBg)
  have hone : (1 : F p).val = 1 := ZMod.val_one p
  have hzero : (0 : F p).val = 0 := ZMod.val_zero
  have hsum_lt : (((QA k : ℕ) : F p)).val + (env.get (i₀ + G)).val
      + (1 : F p).val + (0 : F p).val < p := by
    rw [hQAk_val, hone, hzero]
    have h1 : QA k < 2 ^ (B * gl) := hQA_lt k
    have hpw : 2 ^ (B * gl) * 2 = 2 ^ (B * gl + 1) := (pow_succ 2 (B * gl)).symm
    omega
  have hrhs_lt : (((QB k : ℕ) : F p)).val + (0 : F p).val * 2 ^ (B * gl) < p := by
    rw [hQBk_val, hzero]
    have h1 : QB k < 2 ^ (B * gl) := hQB_lt k
    omega
  have heq0 : ((QA k : ℕ) : F p) + env.get (i₀ + G) + 1 + 0
      - ((QB k : ℕ) : F p) - 0 * (2 ^ (B * gl) : F p) = 0 := by
    linear_combination -hselk
  have hlift := per_limb_lift (B := B * gl) ((QA k : ℕ) : F p) (env.get (i₀ + G)) 1 0
    ((QB k : ℕ) : F p) 0 hpBg hsum_lt hrhs_lt heq0
  rw [hQAk_val, hQBk_val, hone, hzero] at hlift
  have hsel_nat : QA k + 1 + (env.get (i₀ + G)).val = QB k := by omega
  -- the lexicographic core at base 2^(B·gl)
  have hQA_lt' : ∀ j, j < G → QA j < 2 ^ (B * gl) := fun j _ => hQA_lt j
  have hQB_lt' : ∀ j, j < G → QB j < 2 ^ (B * gl) := fun j _ => hQB_lt j
  have hcore := selector_sound_core (B := B * gl) G QA QB k
    (env.get (i₀ + G)).val hkm hQA_lt' hQB_lt' heqAbove_nat hsel_nat
  -- value bridges: base-2^B values are the base-2^(B·gl) group-digit sums
  have hval_a : BigInt.value B input.lhs
      = ∑ j ∈ Finset.range G, QA j * 2 ^ (B * gl * j) := by
    have h1 : BigInt.value B input.lhs = ∑ t ∈ Finset.range m, An t * 2 ^ (B * t) := by
      rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun t => An t * 2 ^ (B * t))]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
    rw [h1, GroupedEq.sum_extend_zero B m (gl * G) An hCov
      (fun t ht => by simp only [hAn, dif_neg (by omega : ¬ t < m)]),
      ← GroupedEq.group_flatten B gl An G]
  have hval_b : BigInt.value B input.rhs
      = ∑ j ∈ Finset.range G, QB j * 2 ^ (B * gl * j) := by
    have h1 : BigInt.value B input.rhs = ∑ t ∈ Finset.range m, Bn t * 2 ^ (B * t) := by
      rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun t => Bn t * 2 ^ (B * t))]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
    rw [h1, GroupedEq.sum_extend_zero B m (gl * G) Bn hCov
      (fun t ht => by simp only [hBn, dif_neg (by omega : ¬ t < m)]),
      ← GroupedEq.group_flatten B gl Bn G]
  rw [LessThanSel.Spec, hval_a, hval_b]
  exact hcore

theorem completeness (P : BigIntParams p m) (gl : ℕ) (hgp : GHyps p P.B gl)
    [Fact (p > 2)] :
    FormalAssertion.Completeness (F p) (main P gl hgp)
      (LessThanSel.Assumptions P.B) (LessThanSel.Spec P.B) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  circuit_proof_start
  simp only [circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    Nat.mul_zero, Nat.add_zero] at h_env ⊢
  obtain ⟨h_swit, h_dwit⟩ := h_env
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
  have hgl : 1 ≤ gl := hgp.1
  have hp2 : 2 ^ (B * gl + 1) < p := hgp.2
  have hG1 : 0 < numGroups m gl := numGroups_pos m gl hgl
  have hCov : m ≤ gl * numGroups m gl := numGroups_mul_ge m gl hgl
  set G := numGroups m gl with hGdef
  have hpBg : 2 ^ (B * gl) < p := by
    have hps : 2 ^ (B * gl + 1) = 2 ^ (B * gl) * 2 := pow_succ 2 (B * gl)
    omega
  -- input-limb evaluations
  have ha_e : ∀ (j : ℕ) (hj : j < m),
      Expression.eval env.toEnvironment (input_var.lhs[j]'hj) = input.lhs[j]'hj := by
    intro j hj
    rw [← h_input]
    simp [Vector.getElem_map]
  have hb_e : ∀ (j : ℕ) (hj : j < m),
      Expression.eval env.toEnvironment (input_var.rhs[j]'hj) = input.rhs[j]'hj := by
    intro j hj
    rw [← h_input]
    simp [Vector.getElem_map]
  -- ℕ-indexed limb digit functions and their group digits
  set An : ℕ → ℕ := fun t => if h : t < m then (input.lhs[t]'h).val else 0 with hAn
  set Bn : ℕ → ℕ := fun t => if h : t < m then (input.rhs[t]'h).val else 0 with hBn
  set QA : ℕ → ℕ := fun j => ∑ i ∈ Finset.range gl, An (gl * j + i) * 2 ^ (B * i) with hQA
  set QB : ℕ → ℕ := fun j => ∑ i ∈ Finset.range gl, Bn (gl * j + i) * 2 ^ (B * i) with hQB
  have hQA_app : ∀ j, QA j = ∑ i ∈ Finset.range gl, An (gl * j + i) * 2 ^ (B * i) :=
    fun _ => rfl
  have hQB_app : ∀ j, QB j = ∑ i ∈ Finset.range gl, Bn (gl * j + i) * 2 ^ (B * i) :=
    fun _ => rfl
  have hAn_lt : ∀ t, An t < 2 ^ B := by
    intro t
    simp only [hAn]
    split
    · rename_i h; exact ha_norm ⟨t, h⟩
    · exact Nat.two_pow_pos B
  have hBn_lt : ∀ t, Bn t < 2 ^ B := by
    intro t
    simp only [hBn]
    split
    · rename_i h; exact hb_norm ⟨t, h⟩
    · exact Nat.two_pow_pos B
  have hQA_lt : ∀ j, QA j < 2 ^ (B * gl) := by
    intro j
    rw [hQA_app j, ← Fin.sum_univ_eq_sum_range (fun i => An (gl * j + i) * 2 ^ (B * i))]
    exact sum_lt_pow (fun i : Fin gl => An (gl * j + i.val))
      (fun i => hAn_lt (gl * j + i.val))
  have hQB_lt : ∀ j, QB j < 2 ^ (B * gl) := by
    intro j
    rw [hQB_app j, ← Fin.sum_univ_eq_sum_range (fun i => Bn (gl * j + i) * 2 ^ (B * i))]
    exact sum_lt_pow (fun i : Fin gl => Bn (gl * j + i.val))
      (fun i => hBn_lt (gl * j + i.val))
  -- eval bridges
  have hGA_e : ∀ j : ℕ, Expression.eval env.toEnvironment
      (groupExpr B gl input_var.lhs j) = ((QA j : ℕ) : F p) := by
    intro j
    rw [groupExpr_eval, hQA_app j, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul]
    congr 1
    · by_cases h : gl * j + i < m
      · rw [dif_pos h, ha_e _ h]
        simp only [hAn, dif_pos h]
        rw [ZMod.natCast_zmod_val]
      · rw [dif_neg h]
        simp only [hAn, dif_neg h]
        simp
    · push_cast
      rw [pow_mul]
  have hGB_e : ∀ j : ℕ, Expression.eval env.toEnvironment
      (groupExpr B gl input_var.rhs j) = ((QB j : ℕ) : F p) := by
    intro j
    rw [groupExpr_eval, hQB_app j, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_mul]
    congr 1
    · by_cases h : gl * j + i < m
      · rw [dif_pos h, hb_e _ h]
        simp only [hBn, dif_pos h]
        rw [ZMod.natCast_zmod_val]
      · rw [dif_neg h]
        simp only [hBn, dif_neg h]
        simp
    · push_cast
      rw [pow_mul]
  -- injectivity of the group-digit casts
  have hcast_inj : ∀ x y : ℕ, x < 2 ^ (B * gl) → y < 2 ^ (B * gl) →
      (((x : ℕ) : F p) = ((y : ℕ) : F p) ↔ x = y) := by
    intro x y hx hy
    constructor
    · intro h
      have hval := congrArg ZMod.val h
      rwa [ZMod.val_natCast_of_lt (lt_trans hx hpBg),
        ZMod.val_natCast_of_lt (lt_trans hy hpBg)] at hval
    · intro h; rw [h]
  -- value bridges and the most-significant differing group
  have hval_a : BigInt.value B input.lhs
      = ∑ j ∈ Finset.range G, QA j * 2 ^ (B * gl * j) := by
    have h1 : BigInt.value B input.lhs = ∑ t ∈ Finset.range m, An t * 2 ^ (B * t) := by
      rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun t => An t * 2 ^ (B * t))]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
    rw [h1, GroupedEq.sum_extend_zero B m (gl * G) An hCov
      (fun t ht => by simp only [hAn, dif_neg (by omega : ¬ t < m)]),
      ← GroupedEq.group_flatten B gl An G]
  have hval_b : BigInt.value B input.rhs
      = ∑ j ∈ Finset.range G, QB j * 2 ^ (B * gl * j) := by
    have h1 : BigInt.value B input.rhs = ∑ t ∈ Finset.range m, Bn t * 2 ^ (B * t) := by
      rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun t => Bn t * 2 ^ (B * t))]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
    rw [h1, GroupedEq.sum_extend_zero B m (gl * G) Bn hCov
      (fun t ht => by simp only [hBn, dif_neg (by omega : ¬ t < m)]),
      ← GroupedEq.group_flatten B gl Bn G]
  have hQA_lt' : ∀ j, j < G → QA j < 2 ^ (B * gl) := fun j _ => hQA_lt j
  have hQB_lt' : ∀ j, j < G → QB j < 2 ^ (B * gl) := fun j _ => hQB_lt j
  have hlt : (∑ j ∈ Finset.range G, QA j * 2 ^ (B * gl * j))
      < ∑ j ∈ Finset.range G, QB j * 2 ^ (B * gl * j) := by
    rw [← hval_a, ← hval_b]
    exact h_spec
  obtain ⟨k, hkm, hklt, hkeq⟩ := msd_exists (B := B * gl) G QA QB hQA_lt' hQB_lt' hlt
  -- the witness generator's most-significant-difference index is exactly `k`
  have hdiff : diffIdx B gl env.toEnvironment input_var.lhs input_var.rhs = k := by
    unfold diffIdx
    apply findGreatest_eq_of_top (n := numGroups m gl) hkm
    · simp only [if_pos (show k < numGroups m gl from hkm)]
      rw [hGA_e k, hGB_e k]
      intro hcontra
      rw [hcast_inj (QA k) (QB k) (hQA_lt k) (hQB_lt k)] at hcontra
      omega
    · intro j hkj hj
      simp only [if_pos hj]
      rw [hGA_e j, hGB_e j]
      exact not_not_intro ((hcast_inj (QA j) (QB j) (hQA_lt j) (hQB_lt j)).mpr
        (hkeq j hkj hj))
  -- selector cells are the one-hot indicator of `k`
  have hsv : ∀ (j : ℕ), j < G → env.get (i₀ + j) = if j = k then 1 else 0 := by
    intro j hj
    have h := h_swit ⟨j, hj⟩
    simp only [Vector.getElem_ofFn, hdiff] at h
    exact h
  -- the witnessed difference cell
  have hd0 : env.get (i₀ + G) = ((QB k - 1 - QA k : ℕ) : F p) := by
    have h := h_dwit ⟨0, Nat.zero_lt_one⟩
    simp only [Vector.getElem_ofFn, hdiff] at h
    rw [hGB_e k, hGA_e k,
      ZMod.val_natCast_of_lt (lt_trans (hQB_lt k) hpBg),
      ZMod.val_natCast_of_lt (lt_trans (hQA_lt k) hpBg)] at h
    exact h
  have hd0_lt : QB k - 1 - QA k < 2 ^ (B * gl) := by
    have := hQB_lt k
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. booleanity of the selector cells
    intro i
    rw [hsv i.val i.isLt]
    by_cases hik : i.val = k
    · rw [if_pos hik]; ring
    · rw [if_neg hik]; ring
  · -- 2. the selector cells sum to 1
    rw [eval_prefixSum_get env.toEnvironment i₀ G (le_refl G)]
    rw [show (∑ j ∈ Finset.range G, env.get (i₀ + j))
        = ∑ j ∈ Finset.range G, if j = k then (1 : F p) else 0 from
      Finset.sum_congr rfl fun j hj => hsv j (Finset.mem_range.mp hj)]
    rw [Finset.sum_ite_eq' (Finset.range G) k (fun _ => (1 : F p)),
      if_pos (Finset.mem_range.mpr hkm)]
    ring
  · -- 3. grouped gating rows: groups above `k` agree
    intro i
    have hi1 : i.val + 1 < G := by omega
    rw [eval_prefixSum_get env.toEnvironment i₀ (i.val + 1) (by omega)]
    rw [show (∑ j ∈ Finset.range (i.val + 1), env.get (i₀ + j))
        = if k < i.val + 1 then 1 else 0 from
      onehot_prefix (fun j => env.get (i₀ + j)) k
        (by show env.get (i₀ + k) = 1; rw [hsv k hkm, if_pos rfl])
        (fun j hj hjk => by
          show env.get (i₀ + j) = 0
          rw [hsv j hj, if_neg hjk])
        hkm (i.val + 1) (by omega)]
    by_cases hki : k < i.val + 1
    · have hce : ((QA (i.val + 1) : ℕ) : F p) = ((QB (i.val + 1) : ℕ) : F p) :=
        (hcast_inj (QA (i.val + 1)) (QB (i.val + 1)) (hQA_lt _) (hQB_lt _)).mpr
          (hkeq (i.val + 1) hki hi1)
      rw [if_pos hki, hGA_e (i.val + 1), hGB_e (i.val + 1), hce]
      ring
    · rw [if_neg hki]
      ring
  · -- 4. selection rows
    intro i
    by_cases hik : i.val = k
    · simp only [hik]
      rw [hsv k hkm, if_pos rfl, one_mul, hGA_e k, hGB_e k, hd0]
      have hnat : QA k + 1 + (QB k - 1 - QA k) = QB k := by omega
      have hcast := congrArg (Nat.cast : ℕ → F p) hnat
      push_cast at hcast
      linear_combination -hcast
    · rw [hsv i.val i.isLt, if_neg hik]
      ring
  · -- 5. the difference cell is `B·gl`-bit
    rw [hd0, ZMod.val_natCast_of_lt (lt_trans hd0_lt hpBg)]
    exact hd0_lt

/-- The `LessThanSelG` formal assertion: two normalized big integers satisfy
`lhs.value B < rhs.value B`, via a one-hot most-significant-difference selector
over `gl`-limb super-limbs. Drop-in replacement for `LessThanSel.circuit`. -/
def circuit (P : BigIntParams p m) (gl : ℕ) (hgp : GHyps p P.B gl)
    [Fact (p > 2)] : FormalAssertion (F p) (LessThanSel.Inputs m) where
  main := main P gl hgp
  Assumptions := LessThanSel.Assumptions P.B
  Spec := LessThanSel.Spec P.B
  soundness := soundness P gl hgp
  completeness := completeness P gl hgp

end LessThanSelG

end

/-! ## Cost / R1CS certificates -/

namespace GadgetCost

open Challenge.Instances.RSASSAPKCS1v15_SHA256_4096_65537.Interface
open Challenge.CostR1CS

variable {m : ℕ}

/-- Cost of `LessThanSelG.main P gl hgp input`: witness the one-hot group
selector (`G`), booleanity forEach (`G` rows), the selector-sum row (1), grouped
gating forEach (`G − 1` rows), witness the difference cell (1), selection
forEach (`G` rows), and one implicit `B·gl`-bit range check on the difference
cell (`B·gl − 1` / `B·gl`). -/
theorem costIs_lessThanSelG (P : BigIntParams circomPrime m) (gl : ℕ)
    (hgp : LessThanSelG.GHyps circomPrime P.B gl)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime)) :
    CostIs (LessThanSelG.main P gl hgp input)
      ⟨LessThanSelG.numGroups m gl + 1 + (P.B * gl - 1),
       LessThanSelG.numGroups m gl + 1 + (LessThanSelG.numGroups m gl - 1)
         + LessThanSelG.numGroups m gl + P.B * gl⟩ := by
  rw [show (⟨LessThanSelG.numGroups m gl + 1 + (P.B * gl - 1),
        LessThanSelG.numGroups m gl + 1 + (LessThanSelG.numGroups m gl - 1)
          + LessThanSelG.numGroups m gl + P.B * gl⟩ : Count)
        = ⟨LessThanSelG.numGroups m gl, 0⟩
          + (⟨LessThanSelG.numGroups m gl * 0, LessThanSelG.numGroups m gl * 1⟩
            + (⟨0, 1⟩ + (⟨(LessThanSelG.numGroups m gl - 1) * 0,
                (LessThanSelG.numGroups m gl - 1) * 1⟩
              + (⟨1, 0⟩ + (⟨LessThanSelG.numGroups m gl * 0,
                  LessThanSelG.numGroups m gl * 1⟩
                + ⟨P.B * gl - 1, P.B * gl⟩))))) from by
      congr 1 <;> simp only [Count.add_allocations, Count.add_constraints] <;> ring]
  unfold LessThanSelG.main
  refine CostIs.bind
    (CostIs.witnessVector (F := F circomPrime) (LessThanSelG.numGroups m gl) _)
    fun s => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  refine CostIs.bind (CostIs.assertZero _) fun _ => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  refine CostIs.bind (CostIs.witnessVector (F := F circomPrime) 1 _) fun d => ?_
  refine CostIs.bind (CostIs.forEach fun a n => CostIs.assertZero _ n) fun _ => ?_
  exact costIs_assertion_implicitRangeCheck (P.B * gl)
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ (P.B * gl))) hgp.2)
    (le_trans P.hB1 (Nat.le_mul_of_pos_right P.B hgp.1)) _

theorem costIs_assertion_lessThanSelG (P : BigIntParams circomPrime m) (gl : ℕ)
    (hgp : LessThanSelG.GHyps circomPrime P.B gl)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime)) :
    CostIs (assertion (LessThanSelG.circuit P gl hgp) input)
      ⟨LessThanSelG.numGroups m gl + 1 + (P.B * gl - 1),
       LessThanSelG.numGroups m gl + 1 + (LessThanSelG.numGroups m gl - 1)
         + LessThanSelG.numGroups m gl + P.B * gl⟩ :=
  CostIs.assertion (fun n => costIs_lessThanSelG P gl hgp input n)

/-- The group-sum expression is affine when the limb expressions are. -/
theorem affine_groupExprSel [NeZero m] (B gl : ℕ)
    (x : Var (BigInt m) (F circomPrime)) (hx : AffineW x) (k : ℕ) :
    Affine (LessThanSelG.groupExpr B gl x k) := by
  unfold LessThanSelG.groupExpr
  refine affine_polyEvalExpr _ _ fun i hi => ?_
  rw [Vector.getElem_ofFn]
  split
  · rename_i h
    exact hx _ h
  · exact Affine.zero

theorem isR1CS_lessThanSelG (P : BigIntParams circomPrime m) (gl : ℕ)
    (hgp : LessThanSelG.GHyps circomPrime P.B gl)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (LessThanSelG.main P gl hgp input) := by
  unfold LessThanSelG.main
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec (LessThanSelG.numGroups m gl) _)
    fun ns => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- booleanity rows: each `s · (s - 1)` is a product of affine witnessed cells
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul (affineW_witnessVector_output _ _ _ i.val i.isLt)
      (Affine.sub (affineW_witnessVector_output _ _ _ i.val i.isLt) (Affine.const 1))
  refine IsR1CSCirc.bind (IsR1CSCirc.assertZero ?_) fun _ => ?_
  · -- the selector-sum row is affine
    exact isR1CSRow_of_affine (Affine.sub
      (LessThanSelG.affine_prefixSum _
        (affineW_witnessVector_output (LessThanSelG.numGroups m gl) _ ns)
        (LessThanSelG.numGroups m gl))
      (Affine.const 1))
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- grouped gating rows: `(QB − QA) · prefixSum` is a product of two affine forms
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul
      (Affine.sub (affine_groupExprSel P.B gl input.rhs hr (i.val + 1))
        (affine_groupExprSel P.B gl input.lhs hl (i.val + 1)))
      (LessThanSelG.affine_prefixSum _
        (affineW_witnessVector_output (LessThanSelG.numGroups m gl) _ ns) (i.val + 1))
  refine IsR1CSCirc.bind_out (isR1CS_witnessVec 1 _) fun nd => ?_
  refine IsR1CSCirc.bind ?_ fun _ => ?_
  · -- selection rows: `s · (QB − QA − 1 − d)` is a product of two affine forms
    refine IsR1CSCirc.forEach_mem (α := Expression (F circomPrime)) fun i k => ?_
    refine IsR1CSCirc.assertZero ?_ k
    rw [Vector.getElem_mapFinRange]
    exact isR1CSRow_mul
      (affineW_witnessVector_output (LessThanSelG.numGroups m gl) _ ns i.val i.isLt)
      (Affine.sub (Affine.sub (Affine.sub (affine_groupExprSel P.B gl input.rhs hr i.val)
          (affine_groupExprSel P.B gl input.lhs hl i.val))
        (Affine.const 1)) (affineW_witnessVector_output 1 _ nd 0 (by omega)))
  -- the range-check subcircuit on the witnessed difference cell
  exact isR1CS_assertion_implicitRangeCheck (P.B * gl)
    (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ (P.B * gl))) hgp.2)
    (le_trans P.hB1 (Nat.le_mul_of_pos_right P.B hgp.1)) _
    (affineW_witnessVector_output 1 _ nd 0 (by omega))

theorem isR1CS_assertion_lessThanSelG (P : BigIntParams circomPrime m) (gl : ℕ)
    (hgp : LessThanSelG.GHyps circomPrime P.B gl)
    [Fact (circomPrime > 2)] [NeZero m]
    (input : Var (LessThanSel.Inputs m) (F circomPrime))
    (hl : AffineW input.lhs) (hr : AffineW input.rhs) :
    IsR1CSCirc (assertion (LessThanSelG.circuit P gl hgp) input) :=
  IsR1CSCirc.assertion (fun n => isR1CS_lessThanSelG P gl hgp input hl hr n)

end GadgetCost
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
