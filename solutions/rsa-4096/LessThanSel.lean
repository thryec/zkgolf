import Solution.RSASSAPKCS1v15_SHA256_4096_65537.RangeCheck
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Theorems
import Challenge.Utils.CostR1CS

/-!
# RSA big-integer comparison via a one-hot selector — `LessThanSel`

Replaces the borrow-chain `LessThan`/`LessThanTight` (which fully range-checks a
witnessed `m`-limb difference: ~4.1k witnesses / ~4.2k rows) with a
lexicographic comparison at the most-significant differing limb:

* witness a one-hot selector `s` (`m` bits, booleanity + `Σ s = 1`),
* gating rows `(rhs[i] − lhs[i]) · (Σ_{j<i} s_j) = 0` force `rhs[i] = lhs[i]`
  for every limb *above* the selected one,
* a single witnessed difference cell `d` with one `B`-bit range check and
  selection rows `s_k · (rhs[k] − lhs[k] − 1 − d) = 0` force
  `lhs[k] + 1 + d = rhs[k]` at the selected limb `k`.

Normalized limbs then give `lhs.value < rhs.value` lexicographically.
Cost: `m + 1 + (B−1)` witnesses and `m + 1 + (m−1) + m + B` rows
(= 155 / 223 at `m = 34`, `B = 121`), versus 4,129 / 4,163 for the chain.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace LessThanSel

/-- Inputs of `LessThanSel`: `lhs` and `rhs`, asserting `lhs.value < rhs.value`. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
deriving ProvableStruct

/-- The most-significant limb index at which the evaluated inputs differ
(0 when they agree everywhere). Witness-generator helper. -/
private def diffIdx (env : Environment (F p)) (a b : Var (BigInt m) (F p)) : ℕ :=
  Nat.findGreatest
    (fun j => if h : j < m then
      Expression.eval env (a[j]'h) ≠ Expression.eval env (b[j]'h) else False)
    (m - 1)

/-- Sum of the first `i` selector cells, as a (linear) expression. -/
private def prefixSum (s : Vector (Expression (F p)) m) : ℕ → Expression (F p)
  | 0 => 0
  | i + 1 => prefixSum s i + (if h : i < m then s[i]'h else 0)

/-- The `main` circuit of `LessThanSel`. -/
def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let a := input.lhs
  let b := input.rhs

  -- 1. one-hot selector at the most-significant differing limb
  let s ← witnessVector m fun env =>
    Vector.ofFn fun i : Fin m =>
      if i.val = diffIdx env.toEnvironment a b then (1 : F p) else 0

  -- booleanity of each selector cell
  let boolCs : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    (s[k.val]'k.isLt) * ((s[k.val]'k.isLt) - 1)
  Circuit.forEach boolCs assertZero

  -- exactly one selected
  assertZero (prefixSum s m - 1)

  -- 2. gating: every limb above the selected one is equal
  let gateCs : Vector (Expression (F p)) (m - 1) := Vector.mapFinRange (m - 1) fun k =>
    ((b[k.val + 1]'(by omega)) - (a[k.val + 1]'(by omega))) * prefixSum s (k.val + 1)
  Circuit.forEach gateCs assertZero

  -- 3. the strict difference at the selected limb
  let d ← witnessVector 1 fun env =>
    let j := diffIdx env.toEnvironment a b
    Vector.ofFn fun _ : Fin 1 =>
      if h : j < m then
        (((Expression.eval env.toEnvironment (b[j]'h)).val
          - 1 - (Expression.eval env.toEnvironment (a[j]'h)).val : ℕ) : F p)
      else 0

  let selCs : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    (s[k.val]'k.isLt) * ((b[k.val]'k.isLt) - (a[k.val]'k.isLt)
      - (1 : Expression (F p)) - (d[0]'(by omega)))
  Circuit.forEach selCs assertZero

  -- 4. d < 2^B
  RangeCheck.circuit P.B P.hB P.hB1 (d[0]'(by omega))

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where
  -- s : m witnesses; d : 1 witness; range-check bits : B − 1
  localLength _ := m + 1 + (P.B - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated, RangeCheck.main]
    simp +arith [circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated,
      RangeCheck.main]
  channelsLawful := by
    intro offset
    simp only [main, circuit_norm, RangeCheck.circuit, RangeCheck.elaborated, RangeCheck.main]

/-- Preconditions: both big integers are normalized. -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B

/-- Postcondition: `lhs.value B < rhs.value B`. -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B < input.rhs.value B

/-! ## ℕ-level cores (clean contexts) -/

/-- Full-digit geometric sum: `Σ_{i<k} (2^B − 1)·2^(B·i) = 2^(B·k) − 1`. -/
private lemma geom_full (B : ℕ) : ∀ k : ℕ,
    (∑ i ∈ Finset.range k, (2 ^ B - 1) * 2 ^ (B * i)) = 2 ^ (B * k) - 1 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow : (2 : ℕ) ^ (B * (n + 1)) = 2 ^ B * 2 ^ (B * n) := by
      rw [← pow_add]; congr 1; ring
    have h1 : 1 ≤ (2 : ℕ) ^ (B * n) := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (B * n) ≤ 2 ^ B * 2 ^ (B * n) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos B)
    rw [hpow, Nat.sub_mul, Nat.one_mul]
    omega

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
private lemma onehot_core (mlt : m < p) (sv : ℕ → F p)
    (hbool : ∀ i, i < m → sv i = 0 ∨ sv i = 1)
    (hsum : (∑ i ∈ Finset.range m, sv i) = 1) :
    ∃ k, k < m ∧ sv k = 1 ∧ ∀ j, j < m → j ≠ k → sv j = 0 := by
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hval_le : ∀ i, i < m → (sv i).val ≤ 1 := by
    intro i hi
    rcases hbool i hi with h | h <;> simp [h, ZMod.val_one]
  have hN_le : (∑ i ∈ Finset.range m, (sv i).val) ≤ m := by
    calc (∑ i ∈ Finset.range m, (sv i).val)
        ≤ ∑ _i ∈ Finset.range m, 1 :=
          Finset.sum_le_sum fun i hi => hval_le i (Finset.mem_range.mp hi)
      _ = m := by simp
  have hcast : ((∑ i ∈ Finset.range m, (sv i).val : ℕ) : F p)
      = ∑ i ∈ Finset.range m, sv i := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => ZMod.natCast_zmod_val (sv i)
  have hN : (∑ i ∈ Finset.range m, (sv i).val) = 1 := by
    have h1 : ((∑ i ∈ Finset.range m, (sv i).val : ℕ) : F p) = ((1 : ℕ) : F p) := by
      rw [hcast, hsum]; norm_num
    have h2 := congrArg ZMod.val h1
    rwa [ZMod.val_natCast_of_lt (lt_of_le_of_lt hN_le mlt),
      ZMod.val_natCast_of_lt (Fact.out : 1 < p)] at h2
  have hex : ∃ k, k < m ∧ (sv k).val = 1 := by
    by_contra h
    push_neg at h
    have hzero : (∑ i ∈ Finset.range m, (sv i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have := hval_le i hi'
      have := h i hi'
      omega
    omega
  obtain ⟨k, hkm, hk1⟩ := hex
  refine ⟨k, hkm, ?_, ?_⟩
  · rcases hbool k hkm with h | h
    · rw [h, ZMod.val_zero] at hk1; omega
    · exact h
  · intro j hj hjk
    have hsplit : (sv k).val + ∑ i ∈ (Finset.range m).erase k, (sv i).val
        = ∑ i ∈ Finset.range m, (sv i).val :=
      Finset.add_sum_erase (Finset.range m) (fun i => (sv i).val)
        (Finset.mem_range.mpr hkm)
    have hrest : (∑ i ∈ (Finset.range m).erase k, (sv i).val) = 0 := by omega
    have hmem : j ∈ (Finset.range m).erase k :=
      Finset.mem_erase.mpr ⟨hjk, Finset.mem_range.mpr hj⟩
    have hjval : (sv j).val = 0 := by
      by_contra hne
      have hposj : 0 < (sv j).val := Nat.pos_of_ne_zero hne
      have hle : (sv j).val ≤ ∑ i ∈ (Finset.range m).erase k, (sv i).val :=
        Finset.single_le_sum (f := fun i => (sv i).val)
          (fun i _ => Nat.zero_le _) hmem
      omega
    exact (ZMod.val_eq_zero _).mp hjval

/-- Prefix sums of a one-hot family: `1` above the hot index, `0` at or below. -/
private lemma onehot_prefix (sv : ℕ → F p) (k : ℕ)
    (hk : sv k = 1) (hother : ∀ j, j < m → j ≠ k → sv j = 0) (hkm : k < m) :
    ∀ i, i ≤ m → (∑ j ∈ Finset.range i, sv j) = if k < i then 1 else 0 := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ, ih (by omega)]
    by_cases hkn : k < n
    · rw [if_pos hkn, if_pos (by omega), hother n (by omega) (by omega)]
      ring
    · by_cases hkn' : k = n
      · rw [if_neg hkn, if_pos (by omega), ← hkn', hk]
        ring
      · rw [if_neg hkn, if_neg (by omega), hother n (by omega) (by omega)]
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
private lemma eval_prefixSum (env : Environment (F p))
    (s : Vector (Expression (F p)) m) :
    ∀ i, i ≤ m → Expression.eval env (prefixSum s i)
      = ∑ j ∈ Finset.range i, Expression.eval env (s[j]!) := by
  intro i
  induction i with
  | zero => intro _; simp [prefixSum, circuit_norm]
  | succ n ih =>
    intro hn
    have hnm : n < m := hn
    rw [Finset.sum_range_succ, ← ih (by omega)]
    simp only [prefixSum, dif_pos hnm]
    rw [getElem!_pos s n hnm]
    simp [circuit_norm]

/-- Evaluating `prefixSum` on the witnessed selector cells gives the plain
environment sum. -/
private lemma eval_prefixSum_get (env : Environment (F p)) (off : ℕ) :
    ∀ i, i ≤ m → Expression.eval env
      (prefixSum (Vector.mapRange m fun t => var (F := F p) { index := off + t }) i)
      = ∑ j ∈ Finset.range i, env.get (off + j) := by
  intro i hi
  rw [eval_prefixSum env _ i hi]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j < m := by
    have := Finset.mem_range.mp hj
    omega
  rw [getElem!_pos _ j hjm]
  simp [circuit_norm]

omit [NeZero m] in
/-- `prefixSum` over affine cells is affine: it is a plain sum of selector cells.
Exported for the R1CS certificate in `Cost.lean`. -/
theorem affine_prefixSum (s : Vector (Expression (F p)) m)
    (hs : Challenge.CostR1CS.AffineW s) :
    ∀ i, Challenge.CostR1CS.Affine (prefixSum s i) := by
  intro i
  induction i with
  | zero =>
    simp only [prefixSum]
    exact Challenge.CostR1CS.Affine.zero
  | succ n ih =>
    simp only [prefixSum]
    refine Challenge.CostR1CS.Affine.add ih ?_
    split
    · exact hs n ‹_›
    · exact Challenge.CostR1CS.Affine.zero

/-! ## The two proofs (standalone; never structure fields) -/

theorem soundness (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion.Soundness (F p) (main P) (Assumptions P.B) (Spec P.B) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  circuit_proof_start
  simp only [circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    Nat.mul_zero, Nat.add_zero, true_implies] at h_holds ⊢
  obtain ⟨h_bool, h_sum, h_gate, h_sel, h_range⟩ := h_holds
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  -- ℕ-indexed views of the constraint rows
  have h_bool' : ∀ (j : ℕ), j < m →
      env.get (i₀ + j) * (env.get (i₀ + j) + -1) = 0 :=
    fun j hj => h_bool ⟨j, hj⟩
  have h_gate' : ∀ (j : ℕ) (hj : j < m - 1),
      (Expression.eval env (input_var.rhs[j + 1]'(by omega))
        + -Expression.eval env (input_var.lhs[j + 1]'(by omega)))
      * Expression.eval env
          (prefixSum (Vector.mapRange m fun t => var { index := i₀ + t }) (j + 1)) = 0 :=
    fun j hj => h_gate ⟨j, hj⟩
  have h_sel' : ∀ (j : ℕ) (hj : j < m),
      env.get (i₀ + j) * (Expression.eval env (input_var.rhs[j]'hj)
        + -Expression.eval env (input_var.lhs[j]'hj) + -1 + -env.get (i₀ + m)) = 0 :=
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
  -- selector cells are boolean
  have hbool : ∀ j, j < m → env.get (i₀ + j) = 0 ∨ env.get (i₀ + j) = 1 := by
    intro j hj
    rcases mul_eq_zero.mp (h_bool' j hj) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (add_neg_eq_zero.mp h1)
  -- the selector cells sum to 1
  have hsum1 : (∑ j ∈ Finset.range m, env.get (i₀ + j)) = 1 := by
    rw [eval_prefixSum_get env i₀ m (le_refl m)] at h_sum
    linear_combination h_sum
  -- m < p, so the field sum determines the one-hot count
  have hmp : m < p := by
    have h1 : m + 1 ≤ 2 ^ (2 * B) * (m + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  obtain ⟨k, hkm, hk1, hk0⟩ :=
    onehot_core hmp (fun j => env.get (i₀ + j)) hbool hsum1
  have hk1' : env.get (i₀ + k) = 1 := hk1
  have hk0' : ∀ j, j < m → j ≠ k → env.get (i₀ + j) = 0 := hk0
  have hpre : ∀ i, i ≤ m →
      (∑ j ∈ Finset.range i, env.get (i₀ + j)) = if k < i then 1 else 0 :=
    onehot_prefix (fun j => env.get (i₀ + j)) k hk1 hk0 hkm
  -- limbs above the selected one agree
  have heqAbove : ∀ (i : ℕ) (hi : i < m), k < i →
      input.lhs[i]'hi = input.rhs[i]'hi := by
    intro i hi hki
    have hi1 : i - 1 < m - 1 := by omega
    have hg := h_gate' (i - 1) hi1
    simp only [show i - 1 + 1 = i from by omega] at hg
    rw [eval_prefixSum_get env i₀ i (by omega), hpre i (by omega), if_pos hki,
      ha_e i hi, hb_e i hi, mul_one] at hg
    linear_combination -hg
  -- the selected limb satisfies `lhs[k] + 1 + d = rhs[k]`
  have hselk := h_sel' k hkm
  rw [ha_e k hkm, hb_e k hkm, hk1', one_mul] at hselk
  have hd : (env.get (i₀ + m)).val < 2 ^ B := h_range
  have hPB1 : 2 ^ (B + 1) < p := by
    have h1 : 2 ^ (B + 1) ≤ 2 ^ (2 * B + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (2 * B + 2) = 2 ^ (2 * B) * 4 := by rw [pow_add]; ring
    have h3 : 2 ^ (2 * B) * 4 ≤ 2 ^ (2 * B) * (m + 1) * 4 := by
      have : 1 ≤ m + 1 := by omega
      nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hone : (1 : F p).val = 1 := ZMod.val_one p
  have hzero : (0 : F p).val = 0 := ZMod.val_zero
  have hsum_lt : (input.lhs[k]'hkm).val + (env.get (i₀ + m)).val
      + (1 : F p).val + (0 : F p).val < p := by
    rw [hone, hzero]
    have h1 : (input.lhs[k]'hkm).val < 2 ^ B := ha_norm ⟨k, hkm⟩
    have hpw : 2 ^ B + 2 ^ B = 2 ^ (B + 1) := by rw [pow_succ]; ring
    omega
  have hrhs_lt : (input.rhs[k]'hkm).val + (0 : F p).val * 2 ^ B < p := by
    rw [hzero]
    have h1 : (input.rhs[k]'hkm).val < 2 ^ B := hb_norm ⟨k, hkm⟩
    omega
  have heq0 : input.lhs[k]'hkm + env.get (i₀ + m) + 1 + 0
      - input.rhs[k]'hkm - 0 * (2 ^ B : F p) = 0 := by
    linear_combination -hselk
  have hlift := per_limb_lift (B := B) (input.lhs[k]'hkm) (env.get (i₀ + m)) 1 0
    (input.rhs[k]'hkm) 0 hB hsum_lt hrhs_lt heq0
  rw [hone, hzero] at hlift
  -- ℕ-indexed digit functions and the lexicographic core
  set An : ℕ → ℕ := fun j => if h : j < m then (input.lhs[j]'h).val else 0 with hAn
  set Bn : ℕ → ℕ := fun j => if h : j < m then (input.rhs[j]'h).val else 0 with hBn
  have hAn_lt : ∀ j, j < m → An j < 2 ^ B := by
    intro j hj
    simp only [hAn, dif_pos hj]
    exact ha_norm ⟨j, hj⟩
  have hBn_lt : ∀ j, j < m → Bn j < 2 ^ B := by
    intro j hj
    simp only [hBn, dif_pos hj]
    exact hb_norm ⟨j, hj⟩
  have hsel_nat : An k + 1 + (env.get (i₀ + m)).val = Bn k := by
    simp only [hAn, hBn, dif_pos hkm]
    omega
  have heqAbove_nat : ∀ i, k < i → i < m → An i = Bn i := by
    intro i hki hi
    simp only [hAn, hBn, dif_pos hi]
    rw [heqAbove i hi hki]
  have hcore := selector_sound_core m An Bn k (env.get (i₀ + m)).val hkm
    hAn_lt hBn_lt heqAbove_nat hsel_nat
  have hval_a : BigInt.value B input.lhs = ∑ j ∈ Finset.range m, An j * 2 ^ (B * j) := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => An j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
  have hval_b : BigInt.value B input.rhs = ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Bn j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
  rw [hval_a, hval_b]
  exact hcore

theorem completeness (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion.Completeness (F p) (main P) (Assumptions P.B) (Spec P.B) := by
  obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
  circuit_proof_start
  simp only [circuit_norm, RangeCheck.circuit, RangeCheck.Assumptions, RangeCheck.Spec,
    Nat.mul_zero, Nat.add_zero] at h_env ⊢
  obtain ⟨h_swit, h_dwit⟩ := h_env
  obtain ⟨ha_norm, hb_norm⟩ := h_assumptions
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
  -- ℕ-indexed digit functions and the most-significant differing limb
  set An : ℕ → ℕ := fun j => if h : j < m then (input.lhs[j]'h).val else 0 with hAn
  set Bn : ℕ → ℕ := fun j => if h : j < m then (input.rhs[j]'h).val else 0 with hBn
  have hAn_lt : ∀ j, j < m → An j < 2 ^ B := by
    intro j hj
    simp only [hAn, dif_pos hj]
    exact ha_norm ⟨j, hj⟩
  have hBn_lt : ∀ j, j < m → Bn j < 2 ^ B := by
    intro j hj
    simp only [hBn, dif_pos hj]
    exact hb_norm ⟨j, hj⟩
  have hval_a : BigInt.value B input.lhs = ∑ j ∈ Finset.range m, An j * 2 ^ (B * j) := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => An j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hAn, dif_pos i.isLt, Fin.getElem_fin]
  have hval_b : BigInt.value B input.rhs = ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
    rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range (fun j => Bn j * 2 ^ (B * j))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hBn, dif_pos i.isLt, Fin.getElem_fin]
  have hlt : (∑ j ∈ Finset.range m, An j * 2 ^ (B * j))
      < ∑ j ∈ Finset.range m, Bn j * 2 ^ (B * j) := by
    rw [← hval_a, ← hval_b]
    exact h_spec
  obtain ⟨k, hkm, hklt, hkeq⟩ := msd_exists m An Bn hAn_lt hBn_lt hlt
  have hklt' : (input.lhs[k]'hkm).val < (input.rhs[k]'hkm).val := by
    have h := hklt
    simpa only [hAn, hBn, dif_pos hkm] using h
  have hkeq' : ∀ (i : ℕ) (hi : i < m), k < i →
      input.lhs[i]'hi = input.rhs[i]'hi := by
    intro i hi hki
    have h := hkeq i hki hi
    simp only [hAn, hBn, dif_pos hi] at h
    exact FieldUtils.ext h
  -- the witness generator's most-significant-difference index is exactly `k`
  have hdiff : diffIdx env.toEnvironment input_var.lhs input_var.rhs = k := by
    unfold diffIdx
    apply findGreatest_eq_of_top hkm
    · simp only [dif_pos hkm]
      rw [ha_e k hkm, hb_e k hkm]
      intro hcontra
      rw [hcontra] at hklt'
      omega
    · intro j hkj hj
      simp only [dif_pos hj]
      rw [ha_e j hj, hb_e j hj]
      exact not_not_intro (hkeq' j hj hkj)
  -- selector cells are the one-hot indicator of `k`
  have hsv : ∀ (j : ℕ), j < m → env.get (i₀ + j) = if j = k then 1 else 0 := by
    intro j hj
    have h := h_swit ⟨j, hj⟩
    simp only [Vector.getElem_ofFn, hdiff] at h
    exact h
  -- the witnessed difference cell
  have hd0 : env.get (i₀ + m)
      = (((input.rhs[k]'hkm).val - 1 - (input.lhs[k]'hkm).val : ℕ) : F p) := by
    have h := h_dwit ⟨0, Nat.zero_lt_one⟩
    simp only [Vector.getElem_ofFn, hdiff, dif_pos hkm, ha_e k hkm, hb_e k hkm] at h
    exact h
  have hd0_lt : (input.rhs[k]'hkm).val - 1 - (input.lhs[k]'hkm).val < 2 ^ B := by
    have hBk : (input.rhs[k]'hkm).val < 2 ^ B := hb_norm ⟨k, hkm⟩
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- 1. booleanity of the selector cells
    intro i
    rw [hsv i.val i.isLt]
    by_cases hik : i.val = k
    · rw [if_pos hik]; ring
    · rw [if_neg hik]; ring
  · -- 2. the selector cells sum to 1
    rw [eval_prefixSum_get env.toEnvironment i₀ m (le_refl m)]
    rw [show (∑ j ∈ Finset.range m, env.get (i₀ + j))
        = ∑ j ∈ Finset.range m, if j = k then (1 : F p) else 0 from
      Finset.sum_congr rfl fun j hj => hsv j (Finset.mem_range.mp hj)]
    rw [Finset.sum_ite_eq' (Finset.range m) k (fun _ => (1 : F p)),
      if_pos (Finset.mem_range.mpr hkm)]
    ring
  · -- 3. gating rows: limbs above `k` agree
    intro i
    have hi1 : i.val + 1 < m := by omega
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
    · rw [if_pos hki, ha_e (i.val + 1) hi1, hb_e (i.val + 1) hi1,
        hkeq' (i.val + 1) hi1 (by omega)]
      ring
    · rw [if_neg hki]
      ring
  · -- 4. selection rows
    intro i
    by_cases hik : i.val = k
    · simp only [hik]
      rw [hsv k hkm, if_pos rfl, one_mul, ha_e k hkm, hb_e k hkm, hd0]
      have hnat : (input.lhs[k]'hkm).val + 1
          + ((input.rhs[k]'hkm).val - 1 - (input.lhs[k]'hkm).val)
          = (input.rhs[k]'hkm).val := by omega
      have hcast := congrArg (Nat.cast : ℕ → F p) hnat
      push_cast at hcast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hcast
      linear_combination -hcast
    · rw [hsv i.val i.isLt, if_neg hik]
      ring
  · -- 5. the difference cell is `B`-bit
    rw [hd0, ZMod.val_natCast_of_lt (lt_trans hd0_lt hB)]
    exact hd0_lt

/-- The `LessThanSel` formal assertion: two normalized big integers satisfy
`lhs.value B < rhs.value B`, via a one-hot most-significant-difference selector. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] :
    FormalAssertion (F p) (Inputs m) where
  main := main P
  Assumptions := Assumptions P.B
  Spec := Spec P.B
  soundness := soundness P
  completeness := completeness P

end LessThanSel

end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
