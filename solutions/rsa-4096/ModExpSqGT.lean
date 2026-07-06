import Solution.RSASSAPKCS1v15_SHA256_4096_65537.ModExpG
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.SquareModBalGT

/-!
# Power-of-two modular exponentiation over balanced residues

The RSA-specific square-only chain for the `2^14` middle squarings, reworked
for the balanced signed-digit residue representation: every chain link is a
`SquareModBalGT` battery (balanced input, balanced output), the verifier-side
invariant is the ℤ congruence `VZ(acc) ≡ VZ(base)^(2^i) (mod n)` together with
the balanced window checks, and the honest-prover invariant is that `acc`
encodes a canonical residue (`balShift ≤ acc.value < n + balShift`).
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace ModExpSqGT

/-- Evaluate a big-integer variable vector under `env`. -/
private abbrev ev (env : Environment (F p)) (x : Var (BigInt m) (F p)) : BigInt m (F p) :=
  Vector.map (Expression.eval env) x

/-- One balanced square's local length, matching `SquareModBalGT.elaborated`. -/
def squareModTLen (B W tb tw G : ℕ) (Wf : ℕ → ℕ) : ℕ :=
  m + m + ((m - 1) * (B - 1) + (tb - 1)) + ((m - 1) * (B - 1) + (tw - 1))
    + (2 * m - 1) + (2 * m - 2)
    + GroupedEqXV.widthAllocFrom Wf (G - 2) 0

/-- A chain of `k` balanced modular squarings. -/
def squareChain (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)] (n : Var (BigInt m) (F p)) :
    ℕ → Var (BigInt m) (F p) → Circuit (F p) (Var (BigInt m) (F p))
  | 0, acc => pure acc
  | k + 1, acc => do
      let sq ← subcircuitWithAssertion
        (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
        { a := acc, modulus := n }
      squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq

/-- Main circuit: compute `base^(2^k)` modulo `n` as `k` balanced squarings. -/
def main (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)] (k : ℕ) (input : Var (ModExpG.Inputs m) (F p)) :
    Circuit (F p) (Var (BigInt m) (F p)) :=
  squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf input.modulus k input.base

lemma squareChain_localLength (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)] (n : Var (BigInt m) (F p)) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).localLength offset
        = k * squareModTLen (m := m) P.B P.W tb tw G V.Wf := by
  intro k
  induction k with
  | zero =>
    intro acc offset
    simp [squareChain, circuit_norm]
  | succ k ih =>
    intro acc offset
    have hSL : ∀ x : Var (SquareModLazy.Inputs m) (F p),
        (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf).localLength x
          = squareModTLen (m := m) P.B P.W tb tw G V.Wf := fun _ => rfl
    simp only [squareChain, circuit_norm, ih, hSL, Nat.succ_eq_add_one]
    ring

lemma squareChain_subcircuitsConsistent (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR) [Fact (p > 2)]
    (n : Var (BigInt m) (F p)) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      ((squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).operations offset).SubcircuitsConsistent offset := by
  intro k
  induction k with
  | zero =>
    intro acc offset
    simp [squareChain, circuit_norm]
  | succ k ih =>
    intro acc offset
    simp only [squareChain, circuit_norm]
    ring_nf
    exact ih _ _

lemma squareChain_channelsLawful (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)]
    (n : Var (BigInt m) (F p)) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      ((squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).operations offset).ChannelsLawful [] [] := by
  have hsubSq : ∀ (x : Var (SquareModLazy.Inputs m) (F p)) (off : ℕ),
      (((subcircuitWithAssertion
        (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) x)).operations off).ChannelsLawful [] [] := by
    intro x off
    simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.elaborated]
  intro k
  induction k with
  | zero =>
    intro acc offset
    simp only [squareChain, Circuit.pure_operations_eq]
    exact Operations.channelsLawful_nil
  | succ k ih =>
    intro acc offset
    rw [show (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc)
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl]
    rw [Circuit.bind_operations_eq]
    exact Operations.channelsLawful_append_of_channelsLawful
      (hsubSq { a := acc, modulus := n } offset) (ih _ _)

instance elaborated (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)] (k : ℕ) :
    ElaboratedCircuit (F p) (ModExpG.Inputs m) (BigInt m)
      (main P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k) where
  localLength _ := k * squareModTLen (m := m) P.B P.W tb tw G V.Wf
  localLength_eq := by
    intro input offset
    unfold main
    exact squareChain_localLength P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf input.modulus k input.base offset
  output input offset :=
    (main P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k input).output offset
  output_eq := by
    intro input offset
    rfl
  subcircuitsConsistent := by
    intro input offset
    unfold main
    exact squareChain_subcircuitsConsistent P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf input.modulus k input.base offset
  channelsLawful := by
    intro input offset
    unfold main
    exact squareChain_channelsLawful P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf input.modulus k input.base offset

/-- Verifier-side assumptions: `base` is a balanced-window vector (packaged as
the value bound), and `n` has the usual 4096-bit modulus bounds. -/
def Assumptions (B tb tw : ℕ) (input : ModExpG.Inputs m (F p)) : Prop :=
  input.base.Normalized B ∧ input.modulus.Normalized B ∧
    input.base.value B < 2 ^ ((m - 1) * B + tw) ∧
    input.modulus.value B < 2 ^ ((m - 1) * B + tb) ∧
    0 < input.modulus.value B ∧
    2 ^ ((m - 1) * B + tb - 1) ≤ input.modulus.value B

def Spec (k B tw : ℕ) (input : ModExpG.Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  BigInt.NormalizedTight B tw out ∧
    BalancedZ.VZ B out ≡ BalancedZ.VZ B input.base ^ (2 ^ k)
      [ZMOD (input.modulus.value B : ℤ)]

def ProverAssumptions (B tb tw : ℕ) (input : ModExpG.Inputs m (F p)) : Prop :=
  Assumptions B tb tw input ∧
    BalancedZ.balShift B m ≤ input.base.value B ∧
    input.base.value B - BalancedZ.balShift B m < input.modulus.value B

def ProverSpec (B : ℕ) (input : ModExpG.Inputs m (F p)) (out : BigInt m (F p)) : Prop :=
  BalancedZ.balShift B m ≤ out.value B ∧
    out.value B - BalancedZ.balShift B m < input.modulus.value B

lemma squareChain_soundness (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)]
    (env : Environment (F p)) (Zb : ℤ) (n : Var (BigInt m) (F p))
    (hn_norm : (ev env n).Normalized P.B)
    (hn_ltT : (ev env n).value P.B < 2 ^ ((m - 1) * P.B + tb))
    (hn_pos : 0 < (ev env n).value P.B)
    (hn_ge : 2 ^ ((m - 1) * P.B + tb - 1) ≤ (ev env n).value P.B) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F p)) (offset E : ℕ),
      (ev env acc).Normalized P.B →
      (ev env acc).value P.B < 2 ^ ((m - 1) * P.B + tw) →
      BalancedZ.VZ P.B (ev env acc) ≡ Zb ^ E [ZMOD ((ev env n).value P.B : ℤ)] →
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env e = 0, lookup := fun l ↦ l.Soundness env,
          interact := fun i ↦ i.Guarantees env, subcircuit := fun {_m} s ↦ s.Assumptions env → s.Spec env }
        ((squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).operations offset) →
      (ev env (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1).Normalized P.B ∧
      (ev env (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1).value P.B
        < 2 ^ ((m - 1) * P.B + tw) ∧
      BalancedZ.VZ P.B (ev env (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1)
        ≡ Zb ^ (E * 2 ^ k) [ZMOD ((ev env n).value P.B : ℤ)] := by
  intro k
  induction k with
  | zero =>
    intro acc offset E hacc_norm hacc_lt hacc_val _
    simp only [squareChain, pow_zero, Nat.mul_one]
    exact ⟨hacc_norm, hacc_lt, hacc_val⟩
  | succ k ih =>
    intro acc offset E hacc_norm hacc_lt hacc_val h_holds
    rw [show squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl] at h_holds ⊢
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append] at h_holds
    obtain ⟨h_sq_holds, h_rest_holds⟩ := h_holds
    have hsq_as : SquareModBalGT.SoundAssumptions P.B tb tw ({ a := ev env acc, modulus := ev env n } :
        SquareModLazy.Inputs m (F p)) :=
      ⟨hacc_norm, hn_norm, hacc_lt, hn_ltT, hn_pos, hn_ge⟩
    simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.SoundAssumptions,
      SquareModBalGT.Spec] at h_sq_holds
    obtain ⟨hsq_tight, hsq_val⟩ := h_sq_holds hsq_as
    set sq : Var (BigInt m) (F p) := Vector.mapRange m fun i ↦ var { index := offset + m + i } with hsq_def
    have hsq_norm : (ev env sq).Normalized P.B := hsq_tight.1
    have hsq_ltT : (ev env sq).value P.B < 2 ^ ((m - 1) * P.B + tw) :=
      BigInt.value_lt_tight htwB hsq_tight
    have hsq_pow : BalancedZ.VZ P.B (ev env sq) ≡ Zb ^ (2 * E) [ZMOD ((ev env n).value P.B : ℤ)] := by
      refine Int.ModEq.trans hsq_val ?_
      have h1 : BalancedZ.VZ P.B (ev env acc) * BalancedZ.VZ P.B (ev env acc)
          ≡ Zb ^ E * Zb ^ E [ZMOD ((ev env n).value P.B : ℤ)] :=
        Int.ModEq.mul hacc_val hacc_val
      refine Int.ModEq.trans h1 ?_
      rw [← pow_add, two_mul]
    simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.elaborated] at h_rest_holds ⊢
    obtain ⟨h1, h2, h3⟩ := ih sq _ (2 * E) hsq_norm hsq_ltT hsq_pow h_rest_holds
    refine ⟨h1, h2, ?_⟩
    rw [show E * 2 ^ (k + 1) = 2 * E * 2 ^ k from by rw [pow_succ]; ring]
    exact h3

lemma squareChain_requirements (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)]
    (env : Environment (F p)) (n : Var (BigInt m) (F p)) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      Operations.forAllNoOffset
        { interact := fun i ↦ i.Requirements env,
          subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
        ((squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).operations offset) := by
  have hsubSq : ∀ (x : Var (SquareModLazy.Inputs m) (F p)) (off : ℕ),
      Operations.forAllNoOffset
        { interact := fun i ↦ i.Requirements env,
          subcircuit := fun {_m} s ↦ s.channelsWithRequirements = [] ∨ s.Assumptions env }
        ((subcircuitWithAssertion
          (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf) x).operations off) := by
    intro x off
    simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.elaborated]
  intro k
  induction k with
  | zero =>
    intro acc offset
    simp only [squareChain, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | succ k ih =>
    intro acc offset
    rw [show squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl]
    rw [Circuit.bind_operations_eq, Operations.forAllNoOffset_append]
    exact ⟨hsubSq { a := acc, modulus := n } offset, ih _ _⟩

lemma squareChain_completeness (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)]
    (env : ProverEnvironment (F p)) (n : Var (BigInt m) (F p))
    (hn_norm : (ev env.toEnvironment n).Normalized P.B)
    (hn_ltT : (ev env.toEnvironment n).value P.B < 2 ^ ((m - 1) * P.B + tb))
    (hn_pos : 0 < (ev env.toEnvironment n).value P.B)
    (hn_ge : 2 ^ ((m - 1) * P.B + tb - 1) ≤ (ev env.toEnvironment n).value P.B) :
    ∀ (k : ℕ) (acc : Var (BigInt m) (F p)) (offset : ℕ),
      (ev env.toEnvironment acc).Normalized P.B →
      (ev env.toEnvironment acc).value P.B < 2 ^ ((m - 1) * P.B + tw) →
      BalancedZ.balShift P.B m ≤ (ev env.toEnvironment acc).value P.B →
      (ev env.toEnvironment acc).value P.B - BalancedZ.balShift P.B m
        < (ev env.toEnvironment n).value P.B →
      env.UsesLocalWitnessesCompleteness offset
        ((squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).operations offset) →
      Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env.toEnvironment e = 0,
          lookup := fun l ↦ l.Completeness env.toEnvironment,
          interact := fun i ↦ i.Guarantees env.toEnvironment, subcircuit := fun {_m} s ↦ s.ProverAssumptions env }
        ((squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc).operations offset) ∧
      (ev env.toEnvironment (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1).Normalized P.B ∧
      (ev env.toEnvironment (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1).value P.B
        < 2 ^ ((m - 1) * P.B + tw) ∧
      BalancedZ.balShift P.B m
        ≤ (ev env.toEnvironment (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1).value P.B ∧
      (ev env.toEnvironment (squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k acc offset).1).value P.B
          - BalancedZ.balShift P.B m
        < (ev env.toEnvironment n).value P.B := by
  intro k
  induction k with
  | zero =>
    intro acc offset hacc_norm hacc_ltT hacc_ge hacc_ltN _
    refine ⟨?_, hacc_norm, hacc_ltT, hacc_ge, hacc_ltN⟩
    simp only [squareChain, Circuit.pure_operations_eq, Operations.forAllNoOffset_empty]
  | succ k ih =>
    intro acc offset hacc_norm hacc_ltT hacc_ge hacc_ltN h_env
    rw [show squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n (k + 1) acc
        = (do
            let sq ← subcircuitWithAssertion
              (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
              { a := acc, modulus := n }
            squareChain P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf n k sq) from rfl] at h_env ⊢
    rw [Circuit.bind_operations_eq] at h_env ⊢
    rw [Operations.forAllNoOffset_append]
    rw [Circuit.ConstraintsHold.append_localWitnesses] at h_env
    obtain ⟨h_sq_env, h_rest_env⟩ := h_env
    have hsq_pa : SquareModBalGT.Assumptions P.B tb tw ({ a := ev env.toEnvironment acc, modulus := ev env.toEnvironment n } :
        SquareModLazy.Inputs m (F p)) :=
      ⟨⟨hacc_norm, hn_norm, hacc_ltT, hn_ltT, hn_pos, hn_ge⟩, hacc_ge, hacc_ltN⟩
    have hsq_sound_as : SquareModBalGT.SoundAssumptions P.B tb tw
        ({ a := ev env.toEnvironment acc, modulus := ev env.toEnvironment n } :
          SquareModLazy.Inputs m (F p)) :=
      ⟨hacc_norm, hn_norm, hacc_ltT, hn_ltT, hn_pos, hn_ge⟩
    simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.Assumptions,
      SquareModBalGT.SoundAssumptions, SquareModBalGT.ProverSpec, SquareModBalGT.Spec] at h_sq_env
    obtain ⟨h_sq_spec, hsq_ge, hsq_ltN⟩ := h_sq_env hsq_pa
    obtain ⟨hsq_tight, _hsq_val⟩ := h_sq_spec hsq_sound_as
    set sq : Var (BigInt m) (F p) := Vector.mapRange m fun i ↦ var { index := offset + m + i } with hsq_def
    have hsq_norm : (ev env.toEnvironment sq).Normalized P.B := hsq_tight.1
    have hsq_ltT : (ev env.toEnvironment sq).value P.B < 2 ^ ((m - 1) * P.B + tw) :=
      BigInt.value_lt_tight htwB hsq_tight
    have hsq_pa_ops : Operations.forAllNoOffset
        { assert := fun e ↦ Expression.eval env.toEnvironment e = 0,
          lookup := fun l ↦ l.Completeness env.toEnvironment,
          interact := fun i ↦ i.Guarantees env.toEnvironment, subcircuit := fun {_m} s ↦ s.ProverAssumptions env }
        ((subcircuitWithAssertion
          (SquareModBalGT.generalCircuit P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf)
          { a := acc, modulus := n }).operations offset) := by
      simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.Assumptions,
        SquareModBalGT.SoundAssumptions]
      exact hsq_pa
    simp only [circuit_norm, SquareModBalGT.generalCircuit, SquareModBalGT.elaborated] at hsq_pa_ops h_rest_env hsq_ge hsq_ltN ⊢
    rw [Nat.add_comm] at h_rest_env
    obtain ⟨h_rest_pa, h_rest_norm, h_rest_ltT, h_rest_ge, h_rest_ltN⟩ :=
      ih sq _ hsq_norm hsq_ltT hsq_ge hsq_ltN h_rest_env
    exact ⟨⟨hsq_pa_ops, h_rest_pa⟩, h_rest_norm, h_rest_ltT, h_rest_ge, h_rest_ltN⟩

set_option maxHeartbeats 8000000 in
def generalCircuit (P : BigIntParams p m) (tb tw : ℕ)
    (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htw : 1 ≤ tw ∧ 2 ^ tw < p)
    (htbB : tb + 1 ≤ P.B) (htwB : tw ≤ P.B) (htbw : tb < tw)
    (gf posOf : ℕ → ℕ) (G : ℕ) (V VR : GroupedEqV.VParams)
    (hgv : GroupedEqD.GVDHyps p (2 * m - 1) P.B gf posOf G V VR)
    (hNf : SquareModBalGT.NfOkD (m := m) P.B tb tw V VR)
    [Fact (p > 2)] (k : ℕ) :
    GeneralFormalCircuit (F p) (ModExpG.Inputs m) (BigInt m) where
  main := main P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf k
  Assumptions := fun input _ => Assumptions P.B tb tw input
  Spec := fun input out _ => Spec k P.B tw input out
  ProverAssumptions := fun input _ _ => ProverAssumptions P.B tb tw input
  ProverSpec := fun input out _ => ProverSpec P.B input out
  soundness := by
    circuit_proof_start
    obtain ⟨hbase_norm, hn_norm, hbase_ltT, hn_ltT, hn_pos, hn_ge⟩ := h_assumptions
    rw [← h_input] at hbase_norm hn_norm hbase_ltT hn_ltT hn_pos hn_ge ⊢
    simp only [Assumptions, Spec, ModExpG.Assumptions] at hbase_norm hn_norm hbase_ltT hn_ltT hn_pos hn_ge ⊢
    have hbase_val : BalancedZ.VZ P.B (ev env input_var.base)
        ≡ BalancedZ.VZ P.B (ev env input_var.base) ^ 1
          [ZMOD ((ev env input_var.modulus).value P.B : ℤ)] := by
      rw [pow_one]
    refine ⟨?_, squareChain_requirements P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf env input_var.modulus k input_var.base i₀⟩
    obtain ⟨hout_norm, hout_ltT, hout_val⟩ :=
      squareChain_soundness P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf env
        (BalancedZ.VZ P.B (ev env input_var.base)) input_var.modulus
        hn_norm hn_ltT hn_pos hn_ge k _ i₀ 1 hbase_norm hbase_ltT hbase_val h_holds
    refine ⟨⟨hout_norm, ?_⟩, ?_⟩
    · exact GroupedEqV.top_limb_lt_of_value_lt hout_ltT
    · rw [Nat.one_mul] at hout_val
      exact hout_val
  completeness := by
    circuit_proof_start
    obtain ⟨⟨hbase_norm, hn_norm, hbase_ltT, hn_ltT, hn_pos, hn_ge⟩, hbase_ge, hbase_ltN⟩ := h_assumptions
    rw [← h_input] at hbase_norm hn_norm hbase_ltT hn_ltT hn_pos hn_ge hbase_ge hbase_ltN
    simp only [Assumptions, ProverAssumptions, ModExpG.Assumptions] at hbase_norm hn_norm hbase_ltT hn_ltT hn_pos hn_ge hbase_ge hbase_ltN
    have hmapn : ev env.toEnvironment input_var.modulus = input.modulus := by
      simpa only [ev] using congrArg ModExpG.Inputs.modulus h_input
    obtain ⟨h_ops, _h_norm, _h_ltT, h_ge, h_ltN⟩ :=
      squareChain_completeness P tb tw htb htw htbB htwB htbw gf posOf G V VR hgv hNf env input_var.modulus
        hn_norm hn_ltT hn_pos hn_ge k input_var.base i₀ hbase_norm hbase_ltT hbase_ge hbase_ltN h_env
    exact ⟨h_ops, by simpa only [ProverSpec, ev, hmapn] using h_ge,
      by simpa only [ProverSpec, ev, hmapn] using h_ltN⟩

end ModExpSqGT
end

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
