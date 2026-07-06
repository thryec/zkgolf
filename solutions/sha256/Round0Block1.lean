import Solution.SHA256.SHA256Round
import Solution.SHA256.SHA256RoundsTheorems
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# SHA-256 Block-1 Round 0 (constant-folded, single-constant adders)

Ported from bufferhe4d's 166,679 submission
(`/Users/simon/Documents/dev/Projects/zk.golf/solutions/sha-bufferhe4d-166679/Round0Block1.lean`),
credit to bufferhe4d for the block-1 round-0 IV constant fold.

Block 1's compression starts from the constant IV `H0`, so in round 0 every state
word is a compile-time constant. The four bit gadgets `Σ₁(H0[4])`, `Ch(H0[4..6])`,
`Σ₀(H0[0])`, `Maj(H0[0..2])` evaluate to constant 32-bit words. Moreover, since
`x % 2^32` folds over constant addends, **all** the constant addends of each fused
adder collapse into a single 32-bit constant word:

  new_e = w + eC                    (mod 2^32),
    eC = (H0[3] + H0[7] + Σ₁(H0[4]) + Ch(H0[4..6]) + K[0])         mod 2^32
  new_a = new_e + aC                (mod 2^32),
    aC = (Σ₀(H0[0]) + Maj(H0[0..2]) + ¬H0[3] + 1)                  mod 2^32

so each adder is a plain two-input `Add32` (32 witnesses, 33 rows) instead of a
multi-word `AddMany` — `(64, 66)` for the whole round versus the previous
`(67, 69)`, on top of the four peeled `(32,32)` bit gadgets.
-/

namespace Round0Block1

/-! ## Constant literals and their bridges to the spec values -/

def h0_0 : ℕ := 0x6a09e667
def h0_1 : ℕ := 0xbb67ae85
def h0_2 : ℕ := 0x3c6ef372
def h0_3 : ℕ := 0xa54ff53a
def h0_4 : ℕ := 0x510e527f
def h0_5 : ℕ := 0x9b05688c
def h0_6 : ℕ := 0x1f83d9ab
def h0_7 : ℕ := 0x5be0cd19
def sig1C : ℕ := 0x3587272b
def chC   : ℕ := 0x1f85c98c
def sig0C : ℕ := 0xce20b47e
def majC  : ℕ := 0x3a6fe667
def k0C   : ℕ := 0x428a2f98

/-- The folded round-0 `new_e` constant:
`(h0_3 + h0_7 + sig1C + chC + k0C) % 2^32`. -/
def eC : ℕ := 0x98c7e2a2
/-- The folded round-0 `new_a` constant:
`(sig0C + majC + (2^32 - 1 - h0_3) + 1) % 2^32`. -/
def aC : ℕ := 0x6340a5ab

lemma h0_0_eq : h0_0 = Specs.SHA256.H0[0] := by decide
lemma h0_1_eq : h0_1 = Specs.SHA256.H0[1] := by decide
lemma h0_2_eq : h0_2 = Specs.SHA256.H0[2] := by decide
lemma h0_3_eq : h0_3 = Specs.SHA256.H0[3] := by decide
lemma h0_4_eq : h0_4 = Specs.SHA256.H0[4] := by decide
lemma h0_5_eq : h0_5 = Specs.SHA256.H0[5] := by decide
lemma h0_6_eq : h0_6 = Specs.SHA256.H0[6] := by decide
lemma h0_7_eq : h0_7 = Specs.SHA256.H0[7] := by decide
lemma sig1C_eq : sig1C = Specs.SHA256.upperSigma1 Specs.SHA256.H0[4] := by decide
lemma chC_eq : chC = Specs.SHA256.Ch Specs.SHA256.H0[4] Specs.SHA256.H0[5] Specs.SHA256.H0[6] := by decide
lemma sig0C_eq : sig0C = Specs.SHA256.upperSigma0 Specs.SHA256.H0[0] := by decide
lemma majC_eq : majC = Specs.SHA256.Maj Specs.SHA256.H0[0] Specs.SHA256.H0[1] Specs.SHA256.H0[2] := by decide
lemma k0C_eq : k0C = (Specs.SHA256.K[0]).toNat := by decide

lemma h0_0_lt : h0_0 < 2^32 := by norm_num [h0_0]
lemma h0_1_lt : h0_1 < 2^32 := by norm_num [h0_1]
lemma h0_2_lt : h0_2 < 2^32 := by norm_num [h0_2]
lemma h0_3_lt : h0_3 < 2^32 := by norm_num [h0_3]
lemma h0_4_lt : h0_4 < 2^32 := by norm_num [h0_4]
lemma h0_5_lt : h0_5 < 2^32 := by norm_num [h0_5]
lemma h0_6_lt : h0_6 < 2^32 := by norm_num [h0_6]
lemma h0_7_lt : h0_7 < 2^32 := by norm_num [h0_7]
lemma sig1C_lt : sig1C < 2^32 := by norm_num [sig1C]
lemma chC_lt : chC < 2^32 := by norm_num [chC]
lemma sig0C_lt : sig0C < 2^32 := by norm_num [sig0C]
lemma majC_lt : majC < 2^32 := by norm_num [majC]
lemma k0C_lt : k0C < 2^32 := by norm_num [k0C]
lemma eC_lt : eC < 2^32 := by norm_num [eC]
lemma aC_lt : aC < 2^32 := by norm_num [aC]

/-- `w + eC (mod 2^32)` equals the spec-shaped nested round-0 `new_e` sum. -/
lemma mod_eC (wv : ℕ) :
    (wv + eC) % 2^32 =
      _root_.add32 (Specs.SHA256.H0[3])
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[7])
            (Specs.SHA256.upperSigma1 (Specs.SHA256.H0[4])))
            (Specs.SHA256.Ch (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5]) (Specs.SHA256.H0[6])))
            ((Specs.SHA256.K[0]).toNat)) wv) := by
  rw [← sig1C_eq, ← chC_eq, ← h0_3_eq, ← h0_7_eq, ← k0C_eq]
  simp only [eC, h0_3, h0_7, sig1C, chC, k0C]
  unfold _root_.add32
  omega

/-- `new_e + aC (mod 2^32)` equals the spec-shaped nested round-0 `new_a` sum
(with `new_e = (wv + eC) % 2^32`). -/
lemma mod_aC (wv : ℕ) :
    ((wv + eC) % 2^32 + aC) % 2^32 =
      _root_.add32
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[7])
            (Specs.SHA256.upperSigma1 (Specs.SHA256.H0[4])))
            (Specs.SHA256.Ch (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5]) (Specs.SHA256.H0[6])))
            ((Specs.SHA256.K[0]).toNat)) wv)
        (_root_.add32 (Specs.SHA256.upperSigma0 (Specs.SHA256.H0[0]))
            (Specs.SHA256.Maj (Specs.SHA256.H0[0]) (Specs.SHA256.H0[1]) (Specs.SHA256.H0[2]))) := by
  rw [← sig1C_eq, ← chC_eq, ← sig0C_eq, ← majC_eq, ← h0_7_eq, ← k0C_eq]
  simp only [eC, aC, h0_7, sig1C, chC, sig0C, majC, k0C]
  unfold _root_.add32
  omega

/-! ## The circuit -/

/-- Constant-folded round 0 for block 1 (state = `H0`, only `w` variable):
two plain `Add32`s against the folded constants `eC`, `aC`. -/
def main (w : Var (fields 32) (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let new_e ← Add32.circuit ⟨w, constWord32 eC⟩
  let new_a ← Add32.circuit ⟨new_e, constWord32 aC⟩
  return #v[new_a, constWord32 h0_0, constWord32 h0_1, constWord32 h0_2, new_e,
            constWord32 h0_4, constWord32 h0_5, constWord32 h0_6]

def Assumptions (w : fields 32 (F p)) : Prop := Normalized w

def Spec (w : fields 32 (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round Specs.SHA256.H0 (Specs.SHA256.K[0]).toNat (valueBits w)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated : ElaboratedCircuit (F p) (fields 32) SHA256State main := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨c_newe, c_newa⟩ := h_holds
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have s_newe := c_newe ⟨h_assumptions, SHA256Rounds.normalized_constWord32 env _⟩
  have s_newa := c_newa ⟨s_newe.2, SHA256Rounds.normalized_constWord32 env _⟩
  clear c_newe c_newa
  -- valueBits of new_e in `add32`-nested spec shape
  have v_newe : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + i })) =
      _root_.add32 (Specs.SHA256.H0[3])
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[7])
            (Specs.SHA256.upperSigma1 (Specs.SHA256.H0[4])))
            (Specs.SHA256.Ch (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5]) (Specs.SHA256.H0[6])))
            ((Specs.SHA256.K[0]).toNat)) (valueBits input)) := by
    rw [s_newe.1, SHA256Rounds.valueBits_constWord32_of_lt env eC_lt]
    exact mod_eC _
  -- valueBits of new_a in `add32`-nested spec shape
  have v_newa : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + i })) =
      _root_.add32
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (Specs.SHA256.H0[7])
            (Specs.SHA256.upperSigma1 (Specs.SHA256.H0[4])))
            (Specs.SHA256.Ch (Specs.SHA256.H0[4]) (Specs.SHA256.H0[5]) (Specs.SHA256.H0[6])))
            ((Specs.SHA256.K[0]).toNat)) (valueBits input))
        (_root_.add32 (Specs.SHA256.upperSigma0 (Specs.SHA256.H0[0]))
            (Specs.SHA256.Maj (Specs.SHA256.H0[0]) (Specs.SHA256.H0[1]) (Specs.SHA256.H0[2]))) := by
    rw [s_newa.1, s_newe.1, SHA256Rounds.valueBits_constWord32_of_lt env eC_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env aC_lt]
    exact mod_aC _
  refine ⟨?_, ?_⟩
  · simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, circuit_norm]
    simp only [Specs.SHA256.sha256Round, Vector.getElem_map]
    rw [v_newa, v_newe,
      SHA256Rounds.valueBits_constWord32_of_lt env h0_0_lt, SHA256Rounds.valueBits_constWord32_of_lt env h0_1_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env h0_2_lt, SHA256Rounds.valueBits_constWord32_of_lt env h0_4_lt,
      SHA256Rounds.valueBits_constWord32_of_lt env h0_5_lt, SHA256Rounds.valueBits_constWord32_of_lt env h0_6_lt,
      h0_0_eq, h0_1_eq, h0_2_eq, h0_4_eq, h0_5_eq, h0_6_eq]
  · intro i
    fin_cases i <;>
      (rw [red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newa.2
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact s_newe.2
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact SHA256Rounds.normalized_constWord32 env _
    · exact SHA256Rounds.normalized_constWord32 env _

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main, Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨e_newe, -⟩ := h_env
  have s_newe := e_newe ⟨h_assumptions, SHA256Rounds.normalized_constWord32 _ _⟩
  exact ⟨⟨h_assumptions, SHA256Rounds.normalized_constWord32 _ _⟩,
         ⟨s_newe.2, SHA256Rounds.normalized_constWord32 _ _⟩⟩

def circuit : FormalCircuit (F p) (fields 32) SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Round0Block1
end Solution.SHA256
end
