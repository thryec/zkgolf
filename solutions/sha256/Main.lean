import Challenge.Instances.SHA256.Interface
import Solution.SHA256.Cost
import Solution.SHA256.CompressBlock1
import Solution.SHA256.CompressBlockWide
import Solution.SHA256.CompressBlock5
import Solution.SHA256.CheckPad
import Solution.SHA256.SelectDigest
import Solution.SHA256.PaddingTheorems
import Solution.SHA256.MainTheorems
import Challenge.Utils.CostR1CS

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface

section

def main (input : Var Input (F circomPrime)) : Circuit (F circomPrime) (Var Output (F circomPrime)) := do
  let padded ← witnessVector paddedBitsLen (paddedBitsWitness input)
  let lenFlags ← witnessVector inputBufferLen (lenFlagsWitness input)
  CheckPad.circuit ⟨input.messageLen, input.message, lenFlags, padded⟩
  let state1 ← CompressBlock1.circuit (paddedBlock padded 0)
  let state2 ← CompressBlockWide.circuit ⟨state1, paddedBlock padded 1⟩
  let state3 ← CompressBlockWide.circuit ⟨state2, paddedBlock padded 2⟩
  let state4 ← CompressBlockWide.circuit ⟨state3, paddedBlock padded 3⟩
  let state5 ← CompressBlock5.circuit ⟨input.messageLen, lenFlags, state4⟩
  let digest ← SelectDigest.circuit ⟨input.messageLen, lenFlags, state1, state2, state3, state4, state5⟩
  return { digest }

instance elaborated : ElaboratedCircuit (F circomPrime) Input Output main := by
  elaborate_circuit

/-! Cheap `rfl` projections that expose the compress blocks' `Assumptions`/`Spec`
without unfolding their (now fused) `main`, so `soundness` can keep them out of
the `circuit_proof_start` bracket. -/

private lemma cb1_Assumptions_eq :
    (CompressBlock1.circuit (p := circomPrime)).Assumptions = CompressBlock1.Assumptions := rfl

private lemma cb1_Spec_eq :
    (CompressBlock1.circuit (p := circomPrime)).Spec = CompressBlock1.Spec := rfl

private lemma cbw_Assumptions_eq :
    (CompressBlockWide.circuit (p := circomPrime)).Assumptions = CompressBlockWide.Assumptions := rfl

private lemma cbw_Spec_eq :
    (CompressBlockWide.circuit (p := circomPrime)).Spec = CompressBlockWide.Spec := rfl

private lemma cb5_Assumptions_eq :
    (CompressBlock5.circuit (p := circomPrime)).Assumptions = CompressBlock5.Assumptions := rfl

private lemma cb5_Spec_eq :
    (CompressBlock5.circuit (p := circomPrime)).Spec = CompressBlock5.Spec := rfl

private lemma cb5_localLength_eq (b : Var CompressBlock5.Inputs (F circomPrime)) :
    (CompressBlock5.circuit (p := circomPrime)).localLength b = 10751 := rfl

private lemma cb1_localLength_eq (b : Var SHA256Block (F circomPrime)) :
    (CompressBlock1.circuit (p := circomPrime)).localLength b = 14922 := rfl

private lemma cbw_localLength_eq (b : Var CompressBlockWide.Inputs (F circomPrime)) :
    (CompressBlockWide.circuit (p := circomPrime)).localLength b = 15056 := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem soundness :
    GeneralFormalCircuit.Soundness (F circomPrime) main
      Assumptions Spec := by
  -- Keep the compress blocks out of the `circuit_proof_start` bracket: unfolding
  -- their circuits reaches the fused `SHA256Rounds.circuit`, which whnf-times-out.
  -- Their `Spec`/`Assumptions` are exposed by the cheap `rfl` projections below.
  circuit_proof_start [CheckPad.circuit, CheckPad.Spec, CheckPad.Assumptions,
    SelectDigest.circuit, SelectDigest.Spec, SelectDigest.Assumptions]
  obtain ⟨h_cp, h_c1, h_c2, h_c3, h_c4, h_c5, h_sd⟩ := h_holds
  rw [cb1_Assumptions_eq, cb1_Spec_eq] at h_c1
  rw [cbw_Assumptions_eq, cbw_Spec_eq] at h_c2 h_c3 h_c4
  rw [cb5_Assumptions_eq, cb5_Spec_eq] at h_c5
  simp only [CompressBlock1.Assumptions, CompressBlock1.Spec] at h_c1
  simp only [CompressBlockWide.Assumptions, CompressBlockWide.Spec] at h_c2 h_c3 h_c4
  simp only [CompressBlock5.Assumptions, CompressBlock5.Spec] at h_c5
  obtain ⟨h_msg_assum, h_len_assum⟩ := h_assumptions
  obtain ⟨h_msg_eq, h_msgLen_eq⟩ := h_input
  -- abbreviations
  set msg := Vector.map ZMod.val input_message with hmsg
  set ℓ := ZMod.val input_messageLen with hℓ
  set pvar : Var SHA256PaddedBits (F circomPrime) :=
    Vector.mapRange paddedBitsLen fun i => var { index := i₀ + i } with hpvar
  -- CheckPad antecedent: message bytes < 256
  have h_cp_assum : ∀ i : Fin inputBufferLen, ZMod.val input_message[i.val] < 256 := by
    intro i
    have := h_msg_assum i
    simpa [fieldElemsToNat, Vector.getElem_map] using this
  obtain ⟨h_len_lt, h_onehot, h_bool, h_byte_eq⟩ := h_cp h_cp_assum
  -- bridge h_byte_eq to (Vector.map (Expression.eval env) pvar)
  have h_byte_eq' : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env) pvar) j = specPaddedByte msg ℓ j.val := by
    intro j
    have := h_byte_eq j
    rw [hmsg, hℓ]
    convert this using 2
  -- bridge h_bool to booleanity of (Vector.map (Expression.eval env) pvar)
  have h_bool' : ∀ i : Fin paddedBitsLen,
      IsBool (Vector.map (Expression.eval env) pvar)[i] := by
    intro i
    have := h_bool i
    rw [hpvar, Fin.getElem_fin, Vector.getElem_map, Vector.getElem_mapRange]
    simpa [Expression.eval] using this
  -- per-block value and normalization
  have block_val : ∀ b : Fin witnessedBlocksLen,
      Vector.map valueBits (eval env (paddedBlock pvar b)) = specBlock msg ℓ b.val := by
    intro b; exact paddedBlock_value env pvar msg ℓ h_byte_eq' b
  -- chain block 1 (state = constant IV H0, folded into CompressBlock1)
  obtain ⟨st1_val, st1_norm⟩ := h_c1
    (by intro i
        rw [Fin.getElem_fin]
        have h := paddedBlock_normalized env pvar h_bool' 0 i.val i.isLt
        rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 0) i.val i.isLt])
  rw [block_val 0] at st1_val
  -- chain block 2
  obtain ⟨st2_val, st2_norm⟩ := h_c2
    ⟨st1_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env pvar h_bool' 1 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 1) i.val i.isLt])⟩
  rw [st1_val, block_val 1] at st2_val
  -- chain block 3
  obtain ⟨st3_val, st3_norm⟩ := h_c3
    ⟨st2_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env pvar h_bool' 2 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 2) i.val i.isLt])⟩
  rw [st2_val, block_val 2] at st3_val
  -- chain block 4
  obtain ⟨st4_val, st4_norm⟩ := h_c4
    ⟨st3_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env pvar h_bool' 3 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env (paddedBlock pvar 3) i.val i.isLt])⟩
  rw [st3_val, block_val 3] at st4_val
  -- chain block 5
  obtain ⟨st5_val, st5_norm⟩ := h_c5 ⟨h_len_lt, h_onehot, st4_norm⟩
  rw [st4_val, block5SpecBlock_eq_specBlock msg (le_of_lt h_len_assum)] at st5_val
  -- digest via SelectDigest spec
  have h_sd_spec := h_sd ⟨h_len_lt, h_onehot, by
    intro k i
    -- statesVec[k][i] is one of st1..st5, all normalized
    fin_cases k
    · exact st1_norm i
    · exact st2_norm i
    · exact st3_norm i
    · exact st4_norm i
    · exact st5_norm i⟩
  -- Align the digest output and subcircuit offsets with the goal's reduced form.
  simp only [circuit_norm, SelectDigest.circuit_output_eq, cb1_localLength_eq, cbw_localLength_eq,
    cb5_localLength_eq] at h_sd_spec
  -- The goal is the trusted spec conjoined with the (out-of-bracket) compress
  -- blocks' channel-requirement disjuncts, all of which are `[]`.
  rw [Specs.SHA256.Spec, dif_pos (le_of_lt h_len_assum)]
  extract_lets truncated
  refine ⟨?_, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  apply Vector.ext
  intro w hw
  simp only [fieldElemsToNat, Vector.getElem_map]
  rw [Vector.getElem_mapRange]
  simp only [Expression.eval]
  rw [h_sd_spec ⟨w, hw⟩]
  refine digest_final _ msg ℓ (le_of_lt h_len_assum) (fun k => ?_) ⟨w, hw⟩ hw
  fin_cases k
  · exact st1_val
  · exact st2_val
  · exact st3_val
  · exact st4_val
  · exact st5_val

theorem completeness :
    GeneralFormalCircuit.Completeness (F circomPrime) main
      ProverAssumptions ProverSpec := by
  circuit_proof_start
  obtain ⟨h_pad_env, h_flags_env, h_c1, h_c2, h_c3, h_c4, h_c5, _h_sd⟩ := h_env
  obtain ⟨⟨h_msg_assum, h_len_assum⟩, _h_pad_zeros⟩ := h_assumptions
  obtain ⟨h_msg_eq, h_msgLen_eq⟩ := h_input
  set msg := Vector.map ZMod.val input_message with hmsg
  set ℓ := ZMod.val input_messageLen with hℓ
  set pvar : Var SHA256PaddedBits (F circomPrime) :=
    Vector.mapRange paddedBitsLen fun i => var { index := i₀ + i } with hpvar
  set fvar : Var (fields inputBufferLen) (F circomPrime) :=
    Vector.mapRange inputBufferLen fun i => var { index := i₀ + paddedBitsLen + i } with hfvar
  have hb : eval env input_var_message = input_message := by
    rw [CircuitType.eval_var_fields_prover]; exact h_msg_eq
  have hbwit : paddedBitsWitness { message := input_var_message, messageLen := input_var_messageLen } env
      = paddedBitsValue msg ℓ := by
    simp only [paddedBitsWitness]
    rw [hb, h_msgLen_eq]
  have hfwit : lenFlagsWitness { message := input_var_message, messageLen := input_var_messageLen } env
      = lenFlagsValue ℓ := by
    simp only [lenFlagsWitness]
    rw [h_msgLen_eq]
  -- padded witness evaluates to paddedBitsValue msg ℓ
  have h_pad_val : Vector.map (Expression.eval env.toEnvironment) pvar = paddedBitsValue msg ℓ := by
    rw [← hbwit]
    apply Vector.ext
    intro i hi
    rw [hpvar, Vector.getElem_map, Vector.getElem_mapRange]
    rw [show Expression.eval env.toEnvironment (var { index := i₀ + i }) = env.get (i₀ + i) from rfl]
    exact h_pad_env ⟨i, hi⟩
  -- lenFlags witness evaluates to lenFlagsValue ℓ
  have h_flags_val : Vector.map (Expression.eval env.toEnvironment) fvar = lenFlagsValue ℓ := by
    rw [← hfwit]
    apply Vector.ext
    intro i hi
    rw [hfvar, Vector.getElem_map, Vector.getElem_mapRange]
    rw [show Expression.eval env.toEnvironment (var { index := i₀ + paddedBitsLen + i }) = env.get (i₀ + paddedBitsLen + i) from rfl]
    exact h_flags_env ⟨i, hi⟩
  -- message bytes < 256
  have h_msg256 : ∀ i : Fin inputBufferLen, msg[i] < 256 := by
    intro i; have := h_msg_assum i
    simpa [hmsg, fieldElemsToNat, Vector.getElem_map] using this
  -- booleanity of evaluated padded bits
  have h_bool' : ∀ i : Fin paddedBitsLen, IsBool (Vector.map (Expression.eval env.toEnvironment) pvar)[i] := by
    intro i; rw [h_pad_val]; exact paddedBitsValue_isBool msg ℓ i
  -- per-byte spec equation
  have h_byte_eq' : ∀ j : Fin paddedBytesLen,
      paddedByteVal (Vector.map (Expression.eval env.toEnvironment) pvar) j = specPaddedByte msg ℓ j.val := by
    intro j; rw [h_pad_val]; exact paddedByteVal_paddedBitsValue msg h_msg256 ℓ j
  -- CheckPad message bytes assumption (in input_message form)
  have h_cp_assum : ∀ i : Fin inputBufferLen, ZMod.val input_message[i.val] < 256 := by
    intro i; have := h_msg_assum i; simpa [fieldElemsToNat, Vector.getElem_map] using this
  -- CheckPad Assumptions (bytes) and Spec
  have h_cp_assum_goal : CheckPad.Assumptions
      { messageLen := input_messageLen, message := input_message,
        lenFlags := Vector.map (Expression.eval env.toEnvironment) fvar,
        padded := Vector.map (Expression.eval env.toEnvironment) pvar } := h_cp_assum
  have h_cp_spec_goal : CheckPad.Spec
      { messageLen := input_messageLen, message := input_message,
        lenFlags := Vector.map (Expression.eval env.toEnvironment) fvar,
        padded := Vector.map (Expression.eval env.toEnvironment) pvar } := by
    refine ⟨h_len_assum, ?_, ?_, ?_⟩
    · rw [h_flags_val]; exact lenFlagsValue_oneHotAt ℓ
    · exact h_bool'
    · exact h_byte_eq'
  -- block normalization antecedents (inline, concrete indices) and chaining
  obtain ⟨_, st1_norm⟩ := h_c1
    (by intro i
        rw [Fin.getElem_fin]
        have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 0 i.val i.isLt
        rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 0) i.val i.isLt])
  obtain ⟨_, st2_norm⟩ := h_c2
    ⟨st1_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 1 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 1) i.val i.isLt])⟩
  obtain ⟨_, st3_norm⟩ := h_c3
    ⟨st2_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 2 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 2) i.val i.isLt])⟩
  obtain ⟨_, st4_norm⟩ := h_c4
    ⟨st3_norm,
     (by intro i
         rw [Fin.getElem_fin]
         have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 3 i.val i.isLt
         rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 3) i.val i.isLt])⟩
  obtain ⟨_, st5_norm⟩ := h_c5
    ⟨h_len_assum,
     (by rw [h_flags_val, hℓ]; exact lenFlagsValue_oneHotAt ℓ),
     st4_norm⟩
  -- assemble the goal
  refine ⟨⟨h_cp_assum_goal, h_cp_spec_goal⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- CompressBlock1 Assumptions (block only; state is the constant IV H0)
    intro i
    rw [Fin.getElem_fin]
    have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 0 i.val i.isLt
    rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 0) i.val i.isLt]
  · exact ⟨st1_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 1 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 1) i.val i.isLt])⟩
  · exact ⟨st2_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 2 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 2) i.val i.isLt])⟩
  · exact ⟨st3_norm,
      (by intro i
          rw [Fin.getElem_fin]
          have h := paddedBlock_normalized env.toEnvironment pvar h_bool' 3 i.val i.isLt
          rwa [← getElem_eval_vector (α := fields 32) env.toEnvironment (paddedBlock pvar 3) i.val i.isLt])⟩
  · exact ⟨h_len_assum,
      (by rw [h_flags_val, hℓ]; exact lenFlagsValue_oneHotAt ℓ),
      st4_norm⟩
  · -- SelectDigest Assumptions
    refine ⟨h_len_assum, ?_, ?_⟩
    · rw [h_flags_val]; exact lenFlagsValue_oneHotAt ℓ
    · intro k i
      fin_cases k
      · exact st1_norm i
      · exact st2_norm i
      · exact st3_norm i
      · exact st4_norm i
      · exact st5_norm i

end

section
open Challenge.CostR1CS
open Solution.SHA256.Cost

-- `maxRecDepth` controls elaboration stack depth only (not the trusted base and
-- not the heartbeat budget); the deep `do`-blocks here need more than the default.
set_option maxRecDepth 8000

-- Keep the trusted R1CS predicates opaque while *applying* the per-gadget
-- certificates (see `Cost.lean`): otherwise the unifier evaluates `r1csProducts`
-- on the asserted expressions and loops on neutral subterms.
attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

/-! ### Structural cost of the top-level circuit

The per-gadget cost / R1CS leaves live in `Cost.lean`; here we just assemble
`main`'s total count and its single-row R1CS certificate by structural recursion
over `main`'s own `do`-block, without native evaluation or `decide`. -/

@[reducible] def allocations : Nat := 73153
@[reducible] def constraints : Nat := 78917

theorem mainCost :
    circuitCost main ⟨allocations, constraints⟩ :=
  fun input =>
  (CostIs.bind (CostIs.witnessVector paddedBitsLen _) fun _ =>
    CostIs.bind (CostIs.witnessVector inputBufferLen _) fun _ =>
    CostIs.bind (Cost.costIs_sub_checkPad _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock1 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlockWide _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlockWide _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlockWide _) fun _ =>
    CostIs.bind (Cost.costIs_sub_compressBlock5 _) fun _ =>
    CostIs.bind (Cost.costIs_sub_selectDigest _) fun _ =>
    CostIs.pure _
      : CostIs (main input) ⟨allocations, constraints⟩)

/-- Structural single-row R1CS certificate for the circuit *family* `main`,
for every affine symbolic input. Each assert is an affine combination (or
`A·B`/`A·B−C` of affine forms), threaded through the affine message + length
inputs and the witnessed affine padded bits, length flags and compress-block
outputs. -/
theorem isR1CS : Challenge.CostR1CS.isR1CS main :=
  isR1CS_of_IsR1CSCirc
  (fun input hinput => by
    refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector paddedBitsLen _) fun npad => ?_
    refine IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector inputBufferLen _) fun nflags => ?_
    have hpadded : AffineW
        ((Circuit.witnessVector paddedBitsLen
          (paddedBitsWitness input)).output npad) :=
      affineW_witnessVector_output _ _ _
    have hflags : AffineW
        ((Circuit.witnessVector inputBufferLen
          (lenFlagsWitness input)).output nflags) :=
      affineW_witnessVector_output _ _ _
    refine IsR1CSCirc.bind
      (Cost.r1cs_sub_checkPad _ (Cost.affine_input_messageLen input hinput)
        (Cost.affineW_input_message input hinput) hflags hpadded) fun _ => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock1 _
        (Cost.affineW_paddedBlock _ hpadded 0)) fun n1 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlockWide _ (Cost.affineW_subOut_compressBlock1 _ n1)
        (Cost.affineW_paddedBlock _ hpadded 1)) fun n2 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlockWide _ (Cost.affineW_subOut_compressBlockWide _ n2)
        (Cost.affineW_paddedBlock _ hpadded 2)) fun n3 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlockWide _ (Cost.affineW_subOut_compressBlockWide _ n3)
        (Cost.affineW_paddedBlock _ hpadded 3)) fun n4 => ?_
    refine IsR1CSCirc.bind_out
      (Cost.r1cs_sub_compressBlock5 _
        (Cost.affineW_subOut_compressBlockWide _ n4) hflags) fun n5 => ?_
    refine IsR1CSCirc.bind (Cost.r1cs_selectDigest _ hflags ?_) fun _ => ?_
    · intro k hk j hj
      have hpad : paddedBlocksLen = 5 := rfl
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with
        rfl | rfl | rfl | rfl | rfl
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock1 _ n1 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlockWide _ n2 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlockWide _ n3 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlockWide _ n4 j hj
      · simp [SelectDigest.statesVec]
        exact Cost.affineW_subOut_compressBlock5 _ n5 j hj
    exact IsR1CSCirc.pure _)
  (fun input hinput n => by
    intro i hi
    have hi8 : i < 8 := by
      have hsz : size Output = 8 := rfl
      omega
    change Affine (((main input).output n).digest[i])
    simp only [main, Circuit.bind_output_eq, Circuit.pure_output_eq]
    exact Cost.affineW_subOut_selectDigest _ _ i hi8)

end

end Solution.SHA256
