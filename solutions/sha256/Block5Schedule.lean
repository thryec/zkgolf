import Solution.SHA256.MessageSchedule
import Solution.SHA256.PaddingTheorems
import Solution.SHA256.SHA256RoundsTheorems
import Clean.Utils.Rotation

namespace Solution.SHA256

open Challenge.Instances.SHA256.Interface (inputBufferLen)

/-!
# Length-only schedule for the fixed fifth SHA-256 block

For the top-level circuit's fixed five-block padded buffer, block index `4`
starts at byte offset `256`. Since `messageLen < 256`, no message byte or `0x80`
marker can occur in that block. Its bytes are therefore exactly the
length-dependent padding constants already described by `specPaddedByteConst`.
-/

/-- The fifth fixed block, as 16 SHA-256 big-endian words. -/
def block5SpecBlock (len : ℕ) : Vector ℕ 16 :=
  Specs.SHA256.bytesToBlock
    (Vector.ofFn fun (i : Fin 64) => specPaddedByteConst len (4 * 64 + i.val))

/-- The full 64-word SHA-256 message schedule for the fifth fixed block. -/
def block5ScheduleConst (len : ℕ) : Vector ℕ 64 :=
  Specs.SHA256.messageSchedule (block5SpecBlock len)

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

/-- Field coefficient for one bit of one precomputed schedule word. Kept as a
definition so R1CS affineness proofs need not unfold the full SHA schedule. -/
def block5ScheduleCoeff (len : ℕ) (word : Fin 64) (bit : Fin 32) : F p :=
  (((block5ScheduleConst len)[word] / 2 ^ bit.val % 2 : ℕ) : F p)

/-- One affine bit of the precomputed block-5 schedule, selected by length flags. -/
def block5ScheduleBit (flags : Var (fields inputBufferLen) (F p))
    (word : Fin 64) (bit : Fin 32) : Expression (F p) :=
  Fin.foldl inputBufferLen
    (fun acc len =>
      acc + flags[len] * ((block5ScheduleCoeff len.val word bit : F p) : Expression (F p)))
    0

/-- The fifth-block schedule as affine expressions in the one-hot length flags. -/
def block5Schedule (flags : Var (fields inputBufferLen) (F p)) :
    Vector (Var (fields 32) (F p)) 64 :=
  Vector.ofFn fun word => Vector.ofFn fun bit => block5ScheduleBit flags word bit

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma block5_specPaddedByte_eq_const (msg : Vector ℕ inputBufferLen) {len i : ℕ}
    :
    specPaddedByte msg len (4 * 64 + i) = specPaddedByteConst len (4 * 64 + i) := by
  unfold specPaddedByte
  have hnot : ¬(4 * 64 + i < len ∧ 4 * 64 + i < inputBufferLen) := by
    intro h
    simp only [inputBufferLen] at h
    omega
  rw [dif_neg hnot]

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma block5SpecBlock_eq_specBlock (msg : Vector ℕ inputBufferLen) {len : ℕ}
    (_hlen : len ≤ inputBufferLen) :
    block5SpecBlock len = specBlock msg len 4 := by
  apply Vector.ext
  intro w hw
  unfold block5SpecBlock specBlock Specs.SHA256.bytesToBlock
  simp only [Vector.getElem_mapFinRange, Vector.getElem_ofFn]
  simp only [block5_specPaddedByte_eq_const msg]

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma bytesToWord32BE_lt {b0 b1 b2 b3 : ℕ}
    (h0 : b0 < 256) (h1 : b1 < 256) (h2 : b2 < 256) (h3 : b3 < 256) :
    Specs.SHA256.bytesToWord32BE b0 b1 b2 b3 < 2^32 := by
  unfold Specs.SHA256.bytesToWord32BE
  omega

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma block5SpecBlock_lt (len : ℕ) (i : Fin 16) :
    (block5SpecBlock len)[i] < 2^32 := by
  change (block5SpecBlock len)[i.val]'i.isLt < 2^32
  unfold block5SpecBlock Specs.SHA256.bytesToBlock
  rw [Vector.getElem_mapFinRange]
  simp only [Vector.getElem_ofFn]
  apply bytesToWord32BE_lt
  · exact specPaddedByteConst_lt len (4 * 64 + (4 * i.val))
  · exact specPaddedByteConst_lt len (4 * 64 + (4 * i.val + 1))
  · exact specPaddedByteConst_lt len (4 * 64 + (4 * i.val + 2))
  · exact specPaddedByteConst_lt len (4 * 64 + (4 * i.val + 3))

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma lowerSigma0_lt {x : ℕ} (hx : x < 2^32) :
    Specs.SHA256.lowerSigma0 x < 2^32 := by
  unfold Specs.SHA256.lowerSigma0
  exact Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow
      (Utils.Rotation.rotRight32_lt _ _ hx)
      (Utils.Rotation.rotRight32_lt _ _ hx))
    (lt_of_le_of_lt (Nat.div_le_self _ _) hx)

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma lowerSigma1_lt {x : ℕ} (hx : x < 2^32) :
    Specs.SHA256.lowerSigma1 x < 2^32 := by
  unfold Specs.SHA256.lowerSigma1
  exact Nat.xor_lt_two_pow
    (Nat.xor_lt_two_pow
      (Utils.Rotation.rotRight32_lt _ _ hx)
      (Utils.Rotation.rotRight32_lt _ _ hx))
    (lt_of_le_of_lt (Nat.div_le_self _ _) hx)

omit [Fact p.Prime] [Fact (p > 2^35)] in
lemma messageSchedule_word_lt (block : Vector ℕ 16)
    (hblock : ∀ i : Fin 16, block[i] < 2^32) :
    ∀ i : Fin 64, (Specs.SHA256.messageSchedule block)[i] < 2^32 := by
  rw [MessageSchedule.messageSchedule_eq_valSchedule]
  have h_inv : ∀ (k : ℕ), k ≤ 48 →
      ∀ (j : ℕ) (hj : j < 64),
        (MessageSchedule.valSchedule block k)[j]'hj < 2^32 := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      rw [MessageSchedule.valSchedule]
      rw [Vector.getElem_mapFinRange]
      split
      · next h => exact hblock ⟨j, h⟩
      · norm_num
    | succ k ih =>
      have hk' : k ≤ 48 := by omega
      have hklt : k < 48 := by omega
      intro j hj
      rw [MessageSchedule.valSchedule, dif_pos hklt]
      by_cases hnew : j = k + 16
      · subst hnew
        rw [Vector.getElem_set_self]
        unfold _root_.add32
        exact Nat.mod_lt _ (by norm_num)
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega)]
        exact ih hk' j hj
  intro i
  exact h_inv 48 (le_refl 48) i.val i.isLt

lemma block5ScheduleConst_lt (len : ℕ) (i : Fin 64) :
    (block5ScheduleConst len)[i] < 2^32 := by
  unfold block5ScheduleConst
  exact messageSchedule_word_lt (block5SpecBlock len) (block5SpecBlock_lt len) i

omit [Fact (p > 2^35)] in
lemma eval_block5ScheduleBit (env : Environment (F p))
    (flags : Var (fields inputBufferLen) (F p)) {ℓ : ℕ}
    (h_onehot : OneHotAt (Vector.map (Expression.eval env) flags) ℓ)
    (hℓ : ℓ < inputBufferLen) (word : Fin 64) (bit : Fin 32) :
    Expression.eval env (block5ScheduleBit flags word bit) =
      (((block5ScheduleConst ℓ)[word] / 2 ^ bit.val % 2 : ℕ) : F p) := by
  unfold block5ScheduleBit
  rw [eval_finFoldl_add]
  have hsum :
      (∑ i : Fin inputBufferLen,
        Expression.eval env
          (flags[i] *
            Expression.const
              (block5ScheduleCoeff i.val word bit))) =
        ∑ i : Fin inputBufferLen,
          (Vector.map (Expression.eval env) flags)[i] *
            block5ScheduleCoeff i.val word bit := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Expression.eval]
    have hget : (Vector.map (Expression.eval env) flags)[i] =
        Expression.eval env (flags[i.val]'i.isLt) := by
      change (Vector.map (Expression.eval env) flags)[i.val]'i.isLt =
        Expression.eval env (flags[i.val]'i.isLt)
      rw [Vector.getElem_map]
    rw [hget]
    rfl
  rw [hsum]
  have hcollapse := oneHot_mul_sum h_onehot hℓ
    (fun len : Fin inputBufferLen => block5ScheduleCoeff len.val word bit)
  simpa [block5ScheduleCoeff] using hcollapse

omit [Fact (p > 2^35)] in
lemma eval_block5ScheduleWord (env : Environment (F p))
    (flags : Var (fields inputBufferLen) (F p)) {ℓ : ℕ}
    (h_onehot : OneHotAt (Vector.map (Expression.eval env) flags) ℓ)
    (hℓ : ℓ < inputBufferLen) (word : Fin 64) :
    Vector.map (Expression.eval env) ((block5Schedule flags)[word]) =
      Vector.map (Expression.eval env) (constWord32 (p := p) ((block5ScheduleConst ℓ)[word])) := by
  apply Vector.ext
  intro bit hbit
  rw [Vector.getElem_map]
  rw [show ((block5Schedule flags)[word])[bit] =
      block5ScheduleBit flags word ⟨bit, hbit⟩ by
    rw [block5Schedule, Fin.getElem_fin, Vector.getElem_ofFn]
    rw [Vector.getElem_ofFn]]
  rw [Vector.getElem_map, constWord32, Vector.getElem_ofFn]
  exact eval_block5ScheduleBit env flags h_onehot hℓ word ⟨bit, hbit⟩

omit [Fact (p > 2^35)] in
lemma block5Schedule_normalized (env : Environment (F p))
    (flags : Var (fields inputBufferLen) (F p)) {ℓ : ℕ}
    (h_onehot : OneHotAt (Vector.map (Expression.eval env) flags) ℓ)
    (hℓ : ℓ < inputBufferLen) (word : Fin 64) :
    Normalized (Vector.map (Expression.eval env) ((block5Schedule flags)[word])) := by
  rw [eval_block5ScheduleWord env flags h_onehot hℓ word]
  exact SHA256Rounds.normalized_constWord32 env _

lemma block5Schedule_valueBits (env : Environment (F p))
    (flags : Var (fields inputBufferLen) (F p)) {ℓ : ℕ}
    (h_onehot : OneHotAt (Vector.map (Expression.eval env) flags) ℓ)
    (hℓ : ℓ < inputBufferLen) (word : Fin 64) :
    valueBits (Vector.map (Expression.eval env) ((block5Schedule flags)[word])) =
      (block5ScheduleConst ℓ)[word] := by
  rw [eval_block5ScheduleWord env flags h_onehot hℓ word]
  exact SHA256Rounds.valueBits_constWord32_of_lt env (block5ScheduleConst_lt ℓ word)

lemma block5Schedule_map_valueBits (env : Environment (F p))
    (flags : Var (fields inputBufferLen) (F p)) {ℓ : ℕ}
    (h_onehot : OneHotAt (Vector.map (Expression.eval env) flags) ℓ)
    (hℓ : ℓ < inputBufferLen) :
    Vector.map valueBits (eval env (block5Schedule flags)) = block5ScheduleConst ℓ := by
  apply Vector.ext
  intro word hword
  rw [Vector.getElem_map,
    ← getElem_eval_vector (α := fields 32) env (block5Schedule flags) word hword,
    CircuitType.eval_var_fields]
  exact block5Schedule_valueBits env flags h_onehot hℓ ⟨word, hword⟩

end

end Solution.SHA256
