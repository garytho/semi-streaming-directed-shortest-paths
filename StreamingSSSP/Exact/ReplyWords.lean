module

public import StreamingSSSP.Exact.MeasuredOrigins

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingSSSP.Exact.DescriptorProgram

variable {n : ℕ}

def Request.replyWords : (request : Request n) → request.Reply → List ℕ
  | .base .., answer => answer.toList
  | .level .., answer => answer.vertices.toList ++ [answer.source]
  | .parents .., answer => answer.toList.flatMap fun parent =>
      match parent with
      | none => [0, 0, 0, 0]
      | some e => [1, e.source.val, e.target.val, e.weight]

theorem Request.reply_count (request : Request n) (answer : request.Reply) :
    (request.replyWords answer).length ≤ 4 * n + 4 := by
  cases request with
  | base =>
      change Labels n at answer
      simp [replyWords, ← Hopset.Backend.vector_indices] <;> omega
  | level =>
      change LevelAnswer n at answer
      simp [replyWords, ← Hopset.Backend.vector_indices] <;> omega
  | parents source weightBound distances =>
      change Vector (Option (StoredEdges.Edge n)) n at answer
      have hlen (parent : Option (StoredEdges.Edge n)) :
          (match parent with | none => [0, 0, 0, 0] | some e => [1, e.source.val, e.target.val, e.weight]).length = 4 := by
        cases parent <;> rfl
      simp [replyWords, List.length_flatMap, hlen, ← Hopset.Backend.vector_indices, Function.comp_def] <;> omega

end StreamingSSSP.Exact.DescriptorProgram

namespace StreamingSSSP.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram StoredEdges
open Hopset.Measured

variable {n : ℕ}

def replyCapacity (n coefficient exponent confidence : ℕ) : ℕ :=
  max (valueCapacity n coefficient exponent confidence) (valueCapacity (n + 1) coefficient exponent confidence)

theorem payload_capacity (n coefficient exponent confidence : ℕ) (hn : 0 < n) :
    40 * n * ((2 * n) ^ exponent + 1) ≤ valueCapacity n coefficient exponent confidence := by
  let b := 2 * n
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hw : 1 ≤ b ^ exponent := by change 0 < _; positivity
  have h40 : 40 ≤ b ^ 6 := by
    have h := Nat.pow_le_pow_left hb 6
    norm_num at h
    omega
  have hE : 1 ≤ Hopset.Measured.envelope n coefficient exponent confidence ^ 100 := by
    change 0 < _
    have h := envelope_large n coefficient exponent confidence
    positivity
  unfold valueCapacity
  calc
    _ ≤ 40 * n * (2 * b ^ exponent) :=
      Nat.mul_le_mul_left (40 * n) (by change b ^ exponent + 1 ≤ 2 * b ^ exponent; omega)
    _ = 80 * n * b ^ exponent := by ring
    _ = 40 * b * b ^ exponent := by dsimp only [b]; ring
    _ ≤ b ^ 6 * b * b ^ exponent := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right b h40)
    _ = b ^ (exponent + 7) := by rw [pow_add]; ring
    _ ≤ b ^ (exponent + 100) := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ hE

theorem vector_words (values : Vector ℕ n) (cap : ℕ) (h : ∀ v, values.get v ≤ cap) :
    ∀ value ∈ values.toList, value ≤ cap := by
  intro value hv
  rw [← Hopset.Backend.vector_indices] at hv
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hv
  exact h v

theorem capacity_vertices (n coefficient exponent confidence : ℕ) (hn : 0 < n) :
    n ≤ valueCapacity n coefficient exponent confidence := by
  have hE : 1 ≤ Hopset.Measured.envelope n coefficient exponent confidence ^ 100 := by
    change 0 < _
    have h := envelope_large n coefficient exponent confidence
    positivity
  have hp : (2 * n) ^ 1 ≤ (2 * n) ^ (exponent + 100) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp' : 2 * n ≤ (2 * n) ^ (exponent + 100) := by simpa only [pow_one] using hp
  unfold valueCapacity
  exact (show n ≤ 2 * n by omega).trans (hp'.trans (Nat.le_mul_of_pos_right _ hE))

theorem handler_reply_words (source : Fin n) (exponent confidence coefficient weightExponent : ℕ)
    (input : List (Edge n)) (request : Request n)
    (hinput : ∀ e ∈ input, e.weight ≤ n ^ exponent) (hA : exponent ≤ weightExponent)
    (h : request.rawBounds (EdgeTransducer.preprocessingEdges input source (n ^ exponent))
      (coefficient * Parameters.ell n) ((2 * n) ^ weightExponent)) :
    Early.Sampling.Holds (handler source exponent confidence input request)
      (fun out => ∀ value ∈ request.replyWords out.result, value ≤ replyCapacity n coefficient weightExponent confidence) := by
  cases request with
  | base descriptor querySource denominator clock =>
      have hw : ∀ e ∈ input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor source (n ^ exponent),
          e.weight ≤ (2 * n) ^ weightExponent := by rw [base_input_eq]; exact h.2
      have hp := Approx.Measured.solve_payloads (baseView descriptor) input (baseAuxiliary descriptor source (n ^ exponent))
        (sourcePositive querySource) (safeAccuracy denominator) (Parameters.blockSize n) confidence _
        (safeAccuracy_pos denominator) querySource (base_input_positive descriptor source (n ^ exponent) input) hw
      refine Early.Sampling.holds_map hp (fun out => (fromBase out).map integerLabels) _ ?_
      intro out ho value hv
      have hvec := vector_words (integerLabels out.result) _ (fun v => by
        simpa only [integerLabels, Vector.get_ofFn] using ho v)
      exact (hvec value hv).trans ((payload_capacity n coefficient weightExponent confidence (sourcePositive source)).trans (le_max_left _ _))
  | level descriptor denominator clock =>
      have hw : ∀ e ∈ input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor source (n ^ exponent),
          e.weight ≤ (2 * (n + 1)) ^ weightExponent := by
        rw [level_input_eq]
        exact fun e he => (h.2 e he).trans (Nat.pow_le_pow_left (by omega) _)
      have hp := Approx.Measured.solve_payloads (levelView descriptor) input (levelAuxiliary descriptor source (n ^ exponent))
        (Nat.succ_pos n) (safeAccuracy denominator) (Parameters.blockSize (n + 1)) confidence _
        (safeAccuracy_pos denominator) (Fin.last n) (level_input_positive descriptor source (n ^ exponent) input) hw
      refine Early.Sampling.holds_map hp (fun out => (fromLevel out).map integerLevelAnswer) _ ?_
      intro out ho value hv
      change value ∈ (integerLevelAnswer out.result).vertices.toList ++ [(integerLevelAnswer out.result).source] at hv
      have hbound : value ≤ 40 * (n + 1) * ((2 * (n + 1)) ^ weightExponent + 1) := by
        rcases List.mem_append.mp hv with hv | hv
        · exact vector_words _ _ (fun v => by
            simpa only [integerLevelAnswer, Vector.get_ofFn] using ho v.castSucc) value hv
        · have he := List.mem_singleton.mp hv
          rw [he]
          exact ho (Fin.last n)
      exact hbound.trans ((payload_capacity (n + 1) coefficient weightExponent confidence (Nat.succ_pos n)).trans (le_max_right _ _))
  | parents scanSource weightBound distances =>
      have hn := sourcePositive source
      have hN : n ≤ replyCapacity n coefficient weightExponent confidence :=
        (capacity_vertices n coefficient weightExponent confidence hn).trans (le_max_left _ _)
      have hW : n ^ exponent ≤ replyCapacity n coefficient weightExponent confidence := by
        have hp := (Nat.pow_le_pow_left (show n ≤ 2 * n by omega) exponent).trans
          (Nat.pow_le_pow_right (by omega : 1 ≤ 2 * n) (show exponent ≤ weightExponent + 100 by omega))
        have he : 1 ≤ Hopset.Measured.envelope n coefficient weightExponent confidence ^ 100 := by
          change 0 < _
          have h := envelope_large n coefficient weightExponent confidence
          positivity
        exact (hp.trans (Nat.le_mul_of_pos_right _ he)).trans (le_max_left _ _)
      refine Early.Sampling.holds_pure _ _ ?_
      intro value hv
      obtain ⟨parent, hp, hv⟩ := List.mem_flatMap.mp hv
      rw [← Hopset.Backend.vector_indices] at hp
      obtain ⟨v, _, he⟩ := List.mem_map.mp hp
      simp only [Vector.get_ofFn] at he
      subst parent
      change value ∈ (match ParentPass.run scanSource weightBound distances.get input v with
        | none => [0, 0, 0, 0]
        | some e => [1, e.source.val, e.target.val, e.weight]) at hv
      cases hs : ParentPass.run scanSource weightBound distances.get input v with
      | none => simp only [hs, List.mem_cons, List.not_mem_nil, or_false, or_self] at hv; subst value; omega
      | some e =>
          have hm := (ParentPass.run_valid scanSource weightBound distances.get input v e hs).1
          simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl
          · omega
          · exact e.source.isLt.le.trans hN
          · exact e.target.isLt.le.trans hN
          · exact (hinput e hm).trans hW

theorem evaluate_reply_words (source : Fin n) (exponent confidence : ℕ) (input : List (Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => ∀ entry ∈ out.result.trace, ∀ value ∈ entry.request.replyWords entry.answer,
        value ≤ replyCapacity n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence)) := by
  let conf := oracleConfidence exponent confidence
  have hr := execute_run (handler source exponent conf input) (parentReplyOfEdges input)
    (handler_parents source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have ho := execute_origins (handler source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have hb : Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) {}
        out.result.result out.result.cache out.result.trace ∧ Origins (handler source exponent conf input) out) :=
    fun atom hatom => ⟨hr atom hatom, ho atom hatom⟩
  refine Early.Sampling.holds_mono hb ?_
  intro out hout entry he value hv
  obtain ⟨atom, ha, hanswer⟩ := hout.2.replies entry he (hout.1.root_fresh input entry he)
  have hraw := hout.1.raw_bounds input hw entry he
  have hb := handler_reply_words source exponent conf _ _ input entry.request hw (by omega) hraw atom ha
  dsimp only at hb
  rw [hanswer] at hb
  exact hb value hv

end StreamingSSSP.Exact.Implementation.Measured
