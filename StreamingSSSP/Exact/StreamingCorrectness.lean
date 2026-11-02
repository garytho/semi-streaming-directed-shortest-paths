module

public import StreamingSSSP.Exact.StreamingConfidence

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open DescriptorProgram

variable {n : ℕ}

def CorrectResult (input : List (StoredEdges.Edge n)) (source : Fin n) (result : Result n) : Prop :=
  result.distances = (StoredEdges.graphOfEdges input).dist source ∧
    (ParentPass.graph result.parents).dist source = (StoredEdges.graphOfEdges input).dist source ∧
    WellFounded (fun u v => ∃ e, result.parents v = some e ∧ e.source = u) ∧
    ∀ v e, result.parents v = some e → e ∈ input ∧ e.target = v

theorem answered_physical (source : Fin n) (exponent : ℕ) (input : List (StoredEdges.Edge n))
    (cache : Cache n) (entry : Answered n)
    (ha : Agrees (parentReplyOfEdges input) cache entry.request entry.answer)
    (hg : RequestAccurate source exponent input entry.request entry.answer) :
    ∀ q ∈ observeQuery (preprocess (StoredEdges.graphOfEdges input) source (n ^ exponent)) entry.request,
      PhysicalAccurate cache.baseOracle cache.levelOracle q := by
  let G := preprocess (StoredEdges.graphOfEdges input) source (n ^ exponent)
  have hr := oracle_reply G (parentReplyOfEdges input) cache entry.request entry.answer ha
  rcases entry with ⟨request, answer, fresh⟩
  cases request with
  | base descriptor scanSource denominator clock =>
      have he : cache.baseOracle (descriptor.graph G) scanSource denominator clock = answer.get := by
        have h := congrArg Vector.get hr
        simpa only [interpretReply, vector_get_ofFn] using h
      intro q hq
      change q ∈ [Sum.inl ⟨descriptor.graph G, scanSource, denominator, clock⟩] at hq
      rcases List.mem_singleton.mp hq with rfl
      change IntegerApprox (descriptor.graph G) scanSource denominator
        (cache.baseOracle (descriptor.graph G) scanSource denominator clock)
      rw [he]
      exact hg
  | level descriptor denominator clock =>
      have he : cache.levelOracle (descriptor.graph G) none denominator clock = answer.at := by
        have h := congrArg LevelAnswer.at hr
        simpa only [interpretReply, LevelAnswer.at_ofFn] using h
      intro q hq
      change q ∈ [Sum.inr ⟨descriptor.graph G, none, denominator, clock⟩] at hq
      rcases List.mem_singleton.mp hq with rfl
      change IntegerApprox (descriptor.graph G) none denominator
        (cache.levelOracle (descriptor.graph G) none denominator clock)
      rw [he]
      exact hg
  | parents =>
      intro q hq
      cases hq

theorem Run.parent_edges {source : Fin n} {exponent : ℕ} {cache final : Cache n} {result : Result n}
    {trace : List (Answered n)} (input : List (StoredEdges.Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) cache result final trace) :
    ∀ v e, result.parents v = some e → e ∈ input ∧ e.target = v := by
  let G := preprocess (StoredEdges.graphOfEdges input) source (n ^ exponent)
  have he : result = exactSSSP final.baseOracle final.levelOracle input source exponent :=
    (h.replay G).symm.trans (DescriptorProgram.exact_eq _ _ _ _ _)
  intro v e hp
  rw [he] at hp
  have hv := ParentPass.run_valid source (n ^ exponent)
    (transformedEstimates final.baseOracle final.levelOracle input source exponent) input v e hp
  exact ⟨hv.1, hv.2.1⟩

set_option maxRecDepth 8192 in
theorem Run.correct {source : Fin n} {exponent : ℕ} {cache final : Cache n} {result : Result n}
    {trace : List (Answered n)} (input : List (StoredEdges.Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) cache result final trace)
    (hW : ∀ e ∈ input, e.weight ≤ n ^ exponent)
    (hg : ∀ entry ∈ trace, RequestAccurate source exponent input entry.request entry.answer) :
    CorrectResult input source result := by
  let G := preprocess (StoredEdges.graphOfEdges input) source (n ^ exponent)
  have hphysical : ∀ q ∈ Program.trace (observeQuery G)
      (interpretReply G final.baseOracle final.levelOracle (parentReplyOfEdges input))
      (DescriptorProgram.exact source exponent), PhysicalAccurate final.baseOracle final.levelOracle q := by
    intro q hq
    rw [h.replay_trace G (observeQuery G)] at hq
    obtain ⟨entry, he, hq⟩ := List.mem_flatMap.mp hq
    exact answered_physical source exponent input final entry (h.agrees entry he) (hg entry he) q hq
  have hc := DescriptorProgram.exact_correct final.baseOracle final.levelOracle input source exponent hW hphysical
  rw [h.replay G] at hc
  exact ⟨hc.1, hc.2.1, hc.2.2, h.parent_edges input⟩

/-- Only the interpreter receives the original edge stream. All base and level
requests run the proved cube-root hopset algorithm through local descriptor views. -/
noncomputable def evaluate (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n)) :
    Law (Result n) :=
  (execute (requestHandler source exponent (oracleConfidence exponent confidence) input)
    (DescriptorProgram.exact source exponent) {}).map Outcome.result

theorem exact_streaming_correct (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (hW : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    1 - 1 / (n : ℝ) ^ confidence ≤ (evaluate source exponent confidence input).prob (CorrectResult input source) := by
  let handler := requestHandler source exponent (oracleConfidence exponent confidence) input
  let program := DescriptorProgram.exact source exponent
  let mu := execute handler program {}
  let good := fun out : Outcome n (Result n) =>
    ∀ entry ∈ out.trace, RequestAccurate source exponent input entry.request entry.answer
  have hr := execute_run handler (parentReplyOfEdges input)
    (requestHandler_parents source exponent (oracleConfidence exponent confidence) input) program {}
  have hm : mu.prob good ≤ mu.prob (fun out => CorrectResult input source out.result) :=
    Hopset.Batched.prob_mono_supported mu good _ (Early.Sampling.holds_mono hr
      (fun out ho hg => ho.correct input hW hg))
  have hs := root_all_accurate source exponent (oracleConfidence exponent confidence) input
  change 1 - 1 / (n : ℝ) ^ confidence ≤ (mu.map Outcome.result).prob (CorrectResult input source)
  rw [Law.prob_map]
  by_cases hn : 2 ≤ n
  · have hb := exact_failure_budget n exponent confidence hn
    exact (le_trans (by linarith) hs).trans hm
  · have hn₁ : n = 1 := by have hp := source.isLt; omega
    have hz : (1 : ℝ) - 1 / (n : ℝ) ^ confidence = 0 := by simp [hn₁]
    rw [hz]
    exact Law.prob_nonneg _ _

end StreamingSSSP.Exact.Implementation
