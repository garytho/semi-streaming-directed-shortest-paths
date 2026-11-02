module

public import StreamingReachability.Core.BatchDoubling

@[expose] public section

namespace StreamingReachability.Core.BatchSearch

open StoredEdges

variable {n : ℕ}

def ValidQuery (input : List (Edge n)) (seed : ℕ → Fin n → Distance) (q : Query n) : Prop :=
  (∀ u, u ∉ q.request.known → seed q.id u = ⊤) ∧
    ∀ u, SparseLabels.get q.sources u =
      if u ∈ q.request.known
      then multiDist (BlockSearch.blockGraph input q.request.block) (seed q.id) u else ⊤

def AnswerExact (input : List (Edge n)) (seed : ℕ → Fin n → Distance)
    (q : Query n) (out : BlockSearch.Outcome n) : Prop :=
  let d := multiDist (BlockSearch.blockGraph input q.request.block) (seed q.id)
  out.vertices = found q.request.block q.request.known d q.radiusNumerator ∧
    out.records = (out.vertices.sort (· ≤ ·)).map (fun v => (v, d v)) ∧
    out.nextNumerator = nextDistance q.request.block (q.request.known ∪ out.vertices) d

theorem valid_double (input : List (Edge n)) (seed : ℕ → Fin n → Distance)
    (q : Query n) (h : ValidQuery input seed q) : ValidQuery input seed (double q) := h

theorem returned_exact (hn : 0 < n) (input : List (Edge n))
    (seed : ℕ → Fin n → Distance) (q : Query n) (h : ValidQuery input seed q)
    {out : BlockSearch.Outcome n} (hout : (semanticStage hn input q).2 = .returned out) :
    AnswerExact input seed q out := by
  have hi : ∀ u, (SparseLabels.vector q.sources).get u =
      if u ∈ q.request.known
      then multiDist (BlockSearch.blockGraph input q.request.block) (seed q.id) u else ⊤ := by
    simpa only [SparseLabels.vector_get] using h.2
  by_cases hs : (found q.request.block q.request.known
      (BlockSearch.labels hn q.request.block q.request.known q.request.threshold
        (SparseLabels.vector q.sources) input).get q.radiusNumerator).card < q.request.threshold
  · have he : BlockSearch.finish q.request.block q.request.known q.radiusNumerator
        q.request.threshold (BlockSearch.labels hn q.request.block q.request.known q.request.threshold
          (SparseLabels.vector q.sources) input) = out := by
      simpa only [semanticStage, evaluate, hs, ↓reduceIte, Stage.returned.injEq] using hout
    subst out
    obtain ⟨hU, hv, he⟩ := BlockSearch.search_certificate hn q.request.block q.request.known
      q.request.threshold q.radiusNumerator (seed q.id) (SparseLabels.vector q.sources) input
      h.1 hi hs
    refine ⟨hU, ?_, he⟩
    apply List.map_congr_left
    intro v hvU
    exact congrArg (Prod.mk v) (hv v ((Finset.mem_sort _).mp hvU))
  · simp only [semanticStage, evaluate, hs, ↓reduceIte] at hout
    cases hout

theorem runPhases_sound (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (seed : ℕ → Fin n → Distance) (jobs : List (Query n))
    (hj : ∀ q ∈ jobs, ValidQuery input seed q) :
    ∀ p ∈ (runPhases hn input fuel jobs).answers, AnswerExact input seed p.1 p.2 := by
  induction fuel generalizing jobs with
  | zero => simp [runPhases]
  | succ fuel ih =>
      by_cases he : jobs.isEmpty = true
      · simp [runPhases, he]
      · rw [runPhases, ite_eq_right he]
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · obtain ⟨stage, hstage, hret⟩ := List.mem_filterMap.mp hp
          rw [runPhase_correct] at hstage
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hstage
          have hvalid := hj q (List.mem_reverse.mp hq)
          cases hs : (semanticStage hn input q).2 with
          | retry => simp only [hs] at hret; cases hret
          | returned out =>
              have heq : (q, out) = p := by
                simpa only [hs, semanticStage_fst, Option.some.injEq] using hret
              subst p
              exact returned_exact hn input seed q hvalid hs
        · apply ih _ _ p hp
          intro q hq
          obtain ⟨old, ho, rfl, _⟩ := retry_mem hn input jobs hq
          exact valid_double input seed old (hj old ho)

theorem runPhases_covers (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (jobs : List (Query n)) :
    ∀ q ∈ jobs,
      (∃ p ∈ (runPhases hn input fuel jobs).answers, p.1.id = q.id) ∨
      ∃ old ∈ (runPhases hn input fuel jobs).unfinished, old.id = q.id := by
  induction fuel generalizing jobs with
  | zero =>
      intro q hq
      exact Or.inr ⟨q, hq, rfl⟩
  | succ fuel ih =>
      intro q hq
      have hnonempty : jobs.isEmpty = false := by
        apply List.isEmpty_eq_false_iff.mpr
        intro he
        simp only [he, List.not_mem_nil] at hq
      rw [runPhases, hnonempty]
      dsimp only
      have hstage : semanticStage hn input q ∈ (runPhase hn input jobs).stages := by
        rw [runPhase_correct]
        exact List.mem_map.mpr ⟨q, List.mem_reverse.mpr hq, rfl⟩
      cases hs : (semanticStage hn input q).2 with
      | returned out =>
          left
          refine ⟨(q, out), List.mem_append_left _ ?_, rfl⟩
          exact List.mem_filterMap.mpr ⟨_, hstage, by simp only [hs, semanticStage_fst]⟩
      | retry =>
          have hr : double q ∈ retryJobs (runPhase hn input jobs).stages :=
            List.mem_filterMap.mpr ⟨_, hstage, by simp only [hs, semanticStage_fst]⟩
          rcases ih _ (double q) hr with ⟨p, hp, hid⟩ | ⟨old, ho, hid⟩
          · exact Or.inl ⟨p, List.mem_append_right _ hp, hid⟩
          · exact Or.inr ⟨old, ho, hid⟩

theorem run_answers_every_id (hn : 0 < n) (input : List (Edge n)) (x : ℕ)
    (jobs : List (Query n)) (hj : ∀ q ∈ jobs, q.request.block.card ≤ x ∧ q.request.threshold = 1) :
    ∀ q ∈ jobs, ∃ p ∈ (run hn input x jobs).answers, p.1.id = q.id := by
  intro q hq
  rcases runPhases_covers hn input (Nat.log 2 x + 2) jobs q hq with h | ⟨old, ho, _⟩
  · exact h
  · have he := run_finished hn input x jobs hj
    change old ∈ (run hn input x jobs).unfinished at ho
    rw [he] at ho
    cases ho

end StreamingReachability.Core.BatchSearch
