module

public import StreamingReachability.Hopset.TrialLaw
public import StreamingReachability.Hopset.MetricBounds

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def AllGood (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (queue : List (Finset (Fin n))) : Prop :=
  ∀ S ∈ queue, Reference.BallsGood cfg stored input r S

structure Entry (n : ℕ) where
  level : ℕ
  queue : List (Finset (Fin n))
  step : Step n

/-- This trace is a proof-only stopping construction, not a stored runtime log. -/
def traceLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → Law (List (Entry n))
  | 0, _, _ => Law.pure []
  | fuel + 1, r, queue =>
      if AllGood cfg stored input r queue then
        (levelLaw cfg hn stored input rank r queue.toArray.toVector).bind fun step =>
          (traceLaw cfg hn stored input rank fuel (r + 1) step.children).map
            (⟨r, queue, step⟩ :: ·)
      else Law.pure []

abbrev Reward (n : ℕ) := ℕ → List (Finset (Fin n)) → Step n → ℕ

def traceCost (reward : Reward n) (trace : List (Entry n)) : ℕ :=
  (trace.map fun entry => reward entry.level entry.queue entry.step).sum

theorem traceCost_succ (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (reward : Reward n)
    (fuel r : ℕ) (queue : List (Finset (Fin n))) :
    (traceLaw cfg hn stored input rank (fuel + 1) r queue).expect (fun trace => (traceCost reward trace : ℝ)) =
      if AllGood cfg stored input r queue then
        (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect (fun step =>
          (reward r queue step : ℝ) +
            (traceLaw cfg hn stored input rank fuel (r + 1) step.children).expect
              (fun trace => (traceCost reward trace : ℝ)))
      else 0 := by
  by_cases hg : AllGood cfg stored input r queue
  · simp only [traceLaw, hg, ↓reduceIte, Law.expect_bind, Law.expect_map, traceCost,
      List.map_cons, List.sum_cons, Nat.cast_add, Law.expect_add, Law.expect_const]
  · simp only [traceLaw, hg, ↓reduceIte, Law.expect_pure, traceCost, List.map_nil,
      List.sum_nil, Nat.cast_zero]

theorem queue_get_mem (queue : List (Finset (Fin n))) (i : Fin queue.toArray.size) :
    queue.toArray.toVector.get i ∈ queue := by
  have h := List.get_mem queue ⟨i.val, by simpa using i.isLt⟩
  simpa [Vector.get_eq_getElem] using h

theorem queue_sum (queue : List (Finset (Fin n))) (f : Finset (Fin n) → ℝ) :
    (queue.map f).sum = ∑ i : Fin queue.toArray.size, f (queue.toArray.toVector.get i) := by
  calc
    _ = (queue.toArray.toVector.toList.map f).sum := by simp
    _ = ((List.finRange queue.toArray.size).map fun i => f (queue.toArray.toVector.get i)).sum := by
      have h := congrArg (fun L => (L.map f).sum) (Backend.vector_indices queue.toArray.toVector)
      simpa only [List.map_map, Function.comp_def] using h.symm
    _ = _ := sum_finRange _

theorem expected_traceCost_le (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (reward : Reward n) (metric : Reference.Metric n cfg)
    (hlocal : ∀ r queue, AllGood cfg stored input r queue →
      (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
          (fun step => (reward r queue step : ℝ)) ≤
        ∑ i : Fin queue.toArray.size,
          (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
            (fun step => (metric r (queue.toArray.toVector.get i) (fun v => rank.get v) step.value : ℝ)))
    (fuel r : ℕ) (queue : List (Finset (Fin n))) :
    (traceLaw cfg hn stored input rank fuel r queue).expect (fun trace => (traceCost reward trace : ℝ)) ≤
      (queue.map fun S =>
        Reference.metricPotential cfg hn stored input metric fuel r S (fun v => rank.get v)).sum := by
  induction fuel generalizing r queue with
  | zero =>
      simp [traceLaw, traceCost, Reference.metricPotential, Branching.potential]
  | succ fuel ih =>
      rw [traceCost_succ]
      by_cases hg : AllGood cfg stored input r queue
      · simp only [hg, ↓reduceIte]
        let phi := fun S =>
          Reference.metricPotential cfg hn stored input metric fuel (r + 1) S (fun v => rank.get v)
        calc
          _ ≤ (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
              (fun step => (reward r queue step : ℝ) + (step.children.map phi).sum) := by
            apply Law.expect_mono
            intro step
            exact add_le_add le_rfl (ih (r + 1) step.children)
          _ = (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
                (fun step => (reward r queue step : ℝ)) +
              (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
                (fun step => (step.children.map phi).sum) := Law.expect_add _ _ _
          _ ≤ (∑ i : Fin queue.toArray.size,
                (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
                  (fun step => (metric r (queue.toArray.toVector.get i) (fun v => rank.get v) step.value : ℝ))) +
              ∑ i : Fin queue.toArray.size,
                (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
                  (fun step => (step.children.map phi).sum) := by
            rw [level_children cfg hn stored input rank r _ hs hp hsize hnum phi]
            exact add_le_add (hlocal r queue hg) le_rfl
          _ = _ := by
            rw [queue_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            rw [Reference.metricPotential_succ,
              ite_eq_left (hg _ (queue_get_mem queue i)), Law.expect_add]
      · simp only [hg, ↓reduceIte]
        apply List.sum_nonneg
        intro a ha
        obtain ⟨S, hS, rfl⟩ := List.mem_map.mp ha
        exact Reference.metricPotential_nonneg cfg hn stored input metric _ _ _ _

end

end StreamingReachability.Hopset.Batched
