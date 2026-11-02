module

public import StreamingReachability.Hopset.TraceRewards

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical BigOperators

noncomputable section

def calibratedTraceLaw (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) : Law (List (Entry n)) :=
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  (Law.family n (fun _ => Ranks.firstHit (Reference.earlyRates n hn x))).bind fun ranks =>
    traceLaw cfg hn stored input (Vector.ofFn ranks) (Parameters.maximumLevel n + 1) 0 [Finset.univ]

theorem expected_trace_copies (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    (calibratedTraceLaw n hn accuracy x delta ha hd stored input).expect
        (fun trace => (traceCost copyReward trace : ℝ)) ≤
      2 * n * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  calc
    _ ≤ ∑ v : Fin n,
        (Law.family n (fun _ => Ranks.firstHit (Reference.earlyRates n hn x))).expect (fun ranks =>
          Reference.metricPotential cfg hn stored input (Reference.copyVisit cfg v)
            (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) :=
      root_traceCost_le_sum cfg hn stored input (Reference.earlyRates n hn x) hs hp hsize hnum
        copyReward (Reference.copyVisit cfg)
        (fun rank r queue _ => (copyReward_mean cfg hn stored input rank r queue).le) _
    _ ≤ ∑ _v : Fin n, 2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      simp_rw [Reference.copyVisit_potential]
      exact Reference.expected_stopped_copies_per_vertex n hn accuracy x delta
        (volume stored.blocks) ha hd stored input v
    _ = _ := by simp; ring

theorem expected_trace_records (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    (calibratedTraceLaw n hn accuracy x delta ha hd stored input).expect
        (fun trace => (traceCost recordReward trace : ℝ)) ≤
      Reference.recordVisitBudget n accuracy * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) *
        (n + volume stored.blocks) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  calc
    _ ≤ ∑ v : Fin n,
        (Law.family n (fun _ => Ranks.firstHit (Reference.earlyRates n hn x))).expect (fun ranks =>
          Reference.metricPotential cfg hn stored input (Reference.recordMetric cfg stored input v)
            (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) :=
      root_traceCost_le_sum cfg hn stored input (Reference.earlyRates n hn x) hs hp hsize hnum
        recordReward (Reference.recordMetric cfg stored input)
        (fun rank r queue _ => (recordReward_mean cfg hn stored input rank r queue hs hp hsize).le) _
    _ ≤ ∑ v : Fin n,
        ((Reference.vertexWeight stored v : ℝ) * Reference.recordVisitBudget n accuracy) *
          (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro v _
      exact Reference.expected_stopped_records_per_vertex n hn accuracy x delta
        (volume stored.blocks) ha hd stored input v
    _ = (∑ v : Fin n, (Reference.vertexWeight stored v : ℝ)) *
        (Reference.recordVisitBudget n accuracy * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ))) := by
      simp only [mul_assoc, Finset.sum_mul]
    _ = _ := by
      have hw : (∑ v : Fin n, (Reference.vertexWeight stored v : ℝ)) = n + volume stored.blocks := by
        exact_mod_cast Reference.vertexWeight_sum stored
      rw [hw]
      ring

theorem expected_trace_blocks (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    (calibratedTraceLaw n hn accuracy x delta ha hd stored input).expect
        (fun trace => (traceCost blockReward trace : ℝ)) ≤
      (400 * (Parameters.k n : ℝ) * Parameters.ell n) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) * n := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  calc
    _ ≤ ∑ v : Fin n,
        (Law.family n (fun _ => Ranks.firstHit (Reference.earlyRates n hn x))).expect (fun ranks =>
          Reference.metricPotential cfg hn stored input (Reference.blockMetric cfg stored input v)
            (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) :=
      root_traceCost_le_sum cfg hn stored input (Reference.earlyRates n hn x) hs hp hsize hnum
        blockReward (Reference.blockMetric cfg stored input)
        (fun rank r queue _ => (blockReward_mean cfg hn stored input rank r queue hs hp hsize hnum).le) _
    _ ≤ ∑ _v : Fin n, (400 * (Parameters.k n : ℝ) * Parameters.ell n) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro v _
      exact Reference.expected_stopped_block_copies_per_vertex n hn accuracy x delta
        (volume stored.blocks) ha hd stored input v
    _ = _ := by simp; ring

theorem expected_trace_bad (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (calibratedTraceLaw n hn accuracy x delta ha hd stored input).expect
        (fun trace => (traceCost (badReward cfg stored input) trace : ℝ)) ≤
      4 * (n : ℝ) ^ 3 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) *
        Real.exp (-25 * Parameters.ell n) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  calc
    _ ≤ ∑ v : Fin n,
        (Law.family n (fun _ => Ranks.firstHit (Reference.earlyRates n hn x))).expect (fun ranks =>
          Reference.metricPotential cfg hn stored input (Reference.badMetric cfg stored input v)
            (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) :=
      root_traceCost_le_sum cfg hn stored input (Reference.earlyRates n hn x) hs hp hsize hnum
        (badReward cfg stored input) (Reference.badMetric cfg stored input)
        (fun rank r queue _ => badReward_mean_le cfg hn stored input rank r queue hs hp hsize hnum) _
    _ ≤ ∑ _v : Fin n, Reference.badVisitBudget n *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro v _
      exact Reference.expected_stopped_bad_per_vertex n hn accuracy x delta
        (volume stored.blocks) ha hd stored input v
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Reference.badVisitBudget]
      ring

end

end StreamingReachability.Hopset.Batched
