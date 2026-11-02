module

public import StreamingReachability.Hopset.RecordMoments

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

def recordVisitBudget (n accuracy : ℕ) : ℝ :=
  1000 * (Parameters.k n : ℝ) ^ (Parameters.advance n accuracy + 1) * Parameters.ell n

theorem recordVisitBudget_nonneg (n accuracy : ℕ) : 0 ≤ recordVisitBudget n accuracy := by
  unfold recordVisitBudget
  positivity

variable {n : ℕ}

theorem vertexHits_le (G : Graph (Fin n)) (S P : Finset (Fin n)) (v : Fin n) (radius b : ℕ)
    (hin : (incomingCentres G S v radius).card ≤ b)
    (hout : (outgoingCentres G S v radius).card ≤ b) :
    vertexHits G S v P radius ≤ 2 * b := by
  have hi := (Finset.card_le_card (Finset.inter_subset_right :
    P ∩ incomingCentres G S v radius ⊆ incomingCentres G S v radius)).trans hin
  have ho := (Finset.card_le_card (Finset.inter_subset_right :
    P ∩ outgoingCentres G S v radius ⊆ outgoingCentres G S v radius)).trans hout
  unfold vertexHits
  omega

theorem calibrated_record_mean (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (history : List (CopyHistory.Observation n))
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hballs : BallsGood (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input r S)
    (hv : v ∈ S) :
    (CopyHistory.law (earlyRates n hn x) history).expect (fun ranks =>
        (kernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks r S).expect
          (fun step => (recordMetric (Parameters.configuration n accuracy x delta blockVolume ha hd)
            stored input v r S ranks step.value : ℝ))) ≤
      (vertexWeight stored v : ℝ) * recordVisitBudget n accuracy := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let b := Parameters.ballSize n r
  have hin : (incomingCentres G S v (cfg.searchRadius r)).card ≤ b :=
    incoming_card_le G cfg r S v b (hballs v hv).1
  have hout : (outgoingCentres G S v (cfg.searchRadius r)).card ≤ b :=
    outgoing_card_le G cfg r S v b (hballs v hv).2
  have hk : 1 ≤ Parameters.k n := by have := Parameters.k_large n; omega
  have hkp : (Parameters.k n : ℝ) ≤
      (Parameters.k n : ℝ) ^ (cfg.advance + 1) := by
    have h := Nat.pow_le_pow_right hk (show 1 ≤ cfg.advance + 1 by omega)
    simpa only [pow_one] using (show (Parameters.k n : ℝ) ^ 1 ≤
      (Parameters.k n : ℝ) ^ (cfg.advance + 1) by exact_mod_cast h)
  have hke := mul_le_mul_of_nonneg_right hkp (Nat.cast_nonneg (Parameters.ell n))
  have hpositive : 0 ≤ (Parameters.k n : ℝ) ^ (cfg.advance + 1) * Parameters.ell n := by positivity
  change (CopyHistory.law ps history).expect (fun ranks =>
    (kernel cfg hn stored input ranks r S).expect
      (fun step => (recordMetric cfg stored input v r S ranks step.value : ℝ))) ≤ _
  by_cases he : r < cfg.earlyLevel
  · have hlen : ps.length = cfg.earlyLevel := by
      simp only [ps, earlyRates, PivotProfile.length_rates]
      rfl
    have hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2 :=
      Parameters.early_prefix_half n hn x r he
    apply (conditional_early_record_mean ps history cfg hn stored input v r S b he hv hlen
      hc hp hs hin hout).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have hcur : (b : ℝ) * (Ranks.rate ps r).value ≤ 200 * Parameters.k n * Parameters.ell n := by
      simpa only [Nat.add_zero, Nat.zero_add, pow_one] using earlyRate_ball_upper n hn x r 0
    have hadv : (b : ℝ) * (Ranks.rate ps (r + cfg.advance)).value ≤
        200 * (Parameters.k n : ℝ) ^ (cfg.advance + 1) * Parameters.ell n :=
      earlyRate_ball_upper n hn x r cfg.advance
    change 2 * (b : ℝ) * (Ranks.rate ps r).value +
      2 * b * (Ranks.rate ps (r + cfg.advance)).value ≤
        1000 * (Parameters.k n : ℝ) ^ (cfg.advance + 1) * Parameters.ell n
    nlinarith
  · have hrate := Parameters.ball_rate_upper n hn r
    by_cases hl : r < cfg.maximumLevel
    · simp_rw [kernel_record_late cfg hn stored input v r S _ he hl hv]
      rw [Law.expect_const]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h := expected_fresh_hits (PivotProfile.rate n hn cfg.k cfg.logarithm r).value
        (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg
        (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one S G v (cfg.searchRadius r) b hin hout
      apply h.trans
      change 2 * (Parameters.ballSize n r : ℝ) *
        (PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r).value ≤ _
      change _ ≤ 1000 * (Parameters.k n : ℝ) ^ (cfg.advance + 1) * Parameters.ell n
      nlinarith
    · simp_rw [kernel_record_final cfg hn stored input v r S _ he hl hv]
      rw [Law.expect_const]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have h : (vertexHits G S v S (cfg.searchRadius r) : ℝ) ≤ 2 * b := by
        exact_mod_cast vertexHits_le G S S v (cfg.searchRadius r) b hin hout
      have hone := Parameters.rate_one_after_max n hn r (by change cfg.maximumLevel ≤ r; omega)
      rw [hone, mul_one] at hrate
      apply h.trans
      change _ ≤ 1000 * (Parameters.k n : ℝ) ^ (cfg.advance + 1) * Parameters.ell n
      dsimp only [b]
      nlinarith

theorem expected_stopped_records_per_vertex (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (v : Fin n) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => metricPotential (Parameters.configuration n accuracy x delta blockVolume ha hd) hn
          stored input (recordMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
          (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) ≤
      ((vertexWeight stored v : ℝ) * recordVisitBudget n accuracy) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let metric := recordMetric cfg stored input v
  let Q : ℝ := (vertexWeight stored v : ℝ) * recordVisitBudget n accuracy
  let fuel := Parameters.maximumLevel n + 1
  have hQ : 0 ≤ Q := mul_nonneg (Nat.cast_nonneg _) (recordVisitBudget_nonneg n accuracy)
  have hlocal : ∀ r S history, CopyHistory.compatible history S → CopyHistory.past history r →
      BallsGood cfg stored input r S → v ∈ S →
        (Law.family n (fun _ => Ranks.firstHit ps)).expect
            (Law.masked (CopyHistory.event history) (fun ranks =>
              (kernel cfg hn stored input ranks r S).expect
                (fun step => (metric r S ranks step.value : ℝ)))) ≤
          CopyHistory.mass ps history * Q := by
    intro r S history hc hp hg hv
    rw [CopyHistory.moment]
    exact mul_le_mul_of_nonneg_left
      (calibrated_record_mean n hn accuracy x delta blockVolume ha hd stored input v r S history hc hp hg hv)
      (CopyHistory.mass_nonneg ps history)
  have h := stopped_metric_moment cfg hn stored input
    (Parameters.initialNumerator_pos n accuracy x ha) ps (growthBound n) (growthBound_nonneg n)
    (calibrated_prefix_budget n hn accuracy x delta blockVolume ha hd) metric v Q hQ
    (recordMetric_outside cfg stored input v) hlocal fuel 0 Finset.univ []
    (by simp [CopyHistory.compatible]) (by simp [CopyHistory.past])
  let f := fun T ranks => metricPotential cfg hn stored input metric fuel 0 T ranks
  have hmass : CopyHistory.mass (n := n) ps [] = 1 := by
    simp [CopyHistory.mass, CopyHistory.allowed, Law.prob]
  have hmask : Law.masked (CopyHistory.event []) (f Finset.univ) = f Finset.univ := by
    funext ranks
    simp [Law.masked, CopyHistory.event, CopyHistory.allowed]
  change futureMoment ps [] f Finset.univ ≤ _ at h
  dsimp only [futureMoment] at h
  rw [hmask, hmass, one_mul] at h
  simp only [Finset.mem_univ, ↓reduceIte, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (copyBudget_le_twice n fuel
      (by have := Parameters.maximumLevel_le_logarithm n; dsimp [fuel]; omega)) hQ)

theorem vertexWeight_sum (stored : Implicit.Representation n) :
    (∑ v : Fin n, vertexWeight stored v) = n + volume stored.blocks := by
  have h (blocks : List (Finset (Fin n))) :
      (∑ v : Fin n, (1 + (blocks.filter fun B => decide (v ∈ B)).length)) = n + volume blocks := by
    induction blocks with
    | nil => simp [volume]
    | cons B blocks ih =>
        have he (v : Fin n) :
            1 + ((B :: blocks).filter fun C => decide (v ∈ C)).length =
              (1 + (blocks.filter fun C => decide (v ∈ C)).length) +
                if v ∈ B then 1 else 0 := by
          by_cases hv : v ∈ B <;> simp [hv, Nat.add_assoc]
        simp_rw [he]
        rw [Finset.sum_add_distrib, ih, Finset.sum_boole]
        have hb : (Finset.univ.filter fun v => v ∈ B) = B := by ext v; simp
        simp [volume, hb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  exact h stored.blocks

theorem expected_stopped_record_sum (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    ((Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).bind fun ranks =>
        Branching.runCost
          (stoppedKernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks)
          (fun r S step => ∑ v : Fin n,
            metricCharge (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input
              (recordMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
              ranks r S step)
          (Parameters.maximumLevel n + 1) 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤
      recordVisitBudget n accuracy * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) *
        (n + volume stored.blocks) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let fuel := Parameters.maximumLevel n + 1
  change ((Law.family n (fun _ => Ranks.firstHit ps)).bind fun ranks =>
    Branching.runCost (stoppedKernel cfg hn stored input ranks)
      (fun r S step => ∑ v : Fin n,
        metricCharge cfg stored input (recordMetric cfg stored input v) ranks r S step)
      fuel 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤ _
  rw [Law.expect_bind]
  simp_rw [Branching.expected_breadth_first_cost]
  simp only [List.map_singleton, List.sum_singleton]
  have hpotential (ranks : Fin n → ℕ) :
      Branching.potential (stoppedKernel cfg hn stored input ranks)
          (fun r S step => ∑ v : Fin n,
            metricCharge cfg stored input (recordMetric cfg stored input v) ranks r S step)
          fuel 0 Finset.univ =
        ∑ v : Fin n, metricPotential cfg hn stored input (recordMetric cfg stored input v)
          fuel 0 Finset.univ ranks :=
    Branching.potential_sum _ Finset.univ
      (fun v => metricCharge cfg stored input (recordMetric cfg stored input v) ranks) fuel 0 Finset.univ
  simp_rw [hpotential]
  rw [Law.expect_finset_sum]
  calc
    _ ≤ ∑ v : Fin n, ((vertexWeight stored v : ℝ) * recordVisitBudget n accuracy) * (2 * fuel) := by
      apply Finset.sum_le_sum
      intro v _
      exact expected_stopped_records_per_vertex n hn accuracy x delta blockVolume ha hd stored input v
    _ = (∑ v : Fin n, (vertexWeight stored v : ℝ)) *
        (recordVisitBudget n accuracy * (2 * fuel)) := by
      simp only [mul_assoc, Finset.sum_mul]
    _ = _ := by
      have hw : (∑ v : Fin n, (vertexWeight stored v : ℝ)) = n + volume stored.blocks := by
        exact_mod_cast vertexWeight_sum stored
      rw [hw]
      ring

end

end StreamingReachability.Hopset.Reference
