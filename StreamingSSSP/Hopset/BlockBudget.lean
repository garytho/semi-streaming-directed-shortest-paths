module

public import StreamingSSSP.Hopset.RecordBudget

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def lateVisitMetric (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) : Metric n cfg :=
  fun r S _ranks choice =>
    if r < cfg.earlyLevel then 0 else
      if v ∈ S then
        vertexHits (Backend.roundedRestricted stored input S cfg.inputScale)
          S v choice.pivots (cfg.searchRadius r)
      else 0

def blockMetric (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) : Metric n cfg :=
  fun r S _ranks choice =>
    ((blocks cfg stored input r S choice).filter fun B => decide (v ∈ B)).length

theorem blockMetric_outside (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (choice : Choice n cfg) (hv : v ∉ S) :
    blockMetric cfg stored input v r S ranks choice = 0 := by
  by_cases he : r < cfg.earlyLevel <;> simp [blockMetric, blocks, he, hv]

theorem blockMetric_le_lateVisits (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (v : Fin n) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ) (choice : Choice n cfg)
    (hP : choice.pivots ⊆ S) :
    blockMetric cfg stored input v r S ranks choice ≤ lateVisitMetric cfg stored input v r S ranks choice := by
  by_cases he : r < cfg.earlyLevel
  · simp [blockMetric, blocks, lateVisitMetric, he]
  · by_cases hv : v ∈ S
    · let G := Backend.roundedRestricted stored input S cfg.inputScale
      let rho := radii cfg r G choice.owners
      let B := fun p => S ∩ Early.bothBall G p (rho p + distanceScale cfg r)
      let A := choice.pivots.filter fun p => v ∈ B p
      have hcount (xs : List (Fin n)) :
          ((xs.map B).filter fun T => decide (v ∈ T)).length =
            (xs.filter fun p => decide (v ∈ B p)).length := by
        induction xs with
        | nil => rfl
        | cons p xs ih =>
            by_cases h : v ∈ B p <;> simp [h, ih]
      have hcard : ((members choice.pivots).filter fun p => decide (v ∈ B p)).length = A.card := by
        rw [← List.toFinset_card_of_nodup ((members_nodup choice.pivots).filter _)]
        congr 1
        ext p
        simp [A]
      have hsub : A ⊆ (choice.pivots ∩ incomingCentres G S v (cfg.searchRadius r)) ∪
          (choice.pivots ∩ outgoingCentres G S v (cfg.searchRadius r)) := by
        intro p hp
        obtain ⟨hpP, hpB⟩ := Finset.mem_filter.mp hp
        have hpS := hP hpP
        have hball := (Early.mem_bothBall G p v _).mp (Finset.mem_inter.mp hpB).2
        have houter := radii_outer_le_search G cfg hnum r choice.owners p
        rcases hball with hin | hout
        · apply Finset.mem_union.mpr
          apply Or.inl
          apply Finset.mem_inter.mpr
          refine ⟨hpP, Finset.mem_filter.mpr ⟨hpS, ?_⟩⟩
          exact (within_search_iff G cfg r p v).mp (Early.within_mono hin houter)
        · apply Finset.mem_union.mpr
          apply Or.inr
          apply Finset.mem_inter.mpr
          refine ⟨hpP, Finset.mem_filter.mpr ⟨hpS, ?_⟩⟩
          exact (within_search_iff G cfg r v p).mp (Early.within_mono hout houter)
      simp only [blockMetric, blocks, lateVisitMetric, he, hv, ↓reduceIte]
      change ((members choice.pivots).map B |>.filter (fun T => decide (v ∈ T))).length ≤ _
      rw [hcount, hcard]
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    · rw [blockMetric_outside cfg stored input v r S ranks choice hv]
      simp [lateVisitMetric, he, hv]

theorem lateVisitMetric_outside (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (choice : Choice n cfg) (hv : v ∉ S) :
    lateVisitMetric cfg stored input v r S ranks choice = 0 := by
  by_cases he : r < cfg.earlyLevel <;> simp [lateVisitMetric, hv, he]

theorem calibrated_late_visit_mean (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (v : Fin n) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ)
    (hballs : BallsGood (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input r S)
    (hv : v ∈ S) :
    (kernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks r S).expect
        (fun step => (lateVisitMetric (Parameters.configuration n accuracy x delta blockVolume ha hd)
          stored input v r S ranks step.value : ℝ)) ≤
      400 * (Parameters.k n : ℝ) * Parameters.ell n := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let b := Parameters.ballSize n r
  have hin : (incomingCentres G S v (cfg.searchRadius r)).card ≤ b :=
    incoming_card_le G cfg r S v b (hballs v hv).1
  have hout : (outgoingCentres G S v (cfg.searchRadius r)).card ≤ b :=
    outgoing_card_le G cfg r S v b (hballs v hv).2
  have hrate := Parameters.ball_rate_upper n hn r
  change (kernel cfg hn stored input ranks r S).expect
    (fun step => (lateVisitMetric cfg stored input v r S ranks step.value : ℝ)) ≤ _
  by_cases he : r < cfg.earlyLevel
  · have hfn : (fun step : Branching.Step (Finset (Fin n)) (Choice n cfg) =>
        (lateVisitMetric cfg stored input v r S ranks step.value : ℝ)) = fun _ => 0 := by
      funext step
      simp [lateVisitMetric, he]
    rw [hfn, Law.expect_const]
    positivity
  · by_cases hl : r < cfg.maximumLevel
    · simp only [kernel, choices, pivotLaw, he, hl, ↓reduceIte, Law.expect_map, Law.expect_bind,
        lateVisitMetric, hv, Law.expect_const]
      apply (expected_fresh_hits (PivotProfile.rate n hn cfg.k cfg.logarithm r).value
        (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg
        (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one S G v (cfg.searchRadius r) b hin hout).trans
      change 2 * (Parameters.ballSize n r : ℝ) *
        (PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r).value ≤ _
      nlinarith
    · simp only [kernel, choices, pivotLaw, he, hl, ↓reduceIte, Law.expect_map, Law.expect_bind,
        Law.expect_pure, lateVisitMetric, hv, Law.expect_const]
      have h : (vertexHits G S v S (cfg.searchRadius r) : ℝ) ≤ 2 * b := by
        exact_mod_cast vertexHits_le G S S v (cfg.searchRadius r) b hin hout
      have hone := Parameters.rate_one_after_max n hn r (by change cfg.maximumLevel ≤ r; omega)
      rw [hone, mul_one] at hrate
      apply h.trans
      dsimp only [b]
      nlinarith

theorem expected_stopped_late_visits_per_vertex (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (v : Fin n) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => metricPotential (Parameters.configuration n accuracy x delta blockVolume ha hd) hn
          stored input (lateVisitMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
          (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) ≤
      (400 * (Parameters.k n : ℝ) * Parameters.ell n) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
  apply expected_calibrated_metric n hn accuracy x delta blockVolume ha hd stored input _ v
    (400 * (Parameters.k n : ℝ) * Parameters.ell n) (by positivity)
    (lateVisitMetric_outside _ _ _ v)
  intro r S history _ _ hg hv
  rw [CopyHistory.moment]
  apply mul_le_mul_of_nonneg_left _ (CopyHistory.mass_nonneg _ _)
  apply (Law.expect_mono _ ?_).trans_eq (Law.expect_const _ _)
  intro ranks
  exact calibrated_late_visit_mean n hn accuracy x delta blockVolume ha hd stored input v r S ranks hg hv

theorem expected_stopped_block_copies_per_vertex (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (v : Fin n) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => metricPotential (Parameters.configuration n accuracy x delta blockVolume ha hd) hn
          stored input (blockMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
          (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) ≤
      (400 * (Parameters.k n : ℝ) * Parameters.ell n) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  apply expected_calibrated_metric n hn accuracy x delta blockVolume ha hd stored input _ v
    (400 * (Parameters.k n : ℝ) * Parameters.ell n) (by positivity)
    (blockMetric_outside _ _ _ v)
  intro r S history _ _ hg hv
  rw [CopyHistory.moment]
  apply mul_le_mul_of_nonneg_left _ (CopyHistory.mass_nonneg _ _)
  apply (Law.expect_mono _ ?_).trans_eq (Law.expect_const _ _)
  intro ranks
  have hdom :
      (kernel cfg hn stored input ranks r S).expect
          (fun step => (blockMetric cfg stored input v r S ranks step.value : ℝ)) ≤
        (kernel cfg hn stored input ranks r S).expect
          (fun step => (lateVisitMetric cfg stored input v r S ranks step.value : ℝ)) := by
    apply Early.Sampling.expect_mono_on
    refine Early.Sampling.holds_mono (kernel_pivots_subset cfg hn stored input ranks r S) ?_
    intro step hP
    exact_mod_cast blockMetric_le_lateVisits cfg stored input hnum v r S ranks step.value hP
  exact hdom.trans
    (calibrated_late_visit_mean n hn accuracy x delta blockVolume ha hd stored input v r S ranks hg hv)

theorem blockCounts_sum (bs : List (Finset (Fin n))) :
    (∑ v : Fin n, (bs.filter fun B => decide (v ∈ B)).length) = volume bs := by
  let R : Implicit.Representation n := ⟨[], bs⟩
  have h := vertexWeight_sum R
  change (∑ v : Fin n, (1 + (bs.filter fun B => decide (v ∈ B)).length)) = n + volume bs at h
  rw [Finset.sum_add_distrib] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact Nat.add_left_cancel h

theorem blockCharge_eq (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (r : ℕ) (S : Finset (Fin n))
    (step : Branching.Step (Finset (Fin n)) (Choice n cfg)) :
    (∑ v : Fin n, metricCharge cfg stored input (blockMetric cfg stored input v) ranks r S step) =
      if BallsGood cfg stored input r S then volume (blocks cfg stored input r S step.value) else 0 := by
  by_cases hg : BallsGood cfg stored input r S
  · simp only [metricCharge, hg, ↓reduceIte, blockMetric]
    exact blockCounts_sum _
  · simp only [metricCharge, hg, ↓reduceIte, Finset.sum_const_zero]

theorem expected_stopped_block_volume (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    ((Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).bind fun ranks =>
        Branching.runCost
          (stoppedKernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks)
          (fun r S step => ∑ v : Fin n,
            metricCharge (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input
              (blockMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
              ranks r S step)
          (Parameters.maximumLevel n + 1) 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤
      (400 * (Parameters.k n : ℝ) * Parameters.ell n) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) * n := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let fuel := Parameters.maximumLevel n + 1
  change ((Law.family n (fun _ => Ranks.firstHit ps)).bind fun ranks =>
    Branching.runCost (stoppedKernel cfg hn stored input ranks)
      (fun r S step => ∑ v : Fin n,
        metricCharge cfg stored input (blockMetric cfg stored input v) ranks r S step)
      fuel 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤ _
  rw [Law.expect_bind]
  simp_rw [Branching.expected_breadth_first_cost]
  simp only [List.map_singleton, List.sum_singleton]
  have hpotential (ranks : Fin n → ℕ) :
      Branching.potential (stoppedKernel cfg hn stored input ranks)
          (fun r S step => ∑ v : Fin n,
            metricCharge cfg stored input (blockMetric cfg stored input v) ranks r S step)
          fuel 0 Finset.univ =
        ∑ v : Fin n, metricPotential cfg hn stored input (blockMetric cfg stored input v)
          fuel 0 Finset.univ ranks :=
    Branching.potential_sum _ Finset.univ
      (fun v => metricCharge cfg stored input (blockMetric cfg stored input v) ranks) fuel 0 Finset.univ
  simp_rw [hpotential]
  rw [Law.expect_finset_sum]
  calc
    _ ≤ ∑ _v : Fin n, (400 * (Parameters.k n : ℝ) * Parameters.ell n) * (2 * fuel) := by
      apply Finset.sum_le_sum
      intro v _
      exact expected_stopped_block_copies_per_vertex n hn accuracy x delta blockVolume ha hd stored input v
    _ = _ := by simp [fuel]; ring

end

end StreamingSSSP.Hopset.Reference
