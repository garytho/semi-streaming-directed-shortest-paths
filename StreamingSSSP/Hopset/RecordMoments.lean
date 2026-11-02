module

public import StreamingSSSP.Hopset.FreshMoments
public import StreamingSSSP.Hopset.CopyMoments
public import StreamingSSSP.Hopset.MetricBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def incomingCentres (G : Graph (Fin n)) (S : Finset (Fin n)) (v : Fin n) (radius : ℕ) :
    Finset (Fin n) :=
  S.filter fun p => G.dist p v ≤ (radius : Distance)

def outgoingCentres (G : Graph (Fin n)) (S : Finset (Fin n)) (v : Fin n) (radius : ℕ) :
    Finset (Fin n) :=
  S.filter fun p => G.dist v p ≤ (radius : Distance)

def vertexHits (G : Graph (Fin n)) (S : Finset (Fin n)) (v : Fin n)
    (P : Finset (Fin n)) (radius : ℕ) : ℕ :=
  (P ∩ incomingCentres G S v radius).card + (P ∩ outgoingCentres G S v radius).card

theorem within_search_iff (G : Graph (Fin n)) (cfg : Config) (r : ℕ) (u v : Fin n) :
    Early.Within G u v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r)) ↔
      G.dist u v ≤ (cfg.searchRadius r : Distance) := by
  unfold distanceScale
  rw [searchRadius_real cfg r]
  have h := Late.withinFraction_iff_bounded (G.dist u v)
    (cfg.etaMax * cfg.initialNumerator) (cfg.denominatorAt r) (cfg.denominatorAt_pos r)
  simpa only [withinFraction, decide_eq_true_eq, Config.searchRadius, Early.Within] using h.symm

theorem rank_inter_card (S A : Finset (Fin n)) (hAS : A ⊆ S) (j : ℕ) (ranks : Fin n → ℕ) :
    ((CopyHistory.pivots S j ranks ∩ A).card : ℝ) = CopyHistory.visits A j ranks := by
  have he : CopyHistory.pivots S j ranks ∩ A = A.filter (fun v => ranks v = j) := by
    ext v
    simp only [CopyHistory.pivots, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, hr⟩, hv⟩
      exact ⟨hv, hr⟩
    · rintro ⟨hv, hr⟩
      exact ⟨⟨hAS hv, hr⟩, hv⟩
  rw [he]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    CopyHistory.visits]

theorem incoming_card_le (G : Graph (Fin n)) (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (v : Fin n) (b : ℕ)
    (hb : (Early.searchIn G v
      (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b) :
    (incomingCentres G S v (cfg.searchRadius r)).card ≤ b := by
  apply (Finset.card_le_card ?_).trans hb
  intro p hp
  have hnat := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold distanceScale
  rw [searchRadius_real cfg r]
  apply (Late.withinFraction_iff_bounded _ _ _ (cfg.denominatorAt_pos r)).mp
  simpa only [withinFraction, decide_eq_true_eq, Config.searchRadius] using hnat

theorem outgoing_card_le (G : Graph (Fin n)) (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (v : Fin n) (b : ℕ)
    (hb : (Early.searchOut G v
      (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b) :
    (outgoingCentres G S v (cfg.searchRadius r)).card ≤ b := by
  apply (Finset.card_le_card ?_).trans hb
  intro p hp
  have hnat := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  unfold distanceScale
  rw [searchRadius_real cfg r]
  apply (Late.withinFraction_iff_bounded _ _ _ (cfg.denominatorAt_pos r)).mp
  simpa only [withinFraction, decide_eq_true_eq, Config.searchRadius] using hnat

theorem expected_rank_hits (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (v : Fin n) (radius b r j : ℕ)
    (hrj : r ≤ j) (hj : j < ps.length)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hin : (incomingCentres G S v radius).card ≤ b)
    (hout : (outgoingCentres G S v radius).card ≤ b) :
    (CopyHistory.law ps history).expect
        (fun ranks => (vertexHits G S v (CopyHistory.pivots S j ranks) radius : ℝ)) ≤
      2 * (b : ℝ) * (Ranks.rate ps j).value := by
  have he : (fun ranks => (vertexHits G S v (CopyHistory.pivots S j ranks) radius : ℝ)) =
      fun ranks =>
        CopyHistory.visits (incomingCentres G S v radius) j ranks +
          CopyHistory.visits (outgoingCentres G S v radius) j ranks := by
    funext ranks
    simp only [vertexHits, Nat.cast_add]
    rw [rank_inter_card S (incomingCentres G S v radius) (Finset.filter_subset _ _),
      rank_inter_card S (outgoingCentres G S v radius) (Finset.filter_subset _ _)]
  rw [he, Law.expect_add]
  have hi := CopyHistory.expected_visits ps history S (incomingCentres G S v radius)
    (Finset.filter_subset _ _) r j
    hrj hj hc hp hs
  have ho := CopyHistory.expected_visits ps history S (outgoingCentres G S v radius)
    (Finset.filter_subset _ _) r j
    hrj hj hc hp hs
  have hci : ((incomingCentres G S v radius).card : ℝ) ≤ b := by exact_mod_cast hin
  have hco : ((outgoingCentres G S v radius).card : ℝ) ≤ b := by exact_mod_cast hout
  calc
    _ ≤ (Ranks.rate ps j).value * (incomingCentres G S v radius).card +
        (Ranks.rate ps j).value * (outgoingCentres G S v radius).card := add_le_add hi ho
    _ ≤ (Ranks.rate ps j).value * b + (Ranks.rate ps j).value * b :=
      add_le_add (mul_le_mul_of_nonneg_left hci (Ranks.rate ps j).value_nonneg)
        (mul_le_mul_of_nonneg_left hco (Ranks.rate ps j).value_nonneg)
    _ = _ := by ring

theorem inter_card_real (P A : Finset (Fin n)) :
    ((P ∩ A).card : ℝ) = ∑ v ∈ A, if v ∈ P then (1 : ℝ) else 0 := by
  have he : P ∩ A = A.filter (fun v => v ∈ P) := by ext v; simp [and_comm]
  rw [he]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem expected_fresh_hits (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) (G : Graph (Fin n)) (v : Fin n) (radius b : ℕ)
    (hin : (incomingCentres G S v radius).card ≤ b)
    (hout : (outgoingCentres G S v radius).card ≤ b) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).expect
        (fun P => (vertexHits G S v P radius : ℝ)) ≤ 2 * (b : ℝ) * p := by
  have he : (fun P => (vertexHits G S v P radius : ℝ)) = fun P =>
      (∑ u ∈ incomingCentres G S v radius, if u ∈ P then (1 : ℝ) else 0) +
        ∑ u ∈ outgoingCentres G S v radius, if u ∈ P then (1 : ℝ) else 0 := by
    funext P
    simp only [vertexHits, Nat.cast_add, inter_card_real]
  rw [he, Law.expect_add,
    fresh_expected_visits p hp hp1 S (incomingCentres G S v radius) (Finset.filter_subset _ _),
    fresh_expected_visits p hp hp1 S (outgoingCentres G S v radius) (Finset.filter_subset _ _)]
  have hi : ((incomingCentres G S v radius).card : ℝ) ≤ b := by exact_mod_cast hin
  have ho : ((outgoingCentres G S v radius).card : ℝ) ≤ b := by exact_mod_cast hout
  nlinarith

theorem advancePivots_eq (cfg : Config) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ)
    (hr : r + cfg.advance < cfg.earlyLevel) :
    advancePivots cfg r S ranks = CopyHistory.pivots S (r + cfg.advance) ranks := by
  ext v
  simp only [advancePivots, CopyHistory.pivots, Finset.mem_filter, advanceWanted, decide_eq_true_eq]
  constructor
  · rintro ⟨hv, _, he⟩
    exact ⟨hv, he⟩
  · rintro ⟨hv, he⟩
    exact ⟨hv, by omega, he⟩

theorem advancePivots_empty (cfg : Config) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ)
    (hr : cfg.earlyLevel ≤ r + cfg.advance) :
    advancePivots cfg r S ranks = ∅ := by
  ext v
  simp [advancePivots, advanceWanted]
  omega

theorem expected_advance_hits (ps : List Rate) (history : List (CopyHistory.Observation n))
    (cfg : Config) (S : Finset (Fin n)) (G : Graph (Fin n)) (v : Fin n) (radius b r : ℕ)
    (hlen : ps.length = cfg.earlyLevel)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hin : (incomingCentres G S v radius).card ≤ b)
    (hout : (outgoingCentres G S v radius).card ≤ b) :
    (CopyHistory.law ps history).expect
        (fun ranks => (vertexHits G S v (advancePivots cfg r S ranks) radius : ℝ)) ≤
      2 * (b : ℝ) * (Ranks.rate ps (r + cfg.advance)).value := by
  by_cases hj : r + cfg.advance < cfg.earlyLevel
  · have he (ranks : Fin n → ℕ) := advancePivots_eq cfg r S ranks hj
    simp_rw [he]
    exact expected_rank_hits ps history S G v radius b r (r + cfg.advance) (by omega)
      (by omega) hc hp hs hin hout
  · have he (ranks : Fin n → ℕ) := advancePivots_empty cfg r S ranks (by omega)
    simp_rw [he]
    simp only [vertexHits, Finset.empty_inter, Finset.card_empty, Nat.cast_zero,
      zero_add, Law.expect_const]
    have hrate := (Ranks.rate ps (r + cfg.advance)).value_nonneg
    positivity

theorem earlyRate_ball_upper (n : ℕ) (hn : 0 < n) (x r delay : ℕ) :
    (Parameters.ballSize n r : ℝ) * (Ranks.rate (earlyRates n hn x) (r + delay)).value ≤
      200 * (Parameters.k n : ℝ) ^ (delay + 1) * Parameters.ell n := by
  by_cases hj : r + delay < Parameters.threshold n x
  · rw [earlyRates, PivotProfile.lookup n hn (Parameters.k n) (Parameters.ell n)
      (Parameters.threshold n x) (r + delay) hj]
    exact Parameters.future_ball_rate_upper n hn r delay
  · have hlen : (earlyRates n hn x).length ≤ r + delay := by
      simp only [earlyRates, PivotProfile.length_rates]
      omega
    have hnone : (earlyRates n hn x)[r + delay]? = none := List.getElem?_eq_none_iff.mpr hlen
    simp only [Ranks.rate, hnone, Option.getD_none, Rate.zero, Rate.value, Nat.cast_zero,
      Nat.cast_one, zero_div, mul_zero]
    positivity

def recordMetric (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) : Metric n cfg :=
  fun r S ranks choice =>
    let G := Backend.roundedRestricted stored input S cfg.inputScale
    if v ∈ S then vertexWeight stored v *
      (vertexHits G S v choice.pivots (cfg.searchRadius r) +
        if r < cfg.earlyLevel then
          vertexHits G S v (advancePivots cfg r S ranks) (cfg.searchRadius r)
        else 0)
    else 0

theorem recordMetric_outside (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (choice : Choice n cfg) (hv : v ∉ S) :
    recordMetric cfg stored input v r S ranks choice = 0 := by simp [recordMetric, hv]

theorem kernel_record_early (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (he : r < cfg.earlyLevel) (hv : v ∈ S) :
    (kernel cfg hn stored input ranks r S).expect
        (fun step => (recordMetric cfg stored input v r S ranks step.value : ℝ)) =
      (vertexWeight stored v : ℝ) *
        ((vertexHits (Backend.roundedRestricted stored input S cfg.inputScale) S v
            (CopyHistory.pivots S r ranks) (cfg.searchRadius r) : ℝ) +
          (vertexHits (Backend.roundedRestricted stored input S cfg.inputScale) S v
            (advancePivots cfg r S ranks) (cfg.searchRadius r) : ℝ)) := by
  simp only [kernel, choices, pivotLaw, he, ↓reduceIte, Law.expect_map,
    Law.expect_bind, Law.expect_pure, recordMetric, hv, Nat.cast_mul, Nat.cast_add, Law.expect_const]

theorem conditional_early_record_mean (ps : List Rate) (history : List (CopyHistory.Observation n))
    (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n)) (b : ℕ)
    (he : r < cfg.earlyLevel) (hv : v ∈ S) (hlen : ps.length = cfg.earlyLevel)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hin : (incomingCentres (Backend.roundedRestricted stored input S cfg.inputScale)
      S v (cfg.searchRadius r)).card ≤ b)
    (hout : (outgoingCentres (Backend.roundedRestricted stored input S cfg.inputScale)
      S v (cfg.searchRadius r)).card ≤ b) :
    (CopyHistory.law ps history).expect (fun ranks =>
        (kernel cfg hn stored input ranks r S).expect
          (fun step => (recordMetric cfg stored input v r S ranks step.value : ℝ))) ≤
      (vertexWeight stored v : ℝ) *
        (2 * (b : ℝ) * (Ranks.rate ps r).value +
          2 * b * (Ranks.rate ps (r + cfg.advance)).value) := by
  simp_rw [kernel_record_early cfg hn stored input v r S _ he hv]
  rw [Law.expect_mul, Law.expect_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact add_le_add
    (expected_rank_hits ps history S _ v (cfg.searchRadius r) b r r le_rfl (by omega)
      hc hp hs hin hout)
    (expected_advance_hits ps history cfg S _ v (cfg.searchRadius r) b r hlen hc hp hs hin hout)

theorem kernel_record_late (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (he : ¬ r < cfg.earlyLevel) (hl : r < cfg.maximumLevel) (hv : v ∈ S) :
    (kernel cfg hn stored input ranks r S).expect
        (fun step => (recordMetric cfg stored input v r S ranks step.value : ℝ)) =
      (vertexWeight stored v : ℝ) *
        (Law.subset (fun _ : Fin n => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value)
          (fun _ => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg)
          (fun _ => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one) (members S)).expect
            (fun P => (vertexHits (Backend.roundedRestricted stored input S cfg.inputScale)
              S v P (cfg.searchRadius r) : ℝ)) := by
  simp only [kernel, choices, pivotLaw, he, hl, ↓reduceIte, Law.expect_map, Law.expect_bind,
    recordMetric, hv, Nat.cast_mul, Nat.cast_add, Nat.cast_zero, add_zero, Law.expect_const]
  rw [Law.expect_mul]

theorem kernel_record_final (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (he : ¬ r < cfg.earlyLevel) (hl : ¬ r < cfg.maximumLevel) (hv : v ∈ S) :
    (kernel cfg hn stored input ranks r S).expect
        (fun step => (recordMetric cfg stored input v r S ranks step.value : ℝ)) =
      (vertexWeight stored v : ℝ) *
        (vertexHits (Backend.roundedRestricted stored input S cfg.inputScale)
          S v S (cfg.searchRadius r) : ℝ) := by
  simp only [kernel, choices, pivotLaw, he, hl, ↓reduceIte, Law.expect_map, Law.expect_bind,
    Law.expect_pure, recordMetric, hv, Nat.cast_mul, Nat.cast_add, Nat.cast_zero, add_zero,
    Law.expect_const]

end

end StreamingSSSP.Hopset.Reference
