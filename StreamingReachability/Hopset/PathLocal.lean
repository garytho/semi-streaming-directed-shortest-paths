module

public import StreamingReachability.Hopset.EligibilitySampling
public import StreamingReachability.Hopset.LocalEarly
public import StreamingReachability.Hopset.ReferenceOwners
public import StreamingReachability.Early.Congruence

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem prefix_expected_pieces (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (hr : r < ps.length) (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) (G : Graph (Fin n))
    (Q : Early.ShortPath G (Reference.distanceScale cfg r)) :
    (RankPrefix.law ps r known).expect (fun ranks =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Early.pieceNumber Q (CopyHistory.pivots S r ranks) (Reference.radii cfg r G owners)
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ))) ≤
      1 + 2 * (Ranks.rate ps r).value *
        ((Early.nearPivots Q (RankPrefix.eligible r known S)
          (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card : ℝ) := by
  let D := Reference.distanceScale cfg r
  let R := Early.searchRadius cfg.k cfg.groups D
  let E := RankPrefix.eligible r known S
  let fallback : Fin cfg.groups × Fin cfg.shifts := (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  let owner := fun _ : Fin n => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos
  have hD := Reference.distanceScale_pos cfg hnum r
  have hradii (xs : List (Fin n × (Fin cfg.groups × Fin cfg.shifts))) :
      Reference.radii cfg r G (Early.Sampling.ownerFor fallback xs) =
        Early.radiusFor (Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos) fallback xs := rfl
  have hdep (P : Finset (Fin n)) (left right : Reference.Owners n cfg)
      (h : ∀ v ∈ P, left v = right v) :
      (Early.pieceNumber Q P (Reference.radii cfg r G left) R : ℝ) =
        (Early.pieceNumber Q P (Reference.radii cfg r G right) R : ℝ) :=
    congrArg (fun count : ℕ => (count : ℝ))
      (Early.pieceNumber_congr_on Q P _ _ R (Reference.radii_congr cfg r G P left right h))
  calc
    _ = (Early.Sampling.marked owner (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
        (Ranks.rate ps r).value_le_one E.toList).expect (fun xs =>
          (Early.pieceNumber Q (Early.Sampling.pivots xs)
            (Reference.radii cfg r G (Early.Sampling.ownerFor fallback xs)) R : ℝ)) :=
      RankPrefix.choice_as_marked ps r hr hprefix known S owner fallback
        (fun P owners => (Early.pieceNumber Q P (Reference.radii cfg r G owners) R : ℝ)) hdep
    _ ≤ _ := by
      simp_rw [hradii]
      have hR (v : Fin n) (z : Fin cfg.groups × Fin cfg.shifts) :
          Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos v z ≤ R := by
        have h := (Late.radius_bounds G D cfg.k cfg.groups cfg.shifts cfg.k_pos hD v z).2
        dsimp only [R]
        unfold Early.nearRadius Early.searchRadius at *
        linarith
      have h := Early.expected_piece_number Q E owner
        (Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos) fallback R R hR
        (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg (Ranks.rate ps r).value_le_one
      simpa only [E, R, D] using h

theorem prefix_expected_related (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (hr : r < ps.length) (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) (G : Graph (Fin n))
    (Q : Early.ShortPath G (Reference.distanceScale cfg r)) (b : ℕ)
    (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hin : ∀ v, (Early.searchIn G v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut G v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hbudget : 2 * (b : ℝ) * b * (Ranks.rate ps r).value ^ 2 ≤ (cfg.k : ℝ) * cfg.groups) :
    (RankPrefix.law ps r known).expect (fun ranks =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Early.actualRelatedTotal Q (RankPrefix.eligible r known S) (CopyHistory.pivots S r ranks)
            (Reference.radii cfg r G owners)
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
            (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ))) ≤
      17 / (Ranks.rate ps r).value := by
  let D := Reference.distanceScale cfg r
  let R := Early.searchRadius cfg.k cfg.groups D
  let Rmin := Early.nextSearchBound cfg.k cfg.groups D
  let E := RankPrefix.eligible r known S
  let fallback : Fin cfg.groups × Fin cfg.shifts := (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  let owner := fun _ : Fin n => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos
  have hradii (xs : List (Fin n × (Fin cfg.groups × Fin cfg.shifts))) :
      Reference.radii cfg r G (Early.Sampling.ownerFor fallback xs) =
        Early.radiusFor (Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos) fallback xs := rfl
  have hdep (P : Finset (Fin n)) (left right : Reference.Owners n cfg)
      (h : ∀ v ∈ P, left v = right v) :
      (Early.actualRelatedTotal Q E P (Reference.radii cfg r G left) R Rmin : ℝ) =
        (Early.actualRelatedTotal Q E P (Reference.radii cfg r G right) R Rmin : ℝ) :=
    congrArg (fun count : ℕ => (count : ℝ))
      (Early.actualRelatedTotal_congr_on Q E P _ _ R Rmin (Reference.radii_congr cfg r G P left right h))
  calc
    _ = (Early.Sampling.marked owner (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
        (Ranks.rate ps r).value_le_one E.toList).expect (fun xs =>
          (Early.actualRelatedTotal Q E (Early.Sampling.pivots xs)
            (Reference.radii cfg r G (Early.Sampling.ownerFor fallback xs)) R Rmin : ℝ)) :=
      RankPrefix.choice_as_marked ps r hr hprefix known S owner fallback
        (fun P owners => (Early.actualRelatedTotal Q E P (Reference.radii cfg r G owners) R Rmin : ℝ)) hdep
    _ ≤ _ := by
      simp_rw [hradii]
      have h := expected_runtime_related Q E cfg.k cfg.groups cfg.shifts b cfg.k_pos hM cfg.shifts_pos
        (Reference.distanceScale_pos cfg hnum r) hin hout
        (Ranks.rate ps r).value hp (Ranks.rate ps r).value_le_one hbudget
      let F := fun xs : List (Fin n × (Fin cfg.groups × Fin cfg.shifts)) =>
        (Early.actualRelatedTotal Q E (Early.Sampling.pivots xs)
          (Early.radiusFor (Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos) fallback xs) R Rmin : ℝ)
      calc
        _ = (Early.Sampling.marked (fun _ : Fin n =>
            Early.ownerLaw cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)
            (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
            (Ranks.rate ps r).value_le_one E.toList).expect F :=
          Early.Sampling.marked_expect_congr owner _
            (fun v f => (Early.Sampling.ownerLaw_uniformPair_expect cfg.groups cfg.shifts
              cfg.groups_pos cfg.shifts_pos f).symm)
            (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
            (Ranks.rate ps r).value_le_one E.toList F
        _ ≤ _ := by simpa only [F, R, Rmin, D, fallback] using h

end

end StreamingReachability.Hopset
