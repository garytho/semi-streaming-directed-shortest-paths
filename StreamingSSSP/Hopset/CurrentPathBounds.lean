module

public import StreamingSSSP.Hopset.PathLocal
public import StreamingSSSP.Hopset.Type3Congruence

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem current_expected_pieces (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) (G : Graph (Fin n))
    (Q : Early.ShortPath G (Reference.distanceScale cfg r)) :
    (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Early.pieceNumber Q (S.filter fun v => coins v = true) (Reference.radii cfg r G owners)
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ))) ≤
      1 + 2 * (Ranks.rate ps r).value *
        ((Early.nearPivots Q (RankPrefix.eligible r known S)
          (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card : ℝ) := by
  let D := Reference.distanceScale cfg r
  let R := Early.searchRadius cfg.k cfg.groups D
  let T := Early.nearRadius cfg.k cfg.groups D
  let E := RankPrefix.eligible r known S
  let fallback : Fin cfg.groups × Fin cfg.shifts := (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  let owner := fun _ : Fin n => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos
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
      RankPrefix.coins_as_marked ps r known S owner fallback
        (fun P owners => (Early.pieceNumber Q P (Reference.radii cfg r G owners) R : ℝ)) hdep
    _ ≤ _ := by
      simp_rw [hradii]
      exact Early.expected_piece_number Q E owner
        (Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos) fallback R T
        (fun v z => (Late.radius_bounds G D cfg.k cfg.groups cfg.shifts cfg.k_pos
          (Reference.distanceScale_pos cfg hnum r) v z).2.le)
        (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg (Ranks.rate ps r).value_le_one

theorem current_expected_related (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (hr : r < ps.length) (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) (G : Graph (Fin n))
    (Q : Early.ShortPath G (Reference.distanceScale cfg r)) (b : ℕ)
    (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hin : ∀ v, (Early.searchIn G v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut G v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hbudget : 2 * (b : ℝ) * b * (Ranks.rate ps r).value ^ 2 ≤ (cfg.k : ℝ) * cfg.groups) :
    (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Early.actualRelatedTotal Q (RankPrefix.eligible r known S) (S.filter fun v => coins v = true)
            (Reference.radii cfg r G owners)
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
            (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ))) ≤
      17 / (Ranks.rate ps r).value := by
  have hc := RankPrefix.current_family ps r hr hprefix known (fun coins =>
    (Reference.ownerLaw n cfg).expect (fun owners =>
      (Early.actualRelatedTotal Q (RankPrefix.eligible r known S) (S.filter fun v => coins v = true)
        (Reference.radii cfg r G owners)
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ)))
  apply le_trans _ (prefix_expected_related cfg r hnum ps hr hprefix known S G Q b hM hp hin hout hbudget)
  exact le_of_eq (by simpa only [CopyHistory.pivots, decide_eq_true_eq] using hc.symm)

theorem current_expected_type3 (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (known : Fin n → Option (Fin r))
    (stored : Implicit.Representation n) (G : Graph (Fin n)) {s t : Fin n}
    (Q : Late.Path stored G s t) (S : Finset (Fin n)) (hS : Q.Inside S)
    (hshort : (Q.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (b : ℕ) (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts)
    (hin : (Early.searchIn (Late.rounded cfg.inputScale (stored.restricted G S)) t
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : (Early.searchOut (Late.rounded cfg.inputScale (stored.restricted G S)) s
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b) :
    (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
      (Reference.ownerLaw n cfg).expect (fun owners =>
        (Late.type3Count Q (Late.rounded cfg.inputScale (stored.restricted G S)) S
          (S.filter fun v => coins v = true)
          (Reference.radii cfg r (Late.rounded cfg.inputScale (stored.restricted G S)) owners)
          (Reference.distanceScale cfg r)
          (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ))) ≤
      48 * b * (Ranks.rate ps r).value / cfg.groups := by
  let H := Late.rounded cfg.inputScale (stored.restricted G S)
  let D := Reference.distanceScale cfg r
  let R := Early.searchRadius cfg.k cfg.groups D
  let E := RankPrefix.eligible r known S
  let fallback : Fin cfg.groups × Fin cfg.shifts := (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  let owner := fun _ : Fin n => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos
  have hradii (xs : List (Fin n × (Fin cfg.groups × Fin cfg.shifts))) :
      Reference.radii cfg r H (Early.Sampling.ownerFor fallback xs) =
        Early.radiusFor (Late.radius H D cfg.k cfg.groups cfg.shifts cfg.k_pos) fallback xs := rfl
  have hdep (P : Finset (Fin n)) (left right : Reference.Owners n cfg)
      (h : ∀ v ∈ P, left v = right v) :
      (Late.type3Count Q H S P (Reference.radii cfg r H left) D R : ℝ) =
        (Late.type3Count Q H S P (Reference.radii cfg r H right) D R : ℝ) :=
    congrArg (fun count : ℕ => (count : ℝ))
      (Late.type3Count_congr_on Q H S P _ _ D R (Reference.radii_congr cfg r H P left right h))
  calc
    _ = (Early.Sampling.marked owner (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
        (Ranks.rate ps r).value_le_one E.toList).expect (fun xs =>
          (Late.type3Count Q H S (Early.Sampling.pivots xs)
            (Reference.radii cfg r H (Early.Sampling.ownerFor fallback xs)) D R : ℝ)) :=
      RankPrefix.coins_as_marked ps r known S owner fallback
        (fun P owners => (Late.type3Count Q H S P (Reference.radii cfg r H owners) D R : ℝ)) hdep
    _ ≤ _ := by
      simp_rw [hradii]
      exact Late.expected_type3 Q cfg.inputScale cfg.inputScale_pos S E hS D
        (Reference.distanceScale_pos cfg hnum r) hshort cfg.k cfg.groups cfg.shifts b
        cfg.k_pos cfg.groups_pos cfg.shifts_pos hgrid hin hout (Ranks.rate ps r).value
        (Ranks.rate ps r).value_nonneg (Ranks.rate ps r).value_le_one

end

end StreamingSSSP.Hopset
