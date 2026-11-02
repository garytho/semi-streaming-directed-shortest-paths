module

public import StreamingReachability.Hopset.CurrentDraw

@[expose] public section

namespace StreamingReachability.Hopset.Following.TrackedPath

open scoped Classical

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

theorem expected_piece_statistic (cfg : Config) (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r))
    (hnum : 0 < cfg.initialNumerator) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      let choice := Batched.currentChoices cfg sets sample.1 sample.2 P.node
      (Early.pieceNumber (P.localView cfg r hshort) choice.pivots (P.localRadii cfg r choice)
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ)) ≤
      1 + 2 * (Ranks.rate ps r).value * Following.related cfg r known [P] := by
  let H := Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node))
  let R := Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)
  calc
    _ = (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Early.pieceNumber (P.localView cfg r hshort) ((sets.get P.node).filter fun v => coins v = true)
            (Reference.radii cfg r H owners) R : ℝ))) :=
      P.currentDraw_path_local cfg ps r known
        (fun pivots rho => (Early.pieceNumber (P.localView cfg r hshort) pivots rho R : ℝ))
    _ ≤ _ := by
      have h := current_expected_pieces cfg r hnum ps known (sets.get P.node) H (P.localView cfg r hshort)
      rw [P.localView_near cfg r known hshort] at h
      exact h

theorem expected_cut_statistic (cfg : Config) (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r))
    (hnum : 0 < cfg.initialNumerator) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts)
    (hin : ∀ v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      let choice := Batched.currentChoices cfg sets sample.1 sample.2 P.node
      (Late.type3Count P.path (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale)
        (sets.get P.node) choice.pivots (P.localRadii cfg r choice) (Reference.distanceScale cfg r)
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ)) ≤
      48 * b * (Ranks.rate ps r).value / cfg.groups := by
  let H := Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node))
  let D := Reference.distanceScale cfg r
  let R := Early.searchRadius cfg.k cfg.groups D
  calc
    _ = (currentDraw cfg ps r known ns).expect (fun sample =>
        let choice := Batched.currentChoices cfg sets sample.1 sample.2 P.node
        (Late.type3Count P.path H (sets.get P.node) choice.pivots (P.localRadii cfg r choice) D R : ℝ)) := by
      apply congrArg (currentDraw cfg ps r known ns).expect
      funext sample
      rfl
    _ = (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Late.type3Count P.path H (sets.get P.node) ((sets.get P.node).filter fun v => coins v = true)
            (Reference.radii cfg r H owners) D R : ℝ))) :=
      P.currentDraw_path_local cfg ps r known
        (fun pivots rho => (Late.type3Count P.path H (sets.get P.node) pivots rho D R : ℝ))
    _ ≤ _ := current_expected_type3 cfg r hnum ps known stored (StoredEdges.graphOfEdges input)
      P.path (sets.get P.node) P.inside hshort b hgrid (hin P.target) (hout P.source)

theorem expected_related_statistic (cfg : Config) (ps : List Rate) (r : ℕ)
    (known : Fin n → Option (Fin r)) (hr : r < ps.length)
    (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hnum : 0 < cfg.initialNumerator) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hin : ∀ v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hbudget : 2 * (b : ℝ) * b * (Ranks.rate ps r).value ^ 2 ≤ (cfg.k : ℝ) * cfg.groups) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      let choice := Batched.currentChoices cfg sets sample.1 sample.2 P.node
      (Early.actualRelatedTotal (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
        choice.pivots (P.localRadii cfg r choice)
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ)) ≤
      17 / (Ranks.rate ps r).value := by
  let H := Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node))
  let R := Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)
  let Rmin := Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)
  calc
    _ = (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          (Early.actualRelatedTotal (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
            ((sets.get P.node).filter fun v => coins v = true) (Reference.radii cfg r H owners) R Rmin : ℝ))) :=
      P.currentDraw_path_local cfg ps r known (fun pivots rho =>
        (Early.actualRelatedTotal (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
          pivots rho R Rmin : ℝ))
    _ ≤ _ := current_expected_related cfg r hnum ps hr hprefix known (sets.get P.node) H
      (P.localView cfg r hshort) b hM hp hin hout hbudget

theorem expected_advance_count (cfg : Config) (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r))
    (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts)
    (hin : ∀ v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      ((P.advance cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) hshort).length : ℝ)) ≤
      1 + 2 * (Ranks.rate ps r).value * Following.related cfg r known [P] +
        48 * b * (Ranks.rate ps r).value / cfg.groups := by
  have hm := Law.expect_mono (currentDraw cfg ps r known ns) (fun sample =>
    (show (((P.advance cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) hshort).length : ℕ) : ℝ) ≤
      (Early.pieceNumber (P.localView cfg r hshort)
        (Batched.currentChoices cfg sets sample.1 sample.2 P.node).pivots
        (P.localRadii cfg r (Batched.currentChoices cfg sets sample.1 sample.2 P.node))
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ) +
      (Late.type3Count P.path (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale)
        (sets.get P.node) (Batched.currentChoices cfg sets sample.1 sample.2 P.node).pivots
        (P.localRadii cfg r (Batched.currentChoices cfg sets sample.1 sample.2 P.node))
        (Reference.distanceScale cfg r) (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ)
      from by exact_mod_cast P.advance_count cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) hshort))
  rw [Law.expect_add] at hm
  exact hm.trans (add_le_add (P.expected_piece_statistic cfg ps r known hnum hshort)
    (P.expected_cut_statistic cfg ps r known hnum hshort b hgrid hin hout))

theorem expected_advance_related (cfg : Config) (ps : List Rate) (r : ℕ)
    (known : Fin n → Option (Fin r)) (hr : r < ps.length)
    (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts) (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hin : ∀ v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hbudget : 2 * (b : ℝ) * b * (Ranks.rate ps r).value ^ 2 ≤ (cfg.k : ℝ) * cfg.groups) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      (Following.related cfg (r + 1) (fun v => RankPrefix.nextKnown r (known v) (sample.1 v))
        (P.advance cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) hshort) : ℝ)) ≤
      17 / (Ranks.rate ps r).value + 2 * b * (48 * b * (Ranks.rate ps r).value / cfg.groups) := by
  have hm := Law.expect_mono (currentDraw cfg ps r known ns) (fun sample =>
    (show (Following.related cfg (r + 1) (fun v => RankPrefix.nextKnown r (known v) (sample.1 v))
      (P.advance cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) hshort) : ℝ) ≤
      (Early.actualRelatedTotal (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
        (Batched.currentChoices cfg sets sample.1 sample.2 P.node).pivots
        (P.localRadii cfg r (Batched.currentChoices cfg sets sample.1 sample.2 P.node))
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ) +
      2 * (b : ℝ) * (Late.type3Count P.path (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale)
        (sets.get P.node) (Batched.currentChoices cfg sets sample.1 sample.2 P.node).pivots
        (P.localRadii cfg r (Batched.currentChoices cfg sets sample.1 sample.2 P.node))
        (Reference.distanceScale cfg r) (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) : ℝ)
      from by
        exact_mod_cast P.advance_related cfg r hnum he known sample.1
          (Batched.currentChoices cfg sets sample.1 sample.2) hshort rfl b hin hout))
  rw [Law.expect_add, Law.expect_mul] at hm
  exact hm.trans (add_le_add (P.expected_related_statistic cfg ps r known hr hprefix hnum hshort b hM hp hin hout hbudget)
    (mul_le_mul_of_nonneg_left (P.expected_cut_statistic cfg ps r known hnum hshort b hgrid hin hout) (by positivity)))

theorem expected_advance_related_le (cfg : Config) (ps : List Rate) (r : ℕ)
    (known : Fin n → Option (Fin r)) (hr : r < ps.length)
    (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts) (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hin : ∀ v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hbudget : 96 * (b : ℝ) ^ 2 * (Ranks.rate ps r).value ^ 2 ≤ cfg.groups) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      (Following.related cfg (r + 1) (fun v => RankPrefix.nextKnown r (known v) (sample.1 v))
        (P.advance cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) hshort) : ℝ)) ≤
      18 / (Ranks.rate ps r).value := by
  have hk : (1 : ℝ) ≤ cfg.k := by exact_mod_cast cfg.k_pos
  have hM0 : (0 : ℝ) < cfg.groups := by exact_mod_cast cfg.groups_pos
  have hprod : 0 ≤ (b : ℝ) ^ 2 * (Ranks.rate ps r).value ^ 2 := by positivity
  have hbudget' : 2 * (b : ℝ) * b * (Ranks.rate ps r).value ^ 2 ≤ (cfg.k : ℝ) * cfg.groups := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hM0.le]
  have hm := P.expected_advance_related cfg ps r known hr hprefix hnum he hshort b hgrid hM hp hin hout hbudget'
  have hextra : 2 * (b : ℝ) * (48 * b * (Ranks.rate ps r).value / cfg.groups) ≤ 1 / (Ranks.rate ps r).value := by
    rw [show 2 * (b : ℝ) * (48 * b * (Ranks.rate ps r).value / cfg.groups) =
      (96 * (b : ℝ) ^ 2 * (Ranks.rate ps r).value) / cfg.groups by ring]
    apply (div_le_div_iff₀ hM0 hp).mpr
    nlinarith
  calc
    _ ≤ _ := hm
    _ ≤ 17 / (Ranks.rate ps r).value + 1 / (Ranks.rate ps r).value := add_le_add le_rfl hextra
    _ = _ := by ring

end

end StreamingReachability.Hopset.Following.TrackedPath
