module

public import StreamingSSSP.Hopset.TrackedEarly
public import StreamingSSSP.Hopset.EligibilityNext
public import StreamingSSSP.Hopset.PathCalibration

@[expose] public section

namespace StreamingSSSP.Hopset.Following.TrackedPath

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

theorem advance_related (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (known : Fin n → Option (Fin r)) (coins : Fin n → Bool)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (hPi : (choices P.node).pivots = (sets.get P.node).filter (fun v => coins v = true)) (b : ℕ)
    (hin : ∀ v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b) :
    Following.related cfg (r + 1) (fun v => RankPrefix.nextKnown r (known v) (coins v))
        (P.advance cfg r hnum he choices hshort) ≤
      Early.actualRelatedTotal (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
        (choices P.node).pivots (P.localRadii cfg r (choices P.node))
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r)) +
      2 * b * Late.type3Count P.path (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale)
        (sets.get P.node) (choices P.node).pivots (P.localRadii cfg r (choices P.node))
        (Reference.distanceScale cfg r) (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) := by
  by_cases hs : Early.stopped (P.localView cfg r hshort) (choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
  · simp only [advance, hs, ↓reduceDIte, Following.related, List.map_nil, List.sum_nil]
    exact Nat.zero_le _
  · let B := P.earlyPlan cfg r hnum hshort (choices P.node) hs
    let nextKnown := fun v => RankPrefix.nextKnown r (known v) (coins v)
    let E' := fun label : B.Label => RankPrefix.eligible (r + 1) nextKnown (B.target label)
    have hEX (label : B.Label) : E' label ⊆ B.target label := Finset.filter_subset _ _
    have hE (label : B.Label) : E' label ⊆ RankPrefix.eligible r known (sets.get P.node) :=
      RankPrefix.eligible_next_subset r known coins _ _ (type1Target_subset _ _ _ _ _ _)
    have hP (label : B.Label) (w : Fin n) (hw : w ∈ E' label) : w ∉ (choices P.node).pivots := by
      rw [hPi]
      exact RankPrefix.eligible_next_not_pivot r known coins (B.target label) (sets.get P.node) w hw
    have hbudget : (P.path.searchWeight cfg.inputScale : ℝ) +
        Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg (r + 1)) ≤
          Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r) := by
      have hn := Reference.next_near_budget cfg r
      linarith
    have hb := B.related_type3_le cfg.inputScale_pos (RankPrefix.eligible r known (sets.get P.node)) E'
      (Early.nextSearchBound cfg.k cfg.groups (Reference.distanceScale cfg r))
      (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg (r + 1))) b
      (fun p hp h => hs ⟨p, hp, h⟩) (fun p _ => P.localRadii_le cfg r hnum (choices P.node) p)
      (Reference.next_near_separated cfg r) hbudget hin hout hEX hE hP
    have hrelated :
        Following.related cfg (r + 1) nextKnown (P.advance cfg r hnum he choices hshort) =
          B.related E' (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg (r + 1))) := by
      simp only [advance, hs, ↓reduceDIte, Following.related, List.map_map, Function.comp_def,
        Finset.sum_map_toList, EarlyPlan.related]
      apply Finset.sum_congr rfl
      intro i _
      have hset := schedule_set
        (Batched.geometricChildren cfg r stored input sets choices) (B.target i.1)
        (P.earlyPlan_target_mem cfg r hnum he choices hshort hs i.1)
        (A := cfg.inputScale) (D := Reference.distanceScale cfg r) (by exact B.piece i)
      dsimp only [B] at hset
      rw [hset]
      rfl
    rw [hrelated]
    have hround : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node)) =
        Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale := rfl
    have hcut := congrArg (fun H => Late.type3Count P.path H (sets.get P.node) (choices P.node).pivots
      (P.localRadii cfg r (choices P.node)) (Reference.distanceScale cfg r)
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))) hround
    rw [hcut] at hb
    exact hb

end

end StreamingSSSP.Hopset.Following.TrackedPath
