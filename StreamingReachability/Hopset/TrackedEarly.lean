module

public import StreamingReachability.Hopset.CallScheduling

@[expose] public section

namespace StreamingReachability.Hopset.Following.TrackedPath

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

def localView (cfg : Config) (r : ℕ) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :=
  P.path.shortView cfg.inputScale (sets.get P.node) P.inside (Reference.distanceScale cfg r) hshort

def localRadii (cfg : Config) (r : ℕ) (P : TrackedPath stored input sets) (choice : Reference.Choice n cfg) :=
  Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) choice.owners

theorem localRadii_le (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) (choice : Reference.Choice n cfg) (p : Fin n) :
    P.localRadii cfg r choice p ≤
      Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r) :=
  (le_add_of_nonneg_right (Reference.distanceScale_pos cfg hnum r).le).trans
    (Reference.radii_outer_le_search _ cfg hnum r choice.owners p)

def earlyPlan (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (choice : Reference.Choice n cfg)
    (hstop : ¬ Early.stopped (P.localView cfg r hshort) choice.pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))) :
    EarlyPlan P.path cfg.inputScale (sets.get P.node) P.inside (Reference.distanceScale cfg r) hshort
      choice.pivots (P.localRadii cfg r choice)
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) (Reference.distanceScale cfg r) :=
  Classical.choice (exists_early_plan P.path cfg.inputScale (sets.get P.node) P.inside
    (Reference.distanceScale cfg r) hshort choice.pivots (P.localRadii cfg r choice)
    (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) (Reference.distanceScale cfg r)
    (Reference.distanceScale_pos cfg hnum r).le
    (fun p hp hb => hstop ⟨p, hp, hb⟩) (fun p _ => P.localRadii_le cfg r hnum choice p))

theorem earlyPlan_target_mem (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (he : r < cfg.earlyLevel) (choices : Fin ns → Reference.Choice n cfg)
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (hstop : ¬ Early.stopped (P.localView cfg r hshort) (choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)))
    (label : (P.earlyPlan cfg r hnum hshort (choices P.node) hstop).Label) :
    (P.earlyPlan cfg r hnum hshort (choices P.node) hstop).target label ∈
      Batched.geometricChildren cfg r stored input sets choices := by
  have hlocal := type1Target_member (P.localView cfg r hshort) (sets.get P.node)
    (choices P.node).pivots (P.localRadii cfg r (choices P.node))
    (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
    (fun i => P.path.vertices_inside P.inside _ (List.get_mem P.path.vertices i))
    (fun p hp hb => hstop ⟨p, hp, hb⟩)
    (fun p _ => P.localRadii_le cfg r hnum (choices P.node) p) label.val label.property
  have hround : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node)) =
      Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale := rfl
  have hchildren := congrArg (fun H =>
    Geometry.fringes H (sets.get P.node) (choices P.node).pivots (P.localRadii cfg r (choices P.node))
      (Reference.distanceScale cfg r) ++
    Geometry.core H (sets.get P.node) (choices P.node).pivots (P.localRadii cfg r (choices P.node))) hround
  rw [hchildren] at hlocal
  exact early_child_mem cfg r he stored input sets choices P.node _ hlocal

def advance (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    List (TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector) :=
  if hstop : Early.stopped (P.localView cfg r hshort) (choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) then []
  else
    let B := P.earlyPlan cfg r hnum hshort (choices P.node) hstop
    (Finset.univ : Finset B.ChildIndex).toList.map fun i : B.ChildIndex =>
      schedule _ (B.target i.1) (P.earlyPlan_target_mem cfg r hnum he choices hshort hstop i.1)
        (A := cfg.inputScale) (D := Reference.distanceScale cfg r) (by exact B.piece i)

theorem advance_count (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    (P.advance cfg r hnum he choices hshort).length ≤
      Early.pieceNumber (P.localView cfg r hshort) (choices P.node).pivots (P.localRadii cfg r (choices P.node))
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) +
      Late.type3Count P.path (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale)
        (sets.get P.node) (choices P.node).pivots (P.localRadii cfg r (choices P.node))
        (Reference.distanceScale cfg r) (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) := by
  by_cases hs : Early.stopped (P.localView cfg r hshort) (choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
  · simp only [advance, hs, ↓reduceDIte, List.length_nil]
    exact Nat.zero_le _
  · simp only [advance, hs, ↓reduceDIte, List.length_map, Finset.length_toList, Finset.card_univ]
    have h := (P.earlyPlan cfg r hnum hshort (choices P.node) hs).child_count_le
      (fun p hp hb => hs ⟨p, hp, hb⟩) (fun p _ => P.localRadii_le cfg r hnum (choices P.node) p)
    have hround : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node)) =
        Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale := rfl
    have hcut := congrArg (fun H => Late.type3Count P.path H (sets.get P.node) (choices P.node).pivots
      (P.localRadii cfg r (choices P.node)) (Reference.distanceScale cfg r)
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))) hround
    rw [hcut] at h
    exact h

theorem advance_weight (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    Following.weight cfg.inputScale (P.advance cfg r hnum he choices hshort) ≤ P.path.searchWeight cfg.inputScale := by
  by_cases hs : Early.stopped (P.localView cfg r hshort) (choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
  · simp [advance, hs, Following.weight]
  · simp only [advance, hs, ↓reduceDIte, Following.weight, List.map_map, Function.comp_def, schedule,
      Finset.sum_map_toList]
    exact (P.earlyPlan cfg r hnum hshort (choices P.node) hs).piece_weight_sum

end

end StreamingReachability.Hopset.Following.TrackedPath
