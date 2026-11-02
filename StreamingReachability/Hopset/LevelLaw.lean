module

public import StreamingReachability.Hopset.LevelCosts
public import StreamingReachability.Hopset.ReferenceOwners

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ}

theorem expected_pivot_observable (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (hselected : ∀ i, selectedVertices targets i = members (P i))
    (observable : List (Pivot n ns) → ℝ) (nodes : Fin ns → Reference.Owners n cfg → ℝ)
    (hpoint : ∀ xs, observable (pivotsFromOwners cfg r sets reply targets 0 xs) =
      ∑ i : Fin ns, nodes i (ownersFromCoordinates cfg targets i (P i) (hselected i) xs))
    (hdepends : ∀ i left right, (∀ v ∈ P i, left v = right v) → nodes i left = nodes i right) :
    (Code.evaluate handler (pivotLoop cfg r sets reply targets 0)).expect
        (fun result => match result with | none => 0 | some pivots => observable pivots) =
      ∑ i : Fin ns, (Reference.ownerLaw n cfg).expect (nodes i) := by
  rw [expect_pivotLoop]
  change (Law.family targets.length (fun _ =>
    Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
    (fun xs => observable (pivotsFromOwners cfg r sets reply targets 0 xs)) = _
  simp_rw [hpoint]
  rw [Law.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact expected_owner_coordinates cfg targets i (P i) (hselected i) (nodes i) (hdepends i)

theorem raw_coordinate_node_views (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (P : Fin ns → Finset (Fin n))
    (hvalid : ∀ target ∈ targets, ValidTarget sets target)
    (hselected : ∀ i, selectedVertices targets i = members (P i))
    (xs : Fin targets.length → Fin cfg.groups × Fin cfg.shifts) :
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    ∀ i, NodeView cfg r (pivotsFromOwners cfg r sets reply targets 0 xs) reply i (sets.get i) (P i)
      (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
      (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
        (ownersFromCoordinates cfg targets i (P i) (hselected i) xs)) := by
  dsimp only
  rw [pivotsFromCoordinates_eq cfg r sets _ targets P hselected xs]
  exact raw_node_views cfg r stored input hn hs hp hsize hnum sets targets P hvalid hselected _

theorem early_children_cost_of_views (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (sets : Vector (Finset (Fin n)) ns) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (P : Fin ns → Finset (Fin n))
    (owners : Fin ns → Reference.Owners n cfg) (hr : r < cfg.earlyLevel)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i)
      (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
      (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (owners i)))
    (f : Finset (Fin n) → ℝ) :
    (((earlyFringes cfg r sets pivots reply ++ earlyCore cfg r sets pivots reply).map f).sum) =
      ∑ i : Fin ns, ((Reference.children cfg stored input r (sets.get i) ⟨P i, owners i⟩).map f).sum := by
  simp only [List.map_append, List.sum_append]
  rw [earlyFringes_cost cfg r sets pivots reply P _ _ hview f,
    earlyCore_cost cfg r sets pivots reply P _ _ hview f, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Reference.children, hr, ↓reduceIte, List.map_append, List.sum_append]

theorem expected_early_children (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (rank : Vector ℕ n) (hr : r < cfg.earlyLevel)
    (f : Finset (Fin n) → ℝ) :
    let targets := earlyTargets cfg r rank sets
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    (Code.evaluate handler (pivotLoop cfg r sets reply targets 0)).expect
        (fun result => match result with
          | none => 0
          | some pivots =>
            ((earlyFringes cfg r sets pivots reply ++ earlyCore cfg r sets pivots reply).map f).sum) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input (fun v => rank.get v) r (sets.get i)).expect
        (fun step => (step.children.map f).sum) := by
  let targets := earlyTargets cfg r rank sets
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  let P := fun i => CopyHistory.pivots (sets.get i) r (fun v => rank.get v)
  have hselected (i : Fin ns) : selectedVertices targets i = members (P i) :=
    earlyTargets_selected cfg r rank sets i hr
  dsimp only
  rw [expect_pivotLoop]
  change (Law.family targets.length (fun _ =>
    Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
    (fun xs => ((earlyFringes cfg r sets (pivotsFromOwners cfg r sets reply targets 0 xs) reply ++
      earlyCore cfg r sets (pivotsFromOwners cfg r sets reply targets 0 xs) reply).map f).sum) = _
  have hpoint (xs : Fin targets.length → Fin cfg.groups × Fin cfg.shifts) :
      ((earlyFringes cfg r sets (pivotsFromOwners cfg r sets reply targets 0 xs) reply ++
        earlyCore cfg r sets (pivotsFromOwners cfg r sets reply targets 0 xs) reply).map f).sum =
        ∑ i : Fin ns,
          ((Reference.children cfg stored input r (sets.get i)
            ⟨P i, ownersFromCoordinates cfg targets i (P i) (hselected i) xs⟩).map f).sum :=
    early_children_cost_of_views cfg r stored input sets _ reply P _ hr
      (raw_coordinate_node_views cfg r stored input hn hs hp hsize hnum sets targets P
        (earlyTargets_inside cfg r rank sets) hselected xs) f
  simp_rw [hpoint]
  rw [Law.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hdepends (left right : Reference.Owners n cfg) (he : ∀ v ∈ P i, left v = right v) :
      ((Reference.children cfg stored input r (sets.get i) ⟨P i, left⟩).map f).sum =
        ((Reference.children cfg stored input r (sets.get i) ⟨P i, right⟩).map f).sum := by
    rw [Reference.children_owners_congr cfg stored input r (sets.get i) (P i) left right he]
  rw [expected_owner_coordinates cfg targets i (P i) (hselected i)
    (fun owners => ((Reference.children cfg stored input r (sets.get i) ⟨P i, owners⟩).map f).sum)
    hdepends]
  simp only [Reference.kernel, Law.expect_map, Reference.choices, Reference.pivotLaw, hr,
    ↓reduceIte, Law.expect_bind, Law.expect_pure, P]

end

end StreamingReachability.Hopset
