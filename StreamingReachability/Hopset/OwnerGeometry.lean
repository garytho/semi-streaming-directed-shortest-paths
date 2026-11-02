module

public import StreamingReachability.Hopset.PivotGeometry
public import StreamingReachability.Hopset.TargetFacts

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem pivotsFromOwners_mem (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (offset : ℕ) :
    ∀ (owners : Fin targets.length → Fin cfg.groups × Fin cfg.shifts)
      (p : Pivot n ns), p ∈ pivotsFromOwners cfg r sets reply targets offset owners →
        ∃ j : Fin targets.length, (targets.get j).kind = .pivot ∧
          p = sampledPivot cfg r sets reply (targets.get j) (offset + j.val) (owners j) := by
  induction targets generalizing offset with
  | nil => intro owners p hp; simp [pivotsFromOwners] at hp
  | cons target targets ih =>
      intro owners p hp
      by_cases hk : target.kind = .pivot
      · simp only [pivotsFromOwners, hk, ↓reduceIte, List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨⟨0, by simp⟩, hk, ?_⟩
          simp [sampledPivot]
        · obtain ⟨j, hj, he⟩ := ih (offset + 1) (fun i => owners i.succ) p hp
          refine ⟨j.succ, hj, ?_⟩
          change p = sampledPivot cfg r sets reply (targets.get j)
            (offset + (j.val + 1)) (owners j.succ)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he
      · simp only [pivotsFromOwners, hk, ↓reduceIte] at hp
        obtain ⟨j, hj, he⟩ := ih (offset + 1) (fun i => owners i.succ) p hp
        refine ⟨j.succ, hj, ?_⟩
        change p = sampledPivot cfg r sets reply (targets.get j)
          (offset + (j.val + 1)) (owners j.succ)
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

theorem pivotsFromOwners_vertices (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (offset : ℕ) :
    ∀ (owners : Fin targets.length → Fin cfg.groups × Fin cfg.shifts) (i : Fin ns),
      (((pivotsFromOwners cfg r sets reply targets offset owners).filter
          fun p => decide (p.setId = i)).map Pivot.vertex) = selectedVertices targets i := by
  induction targets generalizing offset with
  | nil => intro owners i; rfl
  | cons target targets ih =>
      intro owners i
      by_cases hk : target.kind = .pivot <;> by_cases hi : target.setId = i <;>
        simp [pivotsFromOwners, selectedVertices, hk, hi, ih]

theorem pivotsFromOwners_congr (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (offset : ℕ) :
    ∀ (left right : Fin targets.length → Fin cfg.groups × Fin cfg.shifts),
      (∀ j, (targets.get j).kind = .pivot → left j = right j) →
        pivotsFromOwners cfg r sets reply targets offset left =
          pivotsFromOwners cfg r sets reply targets offset right := by
  induction targets generalizing offset with
  | nil => intro left right h; rfl
  | cons target targets ih =>
      intro left right h
      have htail := ih (offset + 1) (fun j => left j.succ) (fun j => right j.succ)
        (fun j hj => h j.succ hj)
      by_cases hk : target.kind = .pivot
      · have hhead : left 0 = right 0 := h 0 (by simpa using hk)
        simp only [pivotsFromOwners, hk, ↓reduceIte, hhead, htail]
      · simp only [pivotsFromOwners, hk, ↓reduceIte, htail]

def ownersForTargets (cfg : Config) (targets : List (Target n ns))
    (owners : Fin ns → Reference.Owners n cfg) :
    Fin targets.length → Fin cfg.groups × Fin cfg.shifts :=
  fun j => owners (targets.get j).setId (targets.get j).vertex

theorem raw_assigned_pivot_geometry (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (hvalid : ∀ target ∈ targets, ValidTarget sets target)
    (owners : Fin ns → Reference.Owners n cfg) :
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    ∀ p ∈ pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets owners),
      let S := sets.get p.setId
      let G := Backend.roundedRestricted stored input S cfg.inputScale
      let D := Reference.distanceScale cfg r
      let rho := Reference.radii cfg r G (owners p.setId) p.vertex
      (∀ v ∈ S,
        (outFlag cfg r p reply v = true ↔ Early.Within G p.vertex v rho) ∧
        (inFlag cfg r p reply v = true ↔ Early.Within G v p.vertex rho)) ∧
      fringe cfg r p.eta p.shift S reply p.forward p.backward =
        S ∩ Early.fringe G p.vertex rho D ∧
      bothBall cfg r (p.eta + 1) p.shift S reply p.forward p.backward =
        S ∩ Early.bothBall G p.vertex (rho + D) := by
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  dsimp only
  intro p hpivot
  obtain ⟨j, hkind, he⟩ := pivotsFromOwners_mem cfg r sets reply targets 0
    (ownersForTargets cfg targets owners) p hpivot
  have ht : targets[j.val]? = some (targets.get j) := by simp
  have hg := raw_pivot_geometry cfg r stored input hn hs hp hsize hnum sets targets j.val
    (targets.get j) ht hkind (hvalid _ (List.get_mem targets j))
    (ownersForTargets cfg targets owners j)
  subst p
  simpa only [Nat.zero_add, sampledPivot, ownersForTargets, Reference.radii] using hg

def ownersFromCoordinates (cfg : Config) (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (xs : Fin targets.length → Fin cfg.groups × Fin cfg.shifts) : Reference.Owners n cfg :=
  fun v => if hv : v ∈ P then xs (pivotIndex targets i P hselected ⟨v, hv⟩)
    else (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)

theorem pivotsFromCoordinates_eq (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (hselected : ∀ i, selectedVertices targets i = members (P i))
    (xs : Fin targets.length → Fin cfg.groups × Fin cfg.shifts) :
    pivotsFromOwners cfg r sets reply targets 0 xs =
      pivotsFromOwners cfg r sets reply targets 0
        (ownersForTargets cfg targets
          (fun i => ownersFromCoordinates cfg targets i (P i) (hselected i) xs)) := by
  apply pivotsFromOwners_congr
  intro j hj
  have hv := selected_vertex_mem targets (targets.get j).setId
    (P (targets.get j).setId) (hselected (targets.get j).setId) j hj rfl
  dsimp only [ownersForTargets, ownersFromCoordinates]
  simp only [hv, ↓reduceDIte]
  rw [pivotIndex_active targets (targets.get j).setId
    (P (targets.get j).setId) (hselected (targets.get j).setId) j hj rfl]

theorem expected_owner_coordinates (cfg : Config) (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (f : Reference.Owners n cfg → ℝ)
    (hdepends : ∀ left right, (∀ v ∈ P, left v = right v) → f left = f right) :
    (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
        (fun xs => f (ownersFromCoordinates cfg targets i P hselected xs)) =
      (Reference.ownerLaw n cfg).expect f :=
  Law.family_subset_pullback n targets.length
    (Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)
    P (pivotIndex targets i P hselected) (pivotIndex_injective targets i P hselected)
    (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩) f hdepends

end

end StreamingReachability.Hopset
