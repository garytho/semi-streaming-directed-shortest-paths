module

public import StreamingReachability.Hopset.FrameLaw
public import StreamingReachability.Hopset.PivotOrder

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem fringes_of_views (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (P : Fin ns → Finset (Fin n)) (G : Fin ns → Graph (Fin n)) (rho : Fin ns → Fin n → ℝ)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i) (G i) (rho i))
    (hkeys : pivots.map (fun p => (p.setId, p.vertex)) =
      (pivotTargets P).map (fun target => (target.setId, target.vertex))) :
    earlyFringes cfg r sets pivots reply =
      (List.finRange ns).flatMap fun i =>
        Geometry.fringes (G i) (sets.get i) (P i) (rho i) (Reference.distanceScale cfg r) := by
  let F : Fin ns × Fin n → Finset (Fin n) := fun q =>
    sets.get q.1 ∩ Early.fringe (G q.1) q.2 (rho q.1 q.2) (Reference.distanceScale cfg r)
  calc
    _ = pivots.map (fun p => F (p.setId, p.vertex)) := by
      apply List.map_congr_left
      intro p hp
      exact (hview p.setId).fringe p hp rfl
    _ = (pivots.map (fun p => (p.setId, p.vertex))).map F := by
      simp only [List.map_map, Function.comp_def]
    _ = ((pivotTargets P).map (fun target => (target.setId, target.vertex))).map F := by rw [hkeys]
    _ = _ := by
      simp only [pivotTargets, List.map_flatMap, List.map_map, Function.comp_def, Geometry.fringes, F]

theorem blocks_of_views (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (P : Fin ns → Finset (Fin n)) (G : Fin ns → Graph (Fin n)) (rho : Fin ns → Fin n → ℝ)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i) (G i) (rho i))
    (hkeys : pivots.map (fun p => (p.setId, p.vertex)) =
      (pivotTargets P).map (fun target => (target.setId, target.vertex))) :
    lateBlocks cfg r sets pivots reply =
      (List.finRange ns).flatMap fun i =>
        (members (P i)).map fun p =>
          sets.get i ∩ Early.bothBall (G i) p (rho i p + Reference.distanceScale cfg r) := by
  let F : Fin ns × Fin n → Finset (Fin n) := fun q =>
    sets.get q.1 ∩ Early.bothBall (G q.1) q.2 (rho q.1 q.2 + Reference.distanceScale cfg r)
  calc
    _ = pivots.map (fun p => F (p.setId, p.vertex)) := by
      apply List.map_congr_left
      intro p hp
      exact (hview p.setId).block p hp rfl
    _ = (pivots.map (fun p => (p.setId, p.vertex))).map F := by
      simp only [List.map_map, Function.comp_def]
    _ = ((pivotTargets P).map (fun target => (target.setId, target.vertex))).map F := by rw [hkeys]
    _ = _ := by
      simp only [pivotTargets, List.map_flatMap, List.map_map, Function.comp_def, F]

namespace Batched

def geometricChildren (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (choices : Fin ns → Reference.Choice n cfg) : List (Finset (Fin n)) :=
  let G := fun i => Backend.roundedRestricted stored input (sets.get i) cfg.inputScale
  let rho := fun i => Reference.radii cfg r (G i) (choices i).owners
  if r < cfg.earlyLevel then
    ((List.finRange ns).flatMap fun i =>
      Geometry.fringes (G i) (sets.get i) (choices i).pivots (rho i) (Reference.distanceScale cfg r)) ++
      (List.finRange ns).flatMap (fun i => Geometry.core (G i) (sets.get i) (choices i).pivots (rho i))
  else if r < cfg.maximumLevel then
    (List.finRange ns).map fun i => Reference.lateChild (G i) (sets.get i) (choices i).pivots (rho i)
  else []

def geometricBlocks (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (choices : Fin ns → Reference.Choice n cfg) : List (Finset (Fin n)) :=
  (List.finRange ns).flatMap fun i => Reference.blocks cfg stored input r (sets.get i) (choices i)

theorem frameFromOwners_geometry (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (P : Fin ns → Finset (Fin n))
    (hvalid : ∀ target ∈ targets, ValidTarget sets target)
    (hselected : ∀ i, selectedVertices targets i = members (P i))
    (hfilter : (targets.filter fun target => decide (target.kind = .pivot)) = pivotTargets P)
    (owners : Fin ns → Reference.Owners n cfg) :
    let frame := frameFromOwners cfg r stored input sets targets P owners
    frame.result.children = geometricChildren cfg r stored input sets frame.choices ∧
      frame.result.output.blocks = geometricBlocks cfg r stored input sets frame.choices := by
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  let pivots := pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets owners)
  let G := fun i => Backend.roundedRestricted stored input (sets.get i) cfg.inputScale
  let rho := fun i => Reference.radii cfg r (G i) (owners i)
  have hv := raw_node_views cfg r stored input hn hs hp hsize hnum sets targets P hvalid hselected owners
  have hk : pivots.map (fun p => (p.setId, p.vertex)) =
      (pivotTargets P).map (fun target => (target.setId, target.vertex)) := by
    rw [pivotsFromOwners_keys cfg r sets reply targets 0 _, hfilter]
  have hc : earlyCore cfg r sets pivots reply =
      (List.finRange ns).flatMap fun i => Geometry.core (G i) (sets.get i) (P i) (rho i) := by
    unfold earlyCore
    apply List.flatMap_congr
    intro i hi
    exact (hv i).core
  have hl : lateCore cfg r sets pivots reply =
      (List.finRange ns).map fun i => Reference.lateChild (G i) (sets.get i) (P i) (rho i) := by
    unfold lateCore
    apply List.map_congr_left
    intro i hi
    exact (hv i).lateCore
  dsimp only [frameFromOwners]
  by_cases he : r < cfg.earlyLevel
  · simp only [assemble, geometricChildren, geometricBlocks, he, ↓reduceIte, Reference.blocks]
    exact ⟨congrArg₂ List.append (fringes_of_views cfg r sets pivots reply P G rho hv hk) hc, by simp⟩
  · simp only [assemble, geometricChildren, geometricBlocks, he, ↓reduceIte, Reference.blocks]
    refine ⟨?_, blocks_of_views cfg r sets pivots reply P G rho hv hk⟩
    by_cases hlast : r < cfg.maximumLevel
    · simpa only [hlast, ↓reduceIte] using hl
    · simp only [hlast, ↓reduceIte]

theorem frameLaw_geometry (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator) :
    Early.Sampling.Holds (frameLaw cfg hn stored input rank r sets) (fun frame =>
      frame.result.children = geometricChildren cfg r stored input sets frame.choices ∧
        frame.result.output.blocks = geometricBlocks cfg r stored input sets frame.choices) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [frameLaw, he, ↓reduceIte, queryFrameLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro owners h
    exact frameFromOwners_geometry cfg r stored input hn hs hp hsize hnum sets _ _
      (earlyTargets_inside cfg r rank sets) (fun i => earlyTargets_selected cfg r rank sets i he)
      (earlyTargets_pivotFilter cfg r rank sets he) owners
  · simp only [frameLaw, he, ↓reduceIte]
    refine Reference.holds_bind_on _ _ (fun P => ∀ i, P i ⊆ sets.get i) _
      (lateFamily_subsets cfg hn r sets) ?_
    intro P hP
    simp only [queryFrameLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro owners h
    exact frameFromOwners_geometry cfg r stored input hn hs hp hsize hnum sets _ P
      (pivotTargets_valid sets P hP) (selectedVertices_pivot_targets P) (pivotTargets_pivotFilter P) owners

end Batched

end

end StreamingReachability.Hopset
