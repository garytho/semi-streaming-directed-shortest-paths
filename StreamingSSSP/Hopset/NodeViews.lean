module

public import StreamingSSSP.Hopset.PartitionGeometry

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

structure NodeView (cfg : Config) (r : ℕ) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns) (S P : Finset (Fin n))
    (G : Graph (Fin n)) (rho : Fin n → ℝ) : Prop where
  vertices : ((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex) = members P
  flags : ∀ p ∈ pivots, p.setId = i → ∀ v ∈ S,
    (outFlag cfg r p reply v = true ↔ Early.Within G p.vertex v (rho p.vertex)) ∧
    (inFlag cfg r p reply v = true ↔ Early.Within G v p.vertex (rho p.vertex))
  fringe : ∀ p ∈ pivots, p.setId = i →
    Hopset.fringe cfg r p.eta p.shift S reply p.forward p.backward =
      S ∩ Early.fringe G p.vertex (rho p.vertex) (Reference.distanceScale cfg r)
  block : ∀ p ∈ pivots, p.setId = i →
    bothBall cfg r (p.eta + 1) p.shift S reply p.forward p.backward =
      S ∩ Early.bothBall G p.vertex (rho p.vertex + Reference.distanceScale cfg r)

theorem raw_node_views (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (P : Fin ns → Finset (Fin n))
    (hvalid : ∀ target ∈ targets, ValidTarget sets target)
    (hselected : ∀ i, selectedVertices targets i = members (P i))
    (owners : Fin ns → Reference.Owners n cfg) :
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    let pivots := pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets owners)
    ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i)
      (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
      (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (owners i)) := by
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  have hg := raw_assigned_pivot_geometry cfg r stored input hn hs hp hsize hnum sets targets hvalid owners
  dsimp only
  intro i
  refine ⟨(pivotsFromOwners_vertices cfg r sets reply targets 0 _ i).trans (hselected i), ?_, ?_, ?_⟩
  · intro p hmem hi v hv
    have h := (hg p hmem).1
    simpa only [hi] using h v (by simpa only [hi] using hv)
  · intro p hmem hi
    simpa only [hi] using (hg p hmem).2.1
  · intro p hmem hi
    simpa only [hi] using (hg p hmem).2.2

theorem raw_early_node_views (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (rank : Vector ℕ n) (hr : r < cfg.earlyLevel)
    (owners : Fin ns → Reference.Owners n cfg) :
    let targets := earlyTargets cfg r rank sets
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    let pivots := pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets owners)
    ∀ i, NodeView cfg r pivots reply i (sets.get i)
      (CopyHistory.pivots (sets.get i) r (fun v => rank.get v))
      (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
      (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (owners i)) :=
  raw_node_views cfg r stored input hn hs hp hsize hnum sets (earlyTargets cfg r rank sets)
    (fun i => CopyHistory.pivots (sets.get i) r (fun v => rank.get v))
    (earlyTargets_inside cfg r rank sets) (fun i => earlyTargets_selected cfg r rank sets i hr) owners

namespace NodeView

variable {cfg : Config} {r : ℕ} {pivots : List (Pivot n ns)}
    {reply : Core.BatchAPI.SparseReply n} {i : Fin ns} {S P : Finset (Fin n)}
    {G : Graph (Fin n)} {rho : Fin n → ℝ}

theorem core (h : NodeView cfg r pivots reply i S P G rho) :
    grouped S (fun v => !removed cfg r pivots reply i v) (labels cfg r pivots reply i) =
      Geometry.core G S P rho :=
  local_core_of_geometry cfg r pivots reply i S P G rho h.vertices h.flags

theorem lateCore (h : NodeView cfg r pivots reply i S P G rho) :
    (S.filter fun v => labels cfg r pivots reply i v = []) = Reference.lateChild G S P rho :=
  local_late_core_of_geometry cfg r pivots reply i S P G rho h.vertices h.flags

theorem fringes (h : NodeView cfg r pivots reply i S P G rho) :
    ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
      Hopset.fringe cfg r p.eta p.shift S reply p.forward p.backward) =
      Geometry.fringes G S P rho (Reference.distanceScale cfg r) := by
  calc
    _ = ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
        S ∩ Early.fringe G p.vertex (rho p.vertex) (Reference.distanceScale cfg r)) := by
      apply List.map_congr_left
      intro p hp
      obtain ⟨hp, hi⟩ := List.mem_filter.mp hp
      exact h.fringe p hp (of_decide_eq_true hi)
    _ = (((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex).map fun v =>
        S ∩ Early.fringe G v (rho v) (Reference.distanceScale cfg r)) := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := by rw [h.vertices]; rfl

theorem blocks (h : NodeView cfg r pivots reply i S P G rho) :
    ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
      bothBall cfg r (p.eta + 1) p.shift S reply p.forward p.backward) =
      (members P).map (fun v => S ∩ Early.bothBall G v (rho v + Reference.distanceScale cfg r)) := by
  calc
    _ = ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
        S ∩ Early.bothBall G p.vertex (rho p.vertex + Reference.distanceScale cfg r)) := by
      apply List.map_congr_left
      intro p hp
      obtain ⟨hp, hi⟩ := List.mem_filter.mp hp
      exact h.block p hp (of_decide_eq_true hi)
    _ = (((pivots.filter fun p => decide (p.setId = i)).map Pivot.vertex).map fun v =>
        S ∩ Early.bothBall G v (rho v + Reference.distanceScale cfg r)) := by
      simp only [List.map_map, Function.comp_def]
    _ = _ := by rw [h.vertices]

end NodeView

end

end StreamingSSSP.Hopset
