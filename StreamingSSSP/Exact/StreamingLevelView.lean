module

public import StreamingSSSP.Exact.StreamingLift
public import StreamingSSSP.Exact.StreamingBaseView

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open StoredEdges

variable {n : ℕ}

def levelLocal (descriptor : LevelDescriptor (Fin n)) (edge : Edge n) : Option (Edge n) :=
  if descriptor.keep edge.source edge.target then some (EdgeTransducer.mapEdge descriptor.weight edge) else none

def levelView (descriptor : LevelDescriptor (Fin n)) (edge : Edge n) : Option (Edge (n + 1)) :=
  (levelLocal descriptor (EdgeTransducer.mapEdge (fun _ _ w => n * w + 1) edge)).map liftEdge

def levelAuxiliary (descriptor : LevelDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ) : List (Edge (n + 1)) :=
  ((EdgeTransducer.sentinelEdges source (sentinel n weightBound)).filterMap (levelLocal descriptor)).map liftEdge ++
    virtualEdges descriptor.sourceWeight

theorem levelLocal_list (descriptor : LevelDescriptor (Fin n)) (input : List (Edge n)) :
    input.filterMap (levelLocal descriptor) = EdgeTransducer.levelEdges descriptor input := by
  induction input with
  | nil => rfl
  | cons edge input ih =>
      by_cases hk : descriptor.keep edge.source edge.target <;>
        simp only [levelLocal, List.filterMap_cons, hk, ↓reduceIte, EdgeTransducer.levelEdges,
          EdgeTransducer.retained, List.filter_cons, List.map_cons, ih, Bool.false_eq_true]

theorem levelView_list (descriptor : LevelDescriptor (Fin n)) (input : List (Edge n)) :
    input.filterMap (levelView descriptor) =
      ((input.map (EdgeTransducer.mapEdge (fun _ _ w => n * w + 1))).filterMap (levelLocal descriptor)).map liftEdge := by
  induction input with
  | nil => rfl
  | cons edge input ih =>
      cases hv : levelLocal descriptor (EdgeTransducer.mapEdge (fun _ _ w => n * w + 1) edge) <;>
        simp only [List.filterMap_cons, levelView, hv, Option.map_none, Option.map_some, List.map_cons, ih]

theorem level_input_eq (descriptor : LevelDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ)
    (input : List (Edge n)) :
    input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor source weightBound =
      (EdgeTransducer.levelEdges descriptor (EdgeTransducer.preprocessingEdges input source weightBound)).map liftEdge ++
        virtualEdges descriptor.sourceWeight := by
  rw [levelView_list]
  unfold levelAuxiliary
  rw [← List.append_assoc, ← List.map_append, ← List.filterMap_append, levelLocal_list]
  rfl

theorem level_graph (descriptor : LevelDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ)
    (input : List (Edge n)) :
    graphOfEdges (input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor source weightBound) =
      (descriptor.graph (preprocess (graphOfEdges input) source weightBound)).comap (vertexEquiv n) := by
  rw [level_input_eq, graphOfEdges_append, lift_graph, virtual_graph]
  funext u v
  change min (onlyOriginal (graphOfEdges
      (EdgeTransducer.levelEdges descriptor (EdgeTransducer.preprocessingEdges input source weightBound)))
        (decodeVertex u) (decodeVertex v))
      (virtualGraph descriptor.sourceWeight (decodeVertex u) (decodeVertex v)) =
    descriptor.graph (preprocess (graphOfEdges input) source weightBound) (decodeVertex u) (decodeVertex v)
  generalize hu : decodeVertex u = a
  generalize hv : decodeVertex v = b
  cases a with
  | none =>
      cases b with
      | none => simp only [onlyOriginal, virtualGraph, min_top_right, descriptor.no_incoming_source]
      | some v => simp only [onlyOriginal, virtualGraph, min_top_left, descriptor.source_local]
  | some u =>
      cases b with
      | none => simp only [onlyOriginal, virtualGraph, min_top_right, descriptor.no_incoming_source]
      | some v =>
          simp only [onlyOriginal, virtualGraph, min_top_right]
          have h := EdgeTransducer.level_graph descriptor (EdgeTransducer.preprocessingEdges input source weightBound) u v
          rw [EdgeTransducer.preprocessing_graph] at h
          exact h

theorem level_auxiliary_size (descriptor : LevelDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ) :
    (levelAuxiliary descriptor source weightBound).length ≤ 2 * n := by
  have hs : (EdgeTransducer.sentinelEdges source (sentinel n weightBound)).length ≤ n := by
    have h := List.length_filter_le (fun v : Fin n => v ≠ source) (List.finRange n)
    simpa only [EdgeTransducer.sentinelEdges, List.length_map, List.length_finRange] using h
  have hf := List.length_filterMap_le (levelLocal descriptor) (EdgeTransducer.sentinelEdges source (sentinel n weightBound))
  simp only [levelAuxiliary, List.length_append, List.length_map, virtual_length]
  omega

theorem level_weight_positive (descriptor : LevelDescriptor (Fin n)) (u v : Fin n) (w : ℕ) :
    0 < descriptor.weight u v w := by unfold LevelDescriptor.weight; omega

theorem level_source_positive (descriptor : LevelDescriptor (Fin n)) (v : Fin n) :
    0 < descriptor.sourceWeight v := by unfold LevelDescriptor.sourceWeight; omega

theorem level_input_positive (descriptor : LevelDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ)
    (input : List (Edge n)) :
    ∀ edge ∈ input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor source weightBound, 0 < edge.weight := by
  rw [level_input_eq]
  intro edge he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp he
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
    exact level_weight_positive descriptor _ _ _
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    exact level_source_positive descriptor v

end StreamingSSSP.Exact.Implementation
