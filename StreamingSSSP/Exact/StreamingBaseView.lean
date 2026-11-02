module

public import StreamingSSSP.Exact.StreamingEncoding

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open StoredEdges

variable {n : ℕ}

def baseView (descriptor : BaseDescriptor (Fin n)) (edge : Edge n) : Option (Edge n) :=
  some { edge with weight := descriptor.weight edge.source edge.target (n * edge.weight + 1) }

def baseAuxiliary (descriptor : BaseDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ) : List (Edge n) :=
  (EdgeTransducer.sentinelEdges source (sentinel n weightBound)).map (EdgeTransducer.mapEdge descriptor.weight)

theorem base_input_eq (descriptor : BaseDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ)
    (input : List (Edge n)) :
    input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor source weightBound =
      (EdgeTransducer.preprocessingEdges input source weightBound).map (EdgeTransducer.mapEdge descriptor.weight) := by
  have hm : input.filterMap (baseView descriptor) =
      input.map (fun edge => { edge with weight := descriptor.weight edge.source edge.target (n * edge.weight + 1) }) := by
    induction input with
    | nil => rfl
    | cons edge input ih => simp only [baseView, List.filterMap_cons, List.map_cons, ih]
  rw [hm]
  simp only [EdgeTransducer.preprocessingEdges, List.map_append, List.map_map, baseAuxiliary]
  congr 1

theorem base_graph (descriptor : BaseDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ)
    (input : List (Edge n)) :
    graphOfEdges (input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor source weightBound) =
      descriptor.graph (preprocess (graphOfEdges input) source weightBound) := by
  rw [base_input_eq, EdgeTransducer.base_graph, EdgeTransducer.preprocessing_graph]

theorem base_auxiliary_size (descriptor : BaseDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ) :
    (baseAuxiliary descriptor source weightBound).length ≤ n := by
  have h := List.length_filter_le (fun v : Fin n => v ≠ source) (List.finRange n)
  simpa only [baseAuxiliary, EdgeTransducer.sentinelEdges, List.length_map, List.length_finRange] using h

theorem base_weight_positive (descriptor : BaseDescriptor (Fin n)) (u v : Fin n) (w : ℕ) :
    0 < descriptor.weight u v w := by
  unfold BaseDescriptor.weight
  omega

theorem base_input_positive (descriptor : BaseDescriptor (Fin n)) (source : Fin n) (weightBound : ℕ)
    (input : List (Edge n)) :
    ∀ edge ∈ input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor source weightBound, 0 < edge.weight := by
  intro edge he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨raw, _, heq⟩ := List.mem_filterMap.mp he
    have h : { raw with weight := descriptor.weight raw.source raw.target (n * raw.weight + 1) } = edge := by
      simpa only [baseView, Option.some.injEq] using heq
    subst edge
    exact base_weight_positive descriptor _ _ _
  · obtain ⟨raw, _, rfl⟩ := List.mem_map.mp he
    exact base_weight_positive descriptor _ _ _

end StreamingSSSP.Exact.Implementation
