module

public import StreamingSSSP.Hopset.OutputInclusion
public import StreamingSSSP.Hopset.FullAudit

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem replay_explicit_list (state : State n) (trace : List (Entry n)) :
    (replay state trace).output.explicit =
      state.output.explicit ++ trace.flatMap (fun entry => entry.step.output.explicit) := by
  induction trace generalizing state with
  | nil => simp only [replay, List.flatMap_nil, List.append_nil]
  | cons entry trace ih =>
      simp only [replay, ih, applyStep, List.flatMap_cons, List.append_assoc]

theorem replay_blocks_list (state : State n) (trace : List (Entry n)) :
    (replay state trace).output.blocks =
      state.output.blocks ++ trace.flatMap (fun entry => entry.step.output.blocks) := by
  induction trace generalizing state with
  | nil => simp only [replay, List.flatMap_nil, List.append_nil]
  | cons entry trace ih =>
      simp only [replay, ih, applyStep, List.flatMap_cons, List.append_assoc]

def geometricOutput (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg)) : Output n :=
  (replay (globalState cfg stored input (Vector.ofFn ranks)) (trace.map GeometricEntry.erase)).output

theorem geometricOutput_explicit (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg)) :
    (geometricOutput cfg stored input ranks trace).explicit =
      (globalState cfg stored input (Vector.ofFn ranks)).output.explicit ++
        trace.flatMap (fun entry => entry.frame.result.output.explicit) := by
  simp only [geometricOutput, replay_explicit_list, List.flatMap_map, Function.comp_def, GeometricEntry.erase]

theorem geometricOutput_blocks (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg)) :
    (geometricOutput cfg stored input ranks trace).blocks =
      trace.flatMap (fun entry => entry.frame.result.output.blocks) := by
  simp only [geometricOutput, replay_blocks_list, globalState, List.flatMap_map, Function.comp_def,
    GeometricEntry.erase, List.nil_append]

theorem geometricOutput_old (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg)) :
    ∀ u v, (commit stored (geometricOutput cfg stored input ranks trace)).graph (StoredEdges.graphOfEdges input) u v ≤
      stored.graph (StoredEdges.graphOfEdges input) u v :=
  commit_graph_le _ _ _

theorem geometricOutput_frame_edge (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
    (entry : GeometricEntry n cfg) (he : entry ∈ trace) (e : StoredEdges.Edge n)
    (hee : e ∈ entry.frame.result.output.explicit) :
    (commit stored (geometricOutput cfg stored input ranks trace)).graph (StoredEdges.graphOfEdges input)
      e.source e.target ≤ (e.weight : Distance) := by
  apply commit_explicit_edge
  rw [geometricOutput_explicit]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry, he, hee⟩)

theorem geometricOutput_frame_block (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
    (B : Finset (Fin n)) (hB : B ∈ trace.flatMap (fun entry => entry.frame.result.output.blocks)) :
    ∀ u v, (commit stored (geometricOutput cfg stored input ranks trace)).graph (StoredEdges.graphOfEdges input) u v ≤
      Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v := by
  apply commit_block_closure
  rw [geometricOutput_blocks]
  exact hB

theorem geometricOutput_global_edge (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
    (e : StoredEdges.Edge n) (he : e ∈ (globalState cfg stored input (Vector.ofFn ranks)).output.explicit) :
    (commit stored (geometricOutput cfg stored input ranks trace)).graph (StoredEdges.graphOfEdges input)
      e.source e.target ≤ (e.weight : Distance) := by
  apply commit_explicit_edge
  rw [geometricOutput_explicit]
  exact List.mem_append_left _ he

end

end StreamingSSSP.Hopset.Batched
