module

public import StreamingSSSP.Hopset.TrialSound

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem commit_base_le (stored : Implicit.Representation n) (out : Output n) (G : Graph (Fin n)) :
    ∀ u v, (commit stored out).base G u v ≤ stored.base G u v := by
  intro u v
  change min (G u v) (StoredEdges.graphOfEdges (stored.explicit ++ out.explicit) u v) ≤
    min (G u v) (StoredEdges.graphOfEdges stored.explicit u v)
  rw [StoredEdges.graphOfEdges_append]
  exact min_le_min le_rfl (min_le_left _ _)

theorem commit_graph_le (stored : Implicit.Representation n) (out : Output n) (G : Graph (Fin n)) :
    ∀ u v, (commit stored out).graph G u v ≤ stored.graph G u v :=
  Implicit.closures_mono stored.blocks (stored.blocks ++ out.blocks) (commit_base_le stored out G)
    (fun _ h => List.mem_append_left _ h)

theorem commit_explicit_edge (stored : Implicit.Representation n) (out : Output n) (G : Graph (Fin n))
    (e : StoredEdges.Edge n) (he : e ∈ out.explicit) :
    (commit stored out).graph G e.source e.target ≤ (e.weight : Distance) := by
  have hbase := Implicit.closures_le_base ((commit stored out).base G) (commit stored out).blocks e.source e.target
  apply (hbase.trans (min_le_right _ _)).trans
  exact StoredEdges.graphOfEdges_le_edge _ (List.mem_append_right stored.explicit he)

theorem commit_block_closure (stored : Implicit.Representation n) (out : Output n) (G : Graph (Fin n))
    (B : Finset (Fin n)) (hB : B ∈ out.blocks) :
    ∀ u v, (commit stored out).graph G u v ≤ Implicit.closure (stored.base G) B u v := by
  intro u v
  exact (Implicit.closures_le_member ((commit stored out).base G) (stored.blocks ++ out.blocks)
    (List.mem_append_right stored.blocks hB) u v).trans
      (Implicit.closure_mono (commit_base_le stored out G) (Finset.Subset.refl B) u v)

end

end StreamingSSSP.Hopset
