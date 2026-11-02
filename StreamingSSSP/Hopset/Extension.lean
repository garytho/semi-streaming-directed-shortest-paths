module

public import StreamingSSSP.Hopset.OutputInclusion

@[expose] public section

namespace StreamingSSSP.Implicit.Representation

variable {n : ℕ}

def Extends (new old : Representation n) : Prop :=
  (∀ e ∈ old.explicit, e ∈ new.explicit) ∧ (∀ B ∈ old.blocks, B ∈ new.blocks)

theorem Extends.refl (stored : Representation n) : stored.Extends stored :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem Extends.trans {new middle old : Representation n}
    (h : new.Extends middle) (g : middle.Extends old) : new.Extends old :=
  ⟨fun e he => h.1 e (g.1 e he), fun B hB => h.2 B (g.2 B hB)⟩

theorem Extends.base_le {new old : Representation n} (h : new.Extends old) (G : Graph (Fin n)) :
    ∀ u v, new.base G u v ≤ old.base G u v := by
  intro u v
  apply min_le_min le_rfl
  apply (StoredEdges.le_graphOfEdges_iff old.explicit u v _).mpr
  intro e he hs ht
  simpa only [hs, ht] using StoredEdges.graphOfEdges_le_edge new.explicit (h.1 e he)

theorem Extends.graph_le {new old : Representation n} (h : new.Extends old) (G : Graph (Fin n)) :
    ∀ u v, new.graph G u v ≤ old.graph G u v :=
  Implicit.closures_mono old.blocks new.blocks (h.base_le G) (fun B hB => h.2 B hB)

end StreamingSSSP.Implicit.Representation

namespace StreamingSSSP.Hopset

variable {n : ℕ}

theorem commit_extends (stored : Implicit.Representation n) (out : Output n) :
    (commit stored out).Extends stored :=
  ⟨fun _ h => List.mem_append_left _ h, fun _ h => List.mem_append_left _ h⟩

theorem commit_extends_commit {new old : Implicit.Representation n} (h : new.Extends old) (out : Output n) :
    (commit new out).Extends (commit old out) := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (h.1 e he)
    · exact List.mem_append_right _ he
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact List.mem_append_left _ (h.2 B hB)
    · exact List.mem_append_right _ hB

theorem commit_blocks_small (stored : Implicit.Representation n) (out : Output n) (x : ℕ)
    (hs : ∀ B ∈ stored.blocks, B.card ≤ x) (ho : ∀ B ∈ out.blocks, B.card ≤ x) :
    ∀ B ∈ (commit stored out).blocks, B.card ≤ x := by
  intro B hB
  rcases List.mem_append.mp hB with h | h
  · exact hs B h
  · exact ho B h

end StreamingSSSP.Hopset
