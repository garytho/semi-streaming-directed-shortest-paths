module

public import StreamingReachability.Hopset.PhysicalCounts
public import StreamingReachability.Core.Main

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n ns : ℕ}

structure QueryBounds (x radius records catalogWords scale weight : ℕ)
    (request : Core.BatchAPI.Request n) (allowance : ℕ) : Prop where
  workspace : request.workspace = x
  radius_le : request.radius ≤ radius
  allowance_le : allowance ≤ records
  catalog_le : Core.Live.catalogCells request.catalog request.explicit ≤ catalogWords
  scale_pos : 0 < request.catalog.scale
  scale_le : request.catalog.scale ≤ scale
  explicit_positive : ∀ e ∈ request.explicit, 0 < e.weight
  explicit_weights : ∀ e ∈ request.explicit, e.weight ≤ weight
  blocks : ∀ i, (request.catalog.blocks.get i).card ≤ x

def catalogLimit (stored : Implicit.Representation n) (copies : ℕ) : ℕ :=
  4 * (stored.blocks.length + 7 * copies + 1) + 3 * stored.explicit.length +
    2 * volume stored.blocks + 2 * copies

theorem catalog_cells (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) :
    Core.Live.catalogCells (catalog cfg r stored.blocks sets targets) stored.explicit =
      4 * (stored.blocks.length + ns + 2 * targets.length + 1) + 3 * stored.explicit.length +
        2 * volume stored.blocks + 2 * setVolume sets := by
  unfold Core.Live.catalogCells
  rw [vector_volume (catalog cfg r stored.blocks sets targets).blocks,
    vector_volume (catalog cfg r stored.blocks sets targets).sets]
  simp only [catalog, queries_length, setVolume, Array.toVector, Vector.toList_mk]

theorem catalog_query_bounds (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) (allowance scale weight : ℕ)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hw : ∀ e ∈ stored.explicit, e.weight ≤ weight)
    (hb : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hscale : cfg.inputScale ≤ scale) (hr : cfg.searchRadius r ≤ cfg.globalRadius)
    (ha : allowance ≤ cfg.recordCap) (hsets : ns ≤ 3 * cfg.copyCap)
    (hvolume : setVolume sets ≤ cfg.copyCap) (htargets : targets.length ≤ 2 * cfg.copyCap) :
    QueryBounds cfg.blockSize cfg.globalRadius cfg.recordCap (catalogLimit stored cfg.copyCap) scale weight
      (Core.BatchAPI.Request.ofCatalog stored.explicit (catalog cfg r stored.blocks sets targets) cfg.blockSize)
      allowance := by
  refine ⟨rfl, request_radius cfg r _ _ sets targets cfg.blockSize hr, ha, ?_,
    cfg.inputScale_pos, hscale, hs, hw, ?_⟩
  · change Core.Live.catalogCells (catalog cfg r stored.blocks sets targets) stored.explicit ≤ _
    rw [catalog_cells]
    unfold catalogLimit
    omega
  · intro i
    exact hb _ (catalog_block_mem cfg r stored.blocks sets targets i)

def passLimit (n x radius records : ℕ) : ℕ :=
  (radius + 1) * (Nat.log 2 x + 3) + 32 * x * records / n

theorem QueryBounds.passes {E : Type*} (hn : 0 < n) (view : E → Option (StoredEdges.Edge n))
    (input : List E) (auxiliary : List (StoredEdges.Edge n))
    {x radius records catalogWords scale weight : ℕ} {request : Core.BatchAPI.Request n} {allowance : ℕ}
    (h : QueryBounds x radius records catalogWords scale weight request allowance)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight) :
    (auxiliaryHandler view input auxiliary request allowance).passes ≤ passLimit n x radius records := by
  have hb := Core.BatchAPI.runGuardedMeasured_pass_bound hn request allowance
    (input.filterMap view ++ auxiliary) h.explicit_positive hp h.scale_pos
    (by intro i; rw [h.workspace]; exact h.blocks i)
  change (Core.BatchAPI.runGuardedMeasuredAuxiliary request allowance view input auxiliary).passes ≤ _
  rw [Core.BatchAPI.runGuardedMeasuredAuxiliary_eq]
  apply hb.trans
  unfold passLimit
  rw [h.workspace]
  gcongr <;> first | exact h.radius_le | exact h.allowance_le

def memoryLimit (n records catalogWords : ℕ) : ℕ :=
  256 * (n + records + 1) + 4 * catalogWords

theorem QueryBounds.every_prefix (hn : 0 < n) (input : List (StoredEdges.Edge n))
    {x radius records catalogWords scale weight : ℕ} {request : Core.BatchAPI.Request n} {allowance : ℕ}
    (h : QueryBounds x radius records catalogWords scale weight request allowance)
    (hp : ∀ e ∈ input, 0 < e.weight) (hspace : 2 * x * x ≤ n) :
    ∀ point : Core.Live.MemoryPoint hn request.catalog request.explicit input allowance request.workspace,
      point.cells ≤ memoryLimit n records catalogWords := by
  have hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace := by
    intro i
    rw [h.workspace]
    exact h.blocks i
  have hsq : 2 * request.workspace * request.workspace ≤ n := by rwa [h.workspace]
  have hs := Core.BatchAPI.runGuarded_every_prefix_space hn request allowance input
    h.explicit_positive hp h.scale_pos hx hsq
  intro point
  have ha := h.allowance_le
  have hc := h.catalog_le
  exact (hs point).trans (by unfold memoryLimit; omega)

end StreamingReachability.Hopset.Measured
