module

public import StreamingReachability.Hopset.RawRecords
public import StreamingReachability.Hopset.LevelCosts

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ}

def targetRecords (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (target : Target n ns) : ℕ :=
  Reference.searchRecords stored
    (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
    (sets.get target.setId) target.vertex (targetRadius cfg r target.kind)

theorem paired_query_records (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (scale : ℕ) (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (p : Fin n) (radius : ℕ) :
    queryRecords stored input scale sets ⟨i, p, false, radius⟩ +
        queryRecords stored input scale sets ⟨i, p, true, radius⟩ =
      Reference.searchRecords stored (Backend.roundedRestricted stored input (sets.get i) scale)
        (sets.get i) p radius := by
  simp only [queryRecords, queryDistance, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  rfl

theorem queries_records (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) :
    ((queries cfg r targets).map (queryRecords stored input cfg.inputScale sets)).sum =
      (targets.map (targetRecords cfg r stored input sets)).sum := by
  induction targets with
  | nil => rfl
  | cons target targets ih =>
      simp only [queries] at ih
      simp only [queries, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, add_zero, ih,
        paired_query_records, targetRecords]

theorem raw_target_records (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (hvalid : ∀ target ∈ targets, ValidTarget sets target) :
    recordCharge stored.blocks
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records =
      (targets.map (targetRecords cfg r stored input sets)).sum := by
  let c := catalog cfg r stored.blocks sets targets
  have hblocks : c.blocks.toList = stored.blocks := by
    simp only [c, catalog, Array.toVector, Vector.toList_mk, List.toList_toArray]
  have hx (i : Fin stored.blocks.length) : (c.blocks.get i).card ≤ cfg.blockSize :=
    hsize _ (catalog_block_mem cfg r stored.blocks sets targets i)
  have hsource (j : Fin (queries cfg r targets).length) :
      (c.searches.get j).source ∈ Core.Shared.vertices c j := by
    have hlen := queries_length cfg r targets
    have hj : j.val / 2 < targets.length := by have := j.isLt; omega
    let target := targets.get ⟨j.val / 2, hj⟩
    have ht : targets[j.val / 2]? = some target := by
      simp only [target, List.get_eq_getElem, List.getElem?_eq_getElem hj]
    have hq := catalog_search_fields cfg r stored.blocks sets targets j target ht
    change (c.searches.get j).source ∈ sets.get (c.searches.get j).setId
    rw [hq]
    exact hvalid target (List.get_mem targets ⟨j.val / 2, hj⟩)
  calc
    _ = ∑ j : Fin (queries cfg r targets).length,
        queryRecords stored input cfg.inputScale sets (c.searches.get j) :=
      raw_catalog_records c stored input hn hs hp hblocks cfg.inputScale_pos cfg.blockSize hx hsource
    _ = ((List.finRange (queries cfg r targets).length).map fun j =>
        queryRecords stored input cfg.inputScale sets (c.searches.get j)).sum := (sum_finRange _).symm
    _ = (c.searches.toList.map (queryRecords stored input cfg.inputScale sets)).sum := by
      have h := congrArg (fun L => (L.map (queryRecords stored input cfg.inputScale sets)).sum)
        (Backend.vector_indices c.searches)
      simpa only [List.map_map, Function.comp_def] using h
    _ = ((queries cfg r targets).map (queryRecords stored input cfg.inputScale sets)).sum := by
      simp only [c, catalog, Array.toVector, Vector.toList_mk, List.toList_toArray]
    _ = _ := queries_records cfg r stored input sets targets

end

end StreamingReachability.Hopset
