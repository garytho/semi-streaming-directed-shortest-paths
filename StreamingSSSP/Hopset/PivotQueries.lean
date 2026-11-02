module

public import StreamingSSSP.Hopset.NodeQueries
public import StreamingSSSP.Hopset.OwnerSampling

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

variable {n ns : ℕ}

theorem accurate_pivot_queries (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target)
    (hk : target.kind = .pivot) :
    Late.AccurateBalls
      (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
      (sets.get target.setId) target.vertex
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
      (2 * index) (2 * index + 1)
      (Early.searchRadius cfg.k cfg.groups
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)) := by
  let c := catalog cfg r stored.blocks sets targets
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp ht
  have hlen := queries_length cfg r targets
  let forward : Fin (queries cfg r targets).length := ⟨2 * index, by omega⟩
  let backward : Fin (queries cfg r targets).length := ⟨2 * index + 1, by omega⟩
  have hft : targets[forward.val / 2]? = some target := by
    simpa [forward, Nat.mul_comm] using ht
  have hbt : targets[backward.val / 2]? = some target := by
    have hd : (2 * index + 1) / 2 = index := by omega
    simpa only [backward, hd] using ht
  have hf : c.searches.get forward =
      ⟨target.setId, target.vertex, false, cfg.searchRadius r⟩ := by
    have h := catalog_search_fields cfg r stored.blocks sets targets forward target hft
    simpa [forward, hk, targetRadius, Nat.mul_comm] using h
  have hb : c.searches.get backward =
      ⟨target.setId, target.vertex, true, cfg.searchRadius r⟩ := by
    have h := catalog_search_fields cfg r stored.blocks sets targets backward target hbt
    have hm : (2 * index + 1) % 2 = 1 := by omega
    simpa [backward, hk, targetRadius, hm] using h
  have hblocks : c.blocks.toList = stored.blocks := by
    simp [c, catalog, Array.toVector, Vector.toList_mk]
  have hx (i : Fin stored.blocks.length) : (c.blocks.get i).card ≤ cfg.blockSize :=
    hsize _ (catalog_block_mem cfg r stored.blocks sets targets i)
  rw [searchRadius_real]
  exact raw_query_pair_fraction c stored input hn hs hp hblocks cfg.inputScale_pos
    cfg.blockSize hx target.setId target.vertex forward backward
    (cfg.etaMax * cfg.initialNumerator) (cfg.denominatorAt r) (cfg.denominatorAt_pos r) hf hb

theorem pivot_eta_matches (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target)
    (hk : target.kind = .pivot) (hsource : target.vertex ∈ sets.get target.setId)
    (sigma : Fin cfg.groups) (phi : Fin cfg.shifts) :
    chooseEta cfg r (sets.get target.setId)
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
        (2 * index) (2 * index + 1) sigma phi =
      cfg.lambda + cfg.width * sigma.val +
        (Late.candidate
          (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
          ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)
          cfg.k cfg.groups cfg.shifts cfg.k_pos target.vertex sigma phi).val := by
  have ha := accurate_pivot_queries cfg r stored input hn hs hp hsize sets targets
    index target ht hk
  have hH : Implicit.induced
      (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
      (sets.get target.setId) =
        Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale :=
    Late.search_induced stored (StoredEdges.graphOfEdges input) _ cfg.inputScale
  have hD : 0 < (cfg.initialNumerator : ℝ) / cfg.denominatorAt r := by
    have hd := cfg.denominatorAt_pos r
    positivity
  exact Late.chooseEta_eq_candidate_of_accurate cfg r _ _ _ hsource hH _ _ _ _ ha hD le_rfl
    sigma phi cfg.k_pos

end StreamingSSSP.Hopset
