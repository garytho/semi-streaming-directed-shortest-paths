module

public import StreamingSSSP.Hopset.NodeQueries

@[expose] public section

namespace StreamingSSSP.Hopset.Backend

open scoped Classical
open StoredEdges

variable {n nb ns nq : ℕ}

theorem rounded_distance_sound (G : Graph (Fin n)) (stored : Implicit.Representation n)
    (input : List (Edge n)) (S : Finset (Fin n)) (A : ℕ) (hA : 0 < A)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (s t : Fin n) (d : ℕ) (hd : (roundedRestricted stored input S A).dist s t ≤ (d : Distance)) :
    G.dist s t ≤ ((A * d : ℕ) : Distance) := by
  have h := noncontracting_rounded_dist G (stored.restricted (graphOfEdges input) S) A hA
    (stored.sound_restricted_over G (graphOfEdges input) hinput hstored S) s t
  obtain ⟨e, he, hed⟩ := Exact.finite_of_le hd
  change G.dist s t ≤ WithTop.map (fun d => A * d)
    ((roundedRestricted stored input S A).dist s t) at h
  rw [he] at h
  exact h.trans (WithTop.coe_le_coe.mpr (Nat.mul_le_mul_left A hed))

theorem record_metric_bound (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hblocks : c.blocks.toList = stored.blocks) (hA : 0 < c.scale)
    (workspace : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ workspace)
    (record : Core.BatchAPI.DistanceRecord n)
    (hr : record ∈ (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c workspace) input).records)
    (j : Fin nq) (hj : record.queryId = j.val) :
    (if (c.searches.get j).backward then
        (roundedRestricted stored input (Core.Shared.vertices c j) c.scale).reverse
      else roundedRestricted stored input (Core.Shared.vertices c j) c.scale).dist
        (c.searches.get j).source record.vertex ≤ (record.distance : Distance) := by
  have h := raw_lookup c stored input hn hs hp hblocks hA workspace hx j record.vertex
  have hm := Core.BatchAPI.lookup_le
    (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c workspace) input).records
    j.val record.vertex hr hj rfl
  change lookup _ _ _ ≤ _ at hm
  apply le_trans _ hm
  rw [h]
  dsimp only
  split_ifs <;> first | exact le_rfl | exact le_top

theorem record_sound (G : Graph (Fin n)) (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hblocks : c.blocks.toList = stored.blocks) (hA : 0 < c.scale)
    (workspace : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ workspace)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (record : Core.BatchAPI.DistanceRecord n)
    (hr : record ∈ (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c workspace) input).records)
    (j : Fin nq) (hj : record.queryId = j.val) :
    G.dist (if (c.searches.get j).backward then record.vertex else (c.searches.get j).source)
        (if (c.searches.get j).backward then (c.searches.get j).source else record.vertex) ≤
      ((c.scale * record.distance : ℕ) : Distance) := by
  have hm := record_metric_bound c stored input hn hs hp hblocks hA workspace hx record hr j hj
  cases hb : (c.searches.get j).backward with
  | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at *
      exact rounded_distance_sound G stored input _ _ hA hinput hstored _ _ _ hm
  | true =>
      simp only [hb, ↓reduceIte, Graph.dist_reverse] at *
      exact rounded_distance_sound G stored input _ _ hA hinput hstored _ _ _ hm

theorem emittedStars_sound (G : Graph (Fin n)) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (e : Edge n)
    (he : e ∈ emittedStars cfg targets
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records) :
    G.dist e.source e.target ≤ (e.weight : Distance) ∧ 0 < e.weight := by
  let c := catalog cfg r stored.blocks sets targets
  let reply := (Core.BatchAPI.run
    (Core.BatchAPI.Request.ofCatalog stored.explicit c cfg.blockSize) input).records
  have hblocks : c.blocks.toList = stored.blocks := by
    simp [c, catalog, Array.toVector, Vector.toList_mk, List.toList_toArray]
  have hx (i : Fin stored.blocks.length) : (c.blocks.get i).card ≤ cfg.blockSize := by
    apply hsize
    have hmem : c.blocks.get i ∈ c.blocks.toList := by
      have h := List.get_mem c.blocks.toList ⟨i.val, by simpa using i.isLt⟩
      simpa only [List.get_eq_getElem, Vector.getElem_toList, Vector.get_eq_getElem] using h
    simpa only [hblocks] using hmem
  change e ∈ emittedStars cfg targets reply at he
  obtain ⟨record, hr, hrecord⟩ := List.mem_filterMap.mp he
  cases ht : targets[record.queryId / 2]? with
  | none =>
      simp only [ht] at hrecord
      cases hrecord
  | some target =>
      simp only [ht] at hrecord
      by_cases hskip : target.kind = .pivot ∨ record.vertex = target.vertex
      · simp only [hskip, ↓reduceIte] at hrecord
        cases hrecord
      · simp only [hskip, ↓reduceIte] at hrecord
        have heq := Option.some.inj hrecord
        subst e
        obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp ht
        have hj : record.queryId < (queries cfg r targets).length := by
          rw [queries_length]
          have h := (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp hi
          simpa only [Nat.mul_comm] using h
        let j : Fin (queries cfg r targets).length := ⟨record.queryId, hj⟩
        have hquery : c.searches.get j =
            ⟨target.setId, target.vertex, decide (record.queryId % 2 = 1),
              targetRadius cfg r target.kind⟩ :=
          catalog_search_fields cfg r stored.blocks sets targets j target ht
        have hweight := record_sound G c stored input hn hs hp hblocks cfg.inputScale_pos
          cfg.blockSize hx
          hinput hstored record hr j rfl
        simp only [hquery, decide_eq_true_eq] at hweight
        refine ⟨hweight, ?_⟩
        have hne :
            (if record.queryId % 2 = 1 then record.vertex else target.vertex) ≠
              (if record.queryId % 2 = 1 then target.vertex else record.vertex) := by
          have hn := (not_or.mp hskip).2
          by_cases hparity : record.queryId % 2 = 1
          · simpa only [hparity, ↓reduceIte] using hn
          · simpa only [hparity, ↓reduceIte] using Ne.symm hn
        exact WithTop.coe_le_coe.mp ((Core.positive_dist hG hne).trans hweight)

end StreamingSSSP.Hopset.Backend
