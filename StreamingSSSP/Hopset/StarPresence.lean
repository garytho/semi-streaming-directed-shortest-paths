module

public import StreamingSSSP.Hopset.NodeSound
public import StreamingSSSP.Late.Routes

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem lookup_record_exists (reply : Core.BatchAPI.SparseReply n) (query : ℕ) (v : Fin n) (d : ℕ)
    (h : lookup reply query v ≤ (d : Distance)) :
    ∃ record ∈ reply, record.queryId = query ∧ record.vertex = v ∧ record.distance ≤ d := by
  induction reply with
  | nil => simp [lookup, Core.BatchAPI.lookup] at h
  | cons record reply ih =>
      change Core.BatchAPI.lookup (record :: reply) query v ≤ (d : Distance) at h
      by_cases hm : record.queryId = query ∧ record.vertex = v
      · rw [Core.BatchAPI.lookup, if_pos hm] at h
        rcases min_le_iff.mp h with hd | ht
        · exact ⟨record, by simp, hm.1, hm.2, WithTop.coe_le_coe.mp hd⟩
        · obtain ⟨other, ho, hj, hv, hd⟩ := ih ht
          exact ⟨other, List.mem_cons_of_mem _ ho, hj, hv, hd⟩
      · rw [Core.BatchAPI.lookup, if_neg hm] at h
        obtain ⟨other, ho, hj, hv, hd⟩ := ih h
        exact ⟨other, List.mem_cons_of_mem _ ho, hj, hv, hd⟩

theorem emitted_record_mem (cfg : Config) (targets : List (Target n ns)) (reply : Core.BatchAPI.SparseReply n)
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target) (hk : target.kind ≠ .pivot)
    (record : Core.BatchAPI.DistanceRecord n) (hr : record ∈ reply) (backward : Bool)
    (hj : record.queryId = 2 * index + if backward then 1 else 0) (hne : record.vertex ≠ target.vertex) :
    (⟨if backward then record.vertex else target.vertex,
      if backward then target.vertex else record.vertex, cfg.inputScale * record.distance⟩ : StoredEdges.Edge n) ∈
        emittedStars cfg targets reply := by
  apply List.mem_filterMap.mpr
  refine ⟨record, hr, ?_⟩
  have hdiv : record.queryId / 2 = index := by rw [hj]; cases backward <;> simp <;> omega
  have hmod : decide (record.queryId % 2 = 1) = backward := by
    rw [hj]
    cases backward <;> simp [Nat.add_mod, Nat.mul_mod]
  have hback : record.queryId % 2 = 1 ↔ backward = true := by
    simp only [← hmod, decide_eq_true_eq]
  simp only [hdiv, ht, hk, hne, false_or, ↓reduceIte, hback]

theorem reply_star_route (cfg : Config) (targets : List (Target n ns)) (reply : Core.BatchAPI.SparseReply n)
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target) (hk : target.kind ≠ .pivot)
    (backward : Bool) (v : Fin n) (d : ℕ)
    (h : lookup reply (2 * index + if backward then 1 else 0) v ≤ (d : Distance))
    (F : Graph (Fin n)) (hF : ∀ e ∈ emittedStars cfg targets reply, F e.source e.target ≤ (e.weight : Distance)) :
    ∃ T : Late.Route F (if backward then v else target.vertex) (if backward then target.vertex else v)
      (cfg.inputScale * d), T.hops ≤ 1 := by
  by_cases hv : v = target.vertex
  · subst v
    cases backward <;> exact ⟨(Late.Route.nil target.vertex).weaken (Nat.zero_le _), by simp⟩
  · obtain ⟨record, hr, hj, hrV, hd⟩ := lookup_record_exists reply _ v d h
    have hne : record.vertex ≠ target.vertex := by rwa [hrV]
    have he := emitted_record_mem cfg targets reply index target ht hk record hr backward hj hne
    have hw := (hF _ he).trans (WithTop.coe_le_coe.mpr (Nat.mul_le_mul_left cfg.inputScale hd))
    simp only [hrV] at hw
    exact ⟨Late.Route.edge _ _ (cfg.inputScale * d) hw, le_rfl⟩

theorem clipped_le_bound (d : Distance) (bound radius : ℕ) (hd : d ≤ (bound : Distance)) (hr : bound ≤ radius) :
    (if d ≤ (radius : Distance) then d else ⊤) ≤ (bound : Distance) := by
  have hcap : d ≤ (radius : Distance) := hd.trans (WithTop.coe_le_coe.mpr hr)
  simpa only [hcap, ↓reduceIte] using hd

theorem raw_star_route (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target) (hk : target.kind ≠ .pivot)
    (backward : Bool) (v : Fin n) (d : ℕ) (hd : d ≤ targetRadius cfg r target.kind)
    (h : (if backward then
      (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist v target.vertex
      else (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist target.vertex v) ≤ (d : Distance))
    (F : Graph (Fin n))
    (hF : ∀ e ∈ emittedStars cfg targets
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance)) :
    ∃ T : Late.Route F (if backward then v else target.vertex) (if backward then target.vertex else v)
      (cfg.inputScale * d), T.hops ≤ 1 := by
  let c := catalog cfg r stored.blocks sets targets
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c cfg.blockSize) input).records
  let q := 2 * index + if backward then 1 else 0
  have hi : index < targets.length := (List.getElem?_eq_some_iff.mp ht).1
  have hq : q < (queries cfg r targets).length := by
    rw [queries_length]
    dsimp only [q]
    cases backward <;> simp <;> omega
  let j : Fin (queries cfg r targets).length := ⟨q, hq⟩
  have hdiv : q / 2 = index := by dsimp only [q]; cases backward <;> simp <;> omega
  have hmod : decide (q % 2 = 1) = backward := by
    dsimp only [q]
    cases backward <;> simp [Nat.add_mod, Nat.mul_mod]
  have htarget : targets[j.val / 2]? = some target := by
    change targets[q / 2]? = some target
    rw [hdiv]
    exact ht
  have hfields : c.searches.get j = ⟨target.setId, target.vertex, backward, targetRadius cfg r target.kind⟩ := by
    have hf := catalog_search_fields cfg r stored.blocks sets targets j target htarget
    change c.searches.get j =
      ⟨target.setId, target.vertex, decide (q % 2 = 1), targetRadius cfg r target.kind⟩ at hf
    rwa [hmod] at hf
  have hblocks : c.blocks.toList = stored.blocks := by
    simp only [c, catalog, Array.toVector, Vector.toList_mk, List.toList_toArray]
  have hx (i : Fin stored.blocks.length) : (c.blocks.get i).card ≤ cfg.blockSize :=
    hsize _ (catalog_block_mem cfg r stored.blocks sets targets i)
  have hm := Backend.raw_lookup c stored input hn hs hp hblocks cfg.inputScale_pos cfg.blockSize hx j v
  rw [hfields] at hm
  simp only [Core.Shared.vertices, hfields] at hm
  have hmodel : lookup reply q v =
      if (if backward then
        (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist v target.vertex
        else (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist target.vertex v) ≤
          (targetRadius cfg r target.kind : Distance)
      then (if backward then
        (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist v target.vertex
        else (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist target.vertex v)
      else ⊤ := by
    cases backward <;> simpa only [Bool.false_eq_true, ↓reduceIte,
      Graph.dist_reverse, c, catalog, reply, j] using hm
  have hlookup : lookup reply q v ≤ (d : Distance) := by
    rw [hmodel]
    exact clipped_le_bound _ d (targetRadius cfg r target.kind) h hd
  exact reply_star_route cfg targets reply index target ht hk backward v d hlookup F hF

end

end StreamingSSSP.Hopset
