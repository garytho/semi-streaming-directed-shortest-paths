module

public import StreamingSSSP.Hopset.NodeQueries
public import StreamingSSSP.Hopset.ReferenceFacts
public import StreamingSSSP.Core.InterfaceCosts

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n nb ns nq : ℕ}

def queryDistance (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (scale : ℕ) (sets : Vector (Finset (Fin n)) ns) (query : Core.Shared.Search n ns)
    (v : Fin n) : Distance :=
  let G := Backend.roundedRestricted stored input (sets.get query.setId) scale
  if query.backward then G.dist v query.source else G.dist query.source v

def queryRecords (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (scale : ℕ) (sets : Vector (Finset (Fin n)) ns) (query : Core.Shared.Search n ns) : ℕ :=
  ∑ v ∈ sets.get query.setId,
    if queryDistance stored input scale sets query v ≤ (query.radius : Distance)
    then Reference.vertexWeight stored v else 0

theorem reached_eq_query (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hblocks : c.blocks.toList = stored.blocks) (hA : 0 < c.scale) (j : Fin nq) :
    Core.BatchDriver.reached c stored.explicit input j =
      Finset.univ.filter (fun v =>
        queryDistance stored input c.scale c.sets (c.searches.get j) v ≤
          ((c.searches.get j).radius : Distance)) := by
  have hm (v : Fin n) :
      Core.Global.target (Core.Shared.referenceProblem c j)
          ((stored.explicit ++ input).filterMap (Core.Shared.view c j)) v =
        queryDistance stored input c.scale c.sets (c.searches.get j) v := by
    change (Core.queryGraph ((stored.explicit ++ input).filterMap (Core.Shared.view c j))
      (Core.Shared.referenceProblem c j).blocks.toList c.scale).dist
        (c.searches.get j).source v = _
    rw [Core.queryGraph_dist_eq_full, Backend.distance_model c stored input hblocks hA j]
    cases hb : (c.searches.get j).backward <;>
      simp only [hb, Bool.false_eq_true, ↓reduceIte, queryDistance, Graph.dist_reverse, Core.Shared.vertices]
  ext v
  simp only [Core.BatchDriver.reached, Finset.mem_filter, Finset.mem_univ, true_and, hm]

theorem reached_subset_query_set (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hblocks : c.blocks.toList = stored.blocks) (hA : 0 < c.scale) (j : Fin nq)
    (hsource : (c.searches.get j).source ∈ Core.Shared.vertices c j) :
    Core.BatchDriver.reached c stored.explicit input j ⊆ Core.Shared.vertices c j := by
  intro v hv
  rw [reached_eq_query c stored input hblocks hA j] at hv
  have hd := (Finset.mem_filter.mp hv).2
  have hb : Early.Bounded (queryDistance stored input c.scale c.sets (c.searches.get j) v)
      ((c.searches.get j).radius : ℝ) :=
    Early.bounded_mono_distance hd ⟨(c.searches.get j).radius, rfl, le_rfl⟩
  apply Late.bothBall_subset_of_induced
    (Backend.roundedRestricted stored input (Core.Shared.vertices c j) c.scale)
    (Core.Shared.vertices c j)
    (Late.search_induced stored (StoredEdges.graphOfEdges input) _ c.scale) hsource _
  apply (Early.mem_bothBall _ _ _ _).mpr
  cases hback : (c.searches.get j).backward
  · exact Or.inl (by simpa only [queryDistance, hback, Bool.false_eq_true, ↓reduceIte,
      Core.Shared.vertices, Early.Within] using hb)
  · exact Or.inr (by simpa only [queryDistance, hback, ↓reduceIte, Core.Shared.vertices, Early.Within] using hb)

theorem raw_catalog_records (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight) (hblocks : c.blocks.toList = stored.blocks)
    (hA : 0 < c.scale) (workspace : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ workspace)
    (hsource : ∀ j, (c.searches.get j).source ∈ Core.Shared.vertices c j) :
    recordCharge stored.blocks
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c workspace) input).records =
      ∑ j : Fin nq, queryRecords stored input c.scale c.sets (c.searches.get j) := by
  let request := Core.BatchAPI.Request.ofCatalog stored.explicit c workspace
  have hw (v : Fin n) : Core.RecordGuard.vertexCharge c v = Reference.vertexWeight stored v := by
    rw [Backend.vertexCharge, hblocks]
    rfl
  have hc : Core.BatchAPI.replyCharge request (Core.BatchAPI.run request input).records =
      recordCharge stored.blocks (Core.BatchAPI.run request input).records := by
    change ((Core.BatchAPI.run request input).records.map fun record =>
      Core.RecordGuard.vertexCharge c record.vertex).sum = _
    simp_rw [hw]
    rfl
  rw [← hc, Core.BatchAPI.raw_reply_charge request input hn hs hp hA hx]
  change Core.BatchDriver.Nrec c stored.explicit input = _
  unfold Core.BatchDriver.Nrec
  apply Finset.sum_congr rfl
  intro j _
  rw [← Core.BatchAPI.vertex_weight c j (Core.BatchDriver.reached c stored.explicit input j)]
  simp_rw [hw]
  have he : Core.BatchDriver.reached c stored.explicit input j =
      (Core.Shared.vertices c j).filter (fun v =>
        queryDistance stored input c.scale c.sets (c.searches.get j) v ≤
          ((c.searches.get j).radius : Distance)) := by
    ext v
    constructor
    · intro hv
      have hs := reached_subset_query_set c stored input hblocks hA j (hsource j) hv
      rw [reached_eq_query c stored input hblocks hA j] at hv
      exact Finset.mem_filter.mpr ⟨hs, (Finset.mem_filter.mp hv).2⟩
    · intro hv
      rw [reached_eq_query c stored input hblocks hA j]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
  rw [he, Finset.sum_filter]
  rfl

end

end StreamingSSSP.Hopset
