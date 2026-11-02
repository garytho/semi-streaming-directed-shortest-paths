module

public import StreamingSSSP.Core.InterfaceCorrect
public import StreamingSSSP.Core.RecordGuard

@[expose] public section

namespace StreamingSSSP.Core.BatchAPI

open StoredEdges

variable {n nb ns nq : ℕ}

def replyCharge {n : ℕ} (request : Request n) (reply : SparseReply n) : ℕ :=
  (reply.map fun record => RecordGuard.vertexCharge request.catalog record.vertex).sum

theorem vertex_weight (c : Catalog n nb ns nq) (j : Fin nq) (S : Finset (Fin n)) :
    S.sum (RecordGuard.vertexCharge c) = S.card +
      ∑ i : Fin nb, (S ∩ c.blocks.get i).card := by
  have h (v : Fin n) : RecordGuard.vertexCharge c v =
      1 + ∑ i : Fin nb, if v ∈ c.blocks.get i then 1 else 0 :=
    RecordGuard.charge_eq c (j, v)
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.card_filter]
    congr 1

theorem sum_flatMap {I S : Type*} (indices : List I) (items : I → List S) (cost : S → ℕ) :
    ((indices.flatMap items).map cost).sum = (indices.map fun i => ((items i).map cost).sum).sum := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem serialize_all (c : Catalog n nb ns nq) (states : BatchDriver.States n nb nq)
    (h : ∀ j, ∀ pair ∈ (states.get j).labels,
      pair.1 ∈ (states.get j).settled ∧ pair.2 ≤ ((c.searches.get j).radius : Distance)) :
    serialize c states = (List.finRange nq).flatMap fun j =>
      (states.get j).labels.map fun pair => (⟨j.val, pair.1, pair.2.untopD 0⟩ : DistanceRecord n) := by
  unfold serialize
  congr 1
  funext j
  have hh (pairs : SparseLabels.Labels (Fin n))
      (hp : ∀ pair ∈ pairs, pair.1 ∈ (states.get j).settled ∧
        pair.2 ≤ ((c.searches.get j).radius : Distance)) :
      (pairs.filterMap fun pair =>
        if pair.1 ∈ (states.get j).settled ∧ pair.2 ≤ ((c.searches.get j).radius : Distance)
        then some (⟨j.val, pair.1, pair.2.untopD 0⟩ : DistanceRecord n) else none) =
        pairs.map (fun pair => (⟨j.val, pair.1, pair.2.untopD 0⟩ : DistanceRecord n)) := by
    induction pairs with
    | nil => rfl
    | cons pair pairs ih =>
        have hc := hp pair (by simp)
        simp only [List.filterMap_cons, hc, and_self, ↓reduceIte, List.map_cons]
        rw [ih (fun q hq => hp q (by simp [hq]))]
  exact hh _ (h j)

theorem serialize_weight (c : Catalog n nb ns nq) (states : BatchDriver.States n nb nq)
    (sets : Fin nq → Finset (Fin n))
    (hu : ∀ j, ((states.get j).labels.map Prod.fst).Nodup)
    (hs : ∀ j, SparseLabels.support (states.get j).labels = sets j)
    (ha : ∀ j, ∀ pair ∈ (states.get j).labels,
      pair.1 ∈ (states.get j).settled ∧ pair.2 ≤ ((c.searches.get j).radius : Distance)) :
    ((serialize c states).map fun record => RecordGuard.vertexCharge c record.vertex).sum =
      ∑ j : Fin nq, ((sets j).card + ∑ i : Fin nb, (sets j ∩ c.blocks.get i).card) := by
  rw [serialize_all c states ha, sum_flatMap]
  simp only [List.map_map, Function.comp_def]
  have hj (j : Fin nq) :
      ((states.get j).labels.map fun pair => RecordGuard.vertexCharge c pair.1).sum =
        (sets j).sum (RecordGuard.vertexCharge c) := by
    have h := List.sum_toFinset (RecordGuard.vertexCharge c) (hu j)
    rw [List.map_map] at h
    change (SparseLabels.support (states.get j).labels).sum (RecordGuard.vertexCharge c) = _ at h
    rw [hs j] at h
    exact h.symm
  rw [show (List.finRange nq).map (fun j =>
      ((states.get j).labels.map fun pair => RecordGuard.vertexCharge c pair.1).sum) =
      (List.finRange nq).map (fun j => (sets j).sum (RecordGuard.vertexCharge c)) from
      List.map_congr_left (fun j _ => hj j)]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  exact vertex_weight c j (sets j)

theorem raw_reply_charge (request : Request n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    replyCharge request (run request input).records =
      BatchDriver.Nrec request.catalog request.explicit input := by
  let c := request.catalog
  let states := (BatchDriver.execute hn c request.explicit input request.workspace (request.radius + 1)).states
  have hg (j : Fin request.queryCount) :=
    (BatchDriver.execute_global_invariant hn c request.explicit input request.workspace (request.radius + 1)
      hs hp hA hx j).1
  have hset (j : Fin request.queryCount) : (states.get j).settled =
      BatchDriver.reached c request.explicit input j :=
    BatchDriver.final_settled hn c request.explicit input request.workspace request.radius hs hp hA hx
      (radius_bound request) j
  have hsupport (j : Fin request.queryCount) : SparseLabels.support (states.get j).labels =
      BatchDriver.reached c request.explicit input j := by
    have hSource : (c.searches.get j).source ∈ (states.get j).settled := by
      rw [hset]
      simp [BatchDriver.reached, Global.target, Shared.referenceProblem]
    have hsup : SparseLabels.support (states.get j).labels =
        (states.get j).settled ∪ {(c.searches.get j).source} := (hg j).label_support
    rw [hsup, Finset.union_singleton, Finset.insert_eq_of_mem hSource, hset]
  have hall (j : Fin request.queryCount) (pair : Fin n × Distance) (hpair : pair ∈ (states.get j).labels) :
      pair.1 ∈ (states.get j).settled ∧ pair.2 ≤ ((c.searches.get j).radius : Distance) := by
    have hmem : pair.1 ∈ SparseLabels.support (states.get j).labels :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, hpair, rfl⟩)
    have hrec : pair.1 ∈ BatchDriver.reached c request.explicit input j := hsupport j ▸ hmem
    refine ⟨by rwa [hset], ?_⟩
    rw [← labels_get_mem _ (hg j).label_unique hpair, (hg j).label_exact pair.1 hmem]
    exact (Finset.mem_filter.mp hrec).2
  rw [replyCharge, run, dite_eq_left hn]
  dsimp only
  rw [BatchDriver.executeTail_eq]
  exact serialize_weight c states (BatchDriver.reached c request.explicit input)
    (fun j => (hg j).label_unique) hsupport hall

theorem raw_stored_records_le_reply_charge (request : Request n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    BatchDriver.recordCount
      (BatchDriver.executeTail hn request.catalog request.explicit input request.workspace (request.radius + 1)).states ≤
      replyCharge request (run request input).records := by
  rw [raw_reply_charge request input hn hs hp hA hx, BatchDriver.executeTail_eq]
  exact BatchDriver.final_record_bound hn _ _ _ _ _ hs hp hA hx (radius_bound request)

end StreamingSSSP.Core.BatchAPI
