module

public import StreamingReachability.Core.Interface
public import StreamingReachability.Core.BatchStatistics

@[expose] public section

namespace StreamingReachability.Core.BatchAPI

open StoredEdges

variable {n nb ns nq : ℕ}

def lookup : SparseReply n → ℕ → Fin n → Distance
  | [], _, _ => ⊤
  | record :: rest, j, v =>
      if record.queryId = j ∧ record.vertex = v
      then min (record.distance : Distance) (lookup rest j v) else lookup rest j v

theorem le_lookup (records : SparseReply n) (j : ℕ) (v : Fin n) (d : Distance) :
    d ≤ lookup records j v ↔ ∀ record ∈ records,
      record.queryId = j → record.vertex = v → d ≤ (record.distance : Distance) := by
  induction records with
  | nil => simp [lookup]
  | cons record rest ih =>
      by_cases h : record.queryId = j ∧ record.vertex = v <;>
        simp [lookup, h, ih] <;> tauto

theorem lookup_le (records : SparseReply n) (j : ℕ) (v : Fin n)
    {record : DistanceRecord n} (hr : record ∈ records)
    (hj : record.queryId = j) (hv : record.vertex = v) :
    lookup records j v ≤ (record.distance : Distance) := by
  induction records with
  | nil => simp at hr
  | cons head rest ih =>
      rcases List.mem_cons.mp hr with rfl | hr
      · simp only [lookup, hj, hv, and_self, ↓reduceIte]
        exact min_le_left _ _
      · unfold lookup
        split_ifs
        · exact (min_le_right _ _).trans (ih hr)
        · exact ih hr

theorem labels_get_mem (records : SparseLabels.Labels (Fin n))
    (hu : (records.map Prod.fst).Nodup) {pair : Fin n × Distance} (hp : pair ∈ records) :
    SparseLabels.get records pair.1 = pair.2 := by
  induction records with
  | nil => simp at hp
  | cons head rest ih =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hu
      rcases List.mem_cons.mp hp with he | hp
      · subst pair
        have hnot : head.1 ∉ SparseLabels.support rest := fun h => hn (List.mem_toFinset.mp h)
        rw [SparseLabels.get_cons, ite_eq_left rfl,
          SparseLabels.get_eq_top_of_not_mem rest hnot, min_top_right]
      · have hne : head.1 ≠ pair.1 := by
          intro he
          exact hn (he ▸ List.mem_map.mpr ⟨pair, hp, rfl⟩)
        rw [SparseLabels.get_cons, ite_eq_right hne]
        exact ih ht hp

theorem serialize_mem (c : Catalog n nb ns nq) (states : BatchDriver.States n nb nq)
    (record : DistanceRecord n) :
    record ∈ serialize c states ↔ ∃ j : Fin nq, ∃ pair ∈ (states.get j).labels,
      pair.1 ∈ (states.get j).settled ∧
      pair.2 ≤ ((c.searches.get j).radius : Distance) ∧
      record = ⟨j.val, pair.1, pair.2.untopD 0⟩ := by
  unfold serialize
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨j, _, hr⟩
    obtain ⟨pair, hp, he⟩ := List.mem_filterMap.mp hr
    by_cases h : pair.1 ∈ (states.get j).settled ∧
        pair.2 ≤ ((c.searches.get j).radius : Distance)
    · have heq : (⟨j.val, pair.1, pair.2.untopD 0⟩ : DistanceRecord n) = record := by
        simpa only [h, and_self, ↓reduceIte, Option.some.injEq] using he
      exact ⟨j, pair, hp, h.1, h.2, heq.symm⟩
    · simp [h] at he
  · rintro ⟨j, pair, hp, hs, hd, rfl⟩
    exact ⟨j, List.mem_finRange j, List.mem_filterMap.mpr ⟨pair, hp, by simp only [hs, hd, and_self, ↓reduceIte]⟩⟩

theorem serialize_lookup (c : Catalog n nb ns nq) (states : BatchDriver.States n nb nq)
    (D : Fin nq → Fin n → Distance)
    (hu : ∀ j, ((states.get j).labels.map Prod.fst).Nodup)
    (hs : ∀ j, (states.get j).settled ⊆ SparseLabels.support (states.get j).labels)
    (he : ∀ j, ∀ v ∈ SparseLabels.support (states.get j).labels,
      SparseLabels.get (states.get j).labels v = D j v)
    (ht : ∀ j v, v ∈ (states.get j).settled ↔ D j v ≤ ((c.searches.get j).radius : Distance))
    (j : Fin nq) (v : Fin n) :
    lookup (serialize c states) j.val v =
      if D j v ≤ ((c.searches.get j).radius : Distance) then D j v else ⊤ := by
  have hrecord {record : DistanceRecord n} (hr : record ∈ serialize c states)
      (hj : record.queryId = j.val) (hv : record.vertex = v) :
      (record.distance : Distance) = D j v ∧ D j v ≤ ((c.searches.get j).radius : Distance) := by
    obtain ⟨k, pair, hp, hsettled, hbound, rfl⟩ := (serialize_mem c states record).mp hr
    have hkj : k = j := Fin.ext hj
    subst k
    have hpv : pair.1 = v := hv
    have hval : pair.2 = D j v := by
      rw [← labels_get_mem _ (hu j) hp, he j pair.1 (hs j hsettled), hpv]
    have hf : pair.2 ≠ ⊤ := by
      intro htop
      rw [htop] at hbound
      exact WithTop.natCast_ne_top _ (top_le_iff.mp hbound)
    exact ⟨(distance_coe_untop hf).trans hval, hval ▸ hbound⟩
  apply le_antisymm
  · by_cases hd : D j v ≤ ((c.searches.get j).radius : Distance)
    · rw [ite_eq_left hd]
      have hvS := (ht j v).mpr hd
      obtain ⟨pair, hp, hpv⟩ := List.mem_map.mp (List.mem_toFinset.mp (hs j hvS))
      have hsup : pair.1 ∈ SparseLabels.support (states.get j).labels :=
        List.mem_toFinset.mpr (List.mem_map.mpr ⟨pair, hp, rfl⟩)
      have hval : pair.2 = D j v := by
        rw [← labels_get_mem _ (hu j) hp, he j pair.1 hsup, hpv]
      let record : DistanceRecord n := ⟨j.val, pair.1, pair.2.untopD 0⟩
      have hr : record ∈ serialize c states := (serialize_mem c states record).mpr
        ⟨j, pair, hp, (by simpa only [hpv] using hvS), (by rwa [hval]), rfl⟩
      have hle := lookup_le (serialize c states) j.val v hr rfl hpv
      exact hle.trans_eq (hrecord hr rfl hpv).1
    · rw [ite_eq_right hd]
      exact le_top
  · apply (le_lookup _ _ _ _).mpr
    intro record hr hj hv
    obtain ⟨hd, hbound⟩ := hrecord hr hj hv
    rw [ite_eq_left hbound]
    exact hd.symm.le

theorem radius_bound (request : Request n) (j : Fin request.queryCount) :
    (request.catalog.searches.get j).radius ≤ request.radius := by
  have h (xs : List ℕ) {r : ℕ} (hr : r ∈ xs) : r ≤ xs.foldr Nat.max 0 := by
    induction xs with
    | nil => simp at hr
    | cons x xs ih =>
        rcases List.mem_cons.mp hr with rfl | hr
        · exact Nat.le_max_left _ _
        · exact (ih hr).trans (Nat.le_max_right _ _)
  apply h
  apply List.mem_map.mpr
  refine ⟨request.catalog.searches.get j, ?_, rfl⟩
  have hj := List.get_mem request.catalog.searches.toList ⟨j.val, by simpa using j.isLt⟩
  simpa only [List.get_eq_getElem, Vector.getElem_toList, Vector.get_eq_getElem] using hj

theorem run_correct (request : Request n) (input : List (Edge n))
    (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (j : Fin request.queryCount) (v : Fin n) :
    lookup (run request input).records j.val v =
      if (fullQueryGraph ((request.explicit ++ input).filterMap (Shared.view request.catalog j))
          (Shared.referenceProblem request.catalog j).blocks.toList request.catalog.scale).dist
          (request.catalog.searches.get j).source v ≤ ((request.catalog.searches.get j).radius : Distance)
      then (fullQueryGraph ((request.explicit ++ input).filterMap (Shared.view request.catalog j))
          (Shared.referenceProblem request.catalog j).blocks.toList request.catalog.scale).dist
          (request.catalog.searches.get j).source v else ⊤ := by
  let c := request.catalog
  let states := (BatchDriver.execute hn c request.explicit input request.workspace (request.radius + 1)).states
  have hinv (k : Fin request.queryCount) :=
    BatchDriver.execute_global_invariant hn c request.explicit input request.workspace (request.radius + 1)
      hs hp hA hx k
  have hg (k : Fin request.queryCount) :
      Global.GlobalInvariant (Shared.referenceProblem c k)
        ((request.explicit ++ input).filterMap (Shared.view c k)) (SparseDriver.observe (states.get k))
        ((c.searches.get k).radius + 1) := by
    have h := (hinv k).1
    rwa [Nat.min_eq_right (Nat.add_le_add_right (radius_bound request k) 1)] at h
  rw [run, dite_eq_left hn]
  dsimp only
  rw [BatchDriver.executeTail_eq]
  change lookup (serialize c states) j.val v = _
  have hser := serialize_lookup c states
    (fun k => Global.target (Shared.referenceProblem c k)
      ((request.explicit ++ input).filterMap (Shared.view c k)))
    (fun k => (hg k).label_unique)
    (fun k => by
      have h : SparseLabels.support (states.get k).labels =
          (states.get k).settled ∪ {(c.searches.get k).source} := (hg k).label_support
      rw [h]
      exact Finset.subset_union_left)
    (fun k => (hg k).label_exact)
    (fun k u => (hg k).settled_iff u |>.trans (distance_lt_succ_iff _ _)) j v
  rw [hser]
  simp only [Global.target, Shared.referenceProblem,
    queryGraph_dist_eq_full, Vector.get_ofFn]
  rfl

end StreamingReachability.Core.BatchAPI
