module

public import StreamingReachability.Core.AllowedRecords
public import StreamingReachability.Core.GuardedOrdinaryProofs

@[expose] public section

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem ordinaryTarget_allowed (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (raw : Edge n) (hm : raw ∈ stored ++ input)
    (j : Fin nq) (v : Fin n)
    (h : ordinaryTarget c r (BatchDriver.execute hn c stored input x r).states raw j = some v) :
    (j, v) ∈ RecordGuard.allowed c stored input := by
  let old := (BatchDriver.execute hn c stored input x r).states
  change ordinaryTarget c r old raw j = some v at h
  by_cases ha : r ≤ (c.searches.get j).radius
  · have hg := (BatchDriver.execute_global_invariant hn c stored input x r hs hp hA hx j).1
    rw [Nat.min_eq_left (by omega)] at hg
    unfold ordinaryTarget at h
    rw [ite_eq_left ha] at h
    cases hv : Shared.view c j raw with
    | none => simp [hv] at h
    | some e =>
        rw [hv] at h
        by_cases he : e.source ∈ (old.get j).settled ∧ e.target ∉ (old.get j).settled ∧
            SparseLabels.get (old.get j).labels e.source + (ceilNat c.scale e.weight : Distance) ≤ (r : Distance)
        · have hev : e.target = v := by simpa [he] using h
          subst v
          have hlabels : SparseLabels.get (old.get j).labels e.source =
              Global.target (Shared.referenceProblem c j)
                ((stored ++ input).filterMap (Shared.view c j)) e.source :=
            hg.label_exact e.source (show e.source ∈ SparseLabels.support (old.get j).labels from by
              have hsup : SparseLabels.support (old.get j).labels =
                  (old.get j).settled ∪ {(c.searches.get j).source} := hg.label_support
              rw [hsup]
              exact Finset.mem_union_left _ he.1)
          have hedge : e ∈ (stored ++ input).filterMap (Shared.view c j) :=
            List.mem_filterMap.mpr ⟨raw, hm, hv⟩
          have hqe : queryGraph ((stored ++ input).filterMap (Shared.view c j))
              (Shared.referenceProblem c j).blocks.toList c.scale e.source e.target ≤
              (ceilNat c.scale e.weight : Distance) :=
            (Query.le_ordinary _ _ _ _ _).trans
              (roundDistance_mono hA (graphOfEdges_le_edge _ hedge))
          have hd : Global.target (Shared.referenceProblem c j)
              ((stored ++ input).filterMap (Shared.view c j)) e.target ≤ (r : Distance) := by
            calc
              _ ≤ Global.target (Shared.referenceProblem c j)
                  ((stored ++ input).filterMap (Shared.view c j)) e.source +
                  queryGraph ((stored ++ input).filterMap (Shared.view c j))
                    (Shared.referenceProblem c j).blocks.toList c.scale e.source e.target :=
                Graph.dist_le_dist_add_edge _ _ _ _
              _ ≤ _ := add_le_add le_rfl hqe
              _ ≤ _ := by
                have hw := he.2.2
                rwa [hlabels] at hw
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, hd.trans (WithTop.coe_le_coe.mpr ha)⟩
        · simp [he] at h
  · simp [ordinaryTarget, ha] at h

theorem proposed_allowed (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (j : Fin nq) (v : Fin n)
    (hv : v ∈ proposed c r j ((BatchDriver.execute hn c stored input x r).states.get j)
      ((BatchDriver.ordinary c r (BatchDriver.execute hn c stored input x r).states stored input).state.get j)
      (BatchDriver.replyMap hn c stored input x r (BatchDriver.execute hn c stored input x r).states)) :
    (j, v) ∈ RecordGuard.allowed c stored input := by
  let old := (BatchDriver.execute hn c stored input x r).states
  by_cases ha : r ≤ (c.searches.get j).radius
  · have hvnew : v ∈ ((BatchDriver.execute hn c stored input x (r + 1)).states.get j).settled := by
      change v ∈ ((BatchDriver.round hn c stored input x r old).states.get j).settled
      simp only [BatchDriver.round, Shared.Engine.runTail_eq, Vector.get_ofFn]
      change v ∈ (BatchDriver.finishQuery c r j (old.get j)
        ((BatchDriver.ordinary c r old stored input).state.get j)
        (BatchDriver.replyMap hn c stored input x r old)).settled
      rw [BatchDriver.finishQuery, ite_eq_left ha]
      apply Finset.mem_union_right
      simpa only [proposed, ha, ↓reduceIte] using hv
    have hg := (BatchDriver.execute_global_invariant hn c stored input x (r + 1) hs hp hA hx j).1
    rw [Nat.min_eq_left (Nat.add_le_add_right ha 1)] at hg
    have hd := (distance_lt_succ_iff _ r).mp ((hg.settled_iff v).mp hvnew)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hd.trans (WithTop.coe_le_coe.mpr ha)⟩
  · simp [proposed, ha] at hv

end StreamingReachability.Core.GuardedDriver
