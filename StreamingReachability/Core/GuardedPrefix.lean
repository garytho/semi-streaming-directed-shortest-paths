module

public import StreamingReachability.Core.GuardedCoverage

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem raw_known_shapes (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ j i,
      ((RecordMap.get Global.emptyBlock ((BatchDriver.execute hn c stored input x r).states.get j).cache i).known.map
        Prod.fst).Nodup ∧
      SparseLabels.support
          (RecordMap.get Global.emptyBlock ((BatchDriver.execute hn c stored input x r).states.get j).cache i).known ⊆
        SparseLabels.support ((BatchDriver.execute hn c stored input x r).states.get j).labels ∩ c.blocks.get i := by
  intro j i
  have hg := BatchDriver.execute_global_invariant hn c stored input x r hs hp hA hx j
  have hknown := (hg.2 i).known_support
  have huniq := (hg.2 i).known_unique
  simp only [SparseDriver.observe, Vector.get_ofFn, Shared.referenceProblem] at hknown huniq
  refine ⟨huniq, ?_⟩
  intro v hv
  rw [hknown] at hv
  obtain ⟨hsettled, hblock⟩ := Finset.mem_inter.mp hv
  have hlabel : SparseLabels.support ((BatchDriver.execute hn c stored input x r).states.get j).labels =
      ((BatchDriver.execute hn c stored input x r).states.get j).settled ∪ {(c.searches.get j).source} :=
    hg.1.label_support
  apply Finset.mem_inter.mpr
  refine ⟨?_, Finset.inter_subset_left hblock⟩
  rw [hlabel]
  exact Finset.mem_union_left _ hsettled

theorem prefix_registry_valid (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x rounds : ℕ) (first last : RecordGuard.Registry n nq) (result : BatchDriver.Run n nb nq)
    (hi : initSources c budget = .ok first)
    (h : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (last, result)) : RecordGuard.Valid c budget last :=
  drive_valid hn c stored input budget x rounds 0 first last _ result (initSources_valid c budget first hi) h

theorem prefix_cover (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x rounds : ℕ) (first last : RecordGuard.Registry n nq) (result : BatchDriver.Run n nb nq)
    (hi : initSources c budget = .ok first)
    (h : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (last, result)) : Cover last result.states :=
  drive_cover hn c stored input budget x rounds 0 first last _ result (initSources_cover c budget first hi) h

theorem prefix_state_eq (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x rounds : ℕ) (first last : RecordGuard.Registry n nq) (result : BatchDriver.Run n nb nq)
    (h : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (last, result)) :
    result = BatchDriver.execute hn c stored input x rounds := by
  have he := drive_erases hn c stored input budget x rounds 0 first last _ result h
  change result = BatchDriver.executeTail hn c stored input x rounds at he
  rwa [BatchDriver.executeTail_eq] at he

theorem prefix_space (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x rounds : ℕ) (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (first last : RecordGuard.Registry n nq) (result : BatchDriver.Run n nb nq)
    (hi : initSources c budget = .ok first)
    (h : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (last, result)) :
    BatchDriver.stateCells result.states + (2 + 3 * last.seen.card) ≤ 4 + 16 * budget := by
  have he := prefix_state_eq hn c stored input budget x rounds first last result h
  have hv := prefix_registry_valid hn c stored input budget x rounds first last result hi h
  have hc := prefix_cover hn c stored input budget x rounds first last result hi h
  have hshape : ∀ j, SparseDriver.Shape (result.states.get j) := by
    rw [he]
    exact BatchDriver.execute_shape hn c stored input x rounds hx
  have hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (result.states.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (result.states.get j).cache i).known ⊆
        SparseLabels.support (result.states.get j).labels ∩ c.blocks.get i := by
    rw [he]
    exact raw_known_shapes hn c stored input x rounds hs hp hA hx
  have hs := registered_state_space c budget last result.states hv hshape hc hknown
  have hr := RecordGuard.registry_cells c budget last hv
  omega

end StreamingReachability.Core.GuardedDriver
