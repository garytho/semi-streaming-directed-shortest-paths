module

public import StreamingReachability.Core.GuardedPrefix
public import StreamingReachability.Core.GuardedInterface

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.BatchAPI

open StoredEdges

variable {n nb ns nq : ℕ}

theorem serialize_charge_le (c : Catalog n nb ns nq) (states : BatchDriver.States n nb nq)
    (registry : RecordGuard.Registry n nq) (hc : GuardedDriver.Cover registry states)
    (hu : ∀ j, ((states.get j).labels.map Prod.fst).Nodup) :
    ((serialize c states).map fun record => RecordGuard.vertexCharge c record.vertex).sum ≤
      RecordGuard.weight c registry.seen := by
  have local_bound (j : Fin nq) (pairs : SparseLabels.Labels (Fin n)) :
      ((pairs.filterMap fun pair =>
          if pair.1 ∈ (states.get j).settled ∧ pair.2 ≤ ((c.searches.get j).radius : Distance)
          then some (⟨j.val, pair.1, pair.2.untopD 0⟩ : DistanceRecord n) else none).map
        fun record => RecordGuard.vertexCharge c record.vertex).sum ≤
      (pairs.map fun pair => RecordGuard.vertexCharge c pair.1).sum := by
    induction pairs with
    | nil => exact Nat.le_refl _
    | cons pair pairs ih =>
        simp only [List.filterMap_cons, List.map_cons, List.sum_cons]
        split_ifs
        · simpa only [List.map_cons, List.sum_cons] using Nat.add_le_add_left ih
            (RecordGuard.vertexCharge c pair.1)
        · exact ih.trans (Nat.le_add_left _ _)
  have hsection (j : Fin nq) :
      ((states.get j).labels.map fun pair => RecordGuard.vertexCharge c pair.1).sum ≤
        (RecordGuard.verticesAt registry.seen j).sum (RecordGuard.vertexCharge c) := by
    have he := List.sum_toFinset (RecordGuard.vertexCharge c) (hu j)
    rw [List.map_map] at he
    dsimp only [Function.comp_def] at he
    change (SparseLabels.support (states.get j).labels).sum (RecordGuard.vertexCharge c) = _ at he
    rw [← he]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc j v hv⟩
    · intro _ _ _
      exact Nat.zero_le _
  unfold serialize
  rw [sum_flatMap]
  calc
    _ ≤ ((List.finRange nq).map fun j =>
        ((states.get j).labels.map fun pair => RecordGuard.vertexCharge c pair.1).sum).sum := by
      simpa only [← List.ofFn_eq_map, List.sum_ofFn] using
        Finset.sum_le_sum (s := (Finset.univ : Finset (Fin nq))) (fun j _ => local_bound j (states.get j).labels)
    _ ≤ ((List.finRange nq).map fun j =>
        (RecordGuard.verticesAt registry.seen j).sum (RecordGuard.vertexCharge c)).sum := by
      simpa only [← List.ofFn_eq_map, List.sum_ofFn] using
        Finset.sum_le_sum (s := (Finset.univ : Finset (Fin nq))) (fun j _ => hsection j)
    _ = RecordGuard.weight c registry.seen := by
      rw [← List.ofFn_eq_map, List.sum_ofFn, RecordGuard.weight_sections]
      exact Finset.sum_congr rfl (fun j _ => vertex_weight c j _)

theorem runGuarded_charge_le (request : Request n) (budget : ℕ) (input : List (Edge n))
    (hn : 0 < n) (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (result : Result n) (h : runGuarded request budget input = .ok result) :
    replyCharge request result.records ≤ budget := by
  change GuardedDriver.run request budget input = .ok result at h
  unfold GuardedDriver.run at h
  rw [dite_eq_left hn] at h
  cases hi : GuardedDriver.initSources request.catalog budget with
  | error reason => simp [hi] at h
  | ok first =>
      simp only [hi] at h
      cases hd : GuardedDriver.drive hn request.catalog request.explicit input budget request.workspace
          (request.radius + 1) 0 first ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩ with
      | error reason => simp [hd] at h
      | ok pair =>
          obtain ⟨last, output⟩ := pair
          simp only [hd] at h
          have he : (⟨serialize request.catalog output.states, output.passes,
              output.reservations, output.peakRows, output.ordinaryPeak⟩ : Result n) = result :=
            Except.ok.inj h
          have hvalid := GuardedDriver.prefix_registry_valid hn _ _ _ _ _ _ first last output hi hd
          have hcover := GuardedDriver.prefix_cover hn _ _ _ _ _ _ first last output hi hd
          have hstate := GuardedDriver.prefix_state_eq hn _ _ _ _ _ _ first last output hd
          have hshape : ∀ j, ((output.states.get j).labels.map Prod.fst).Nodup := by
            intro j
            rw [hstate]
            exact (BatchDriver.execute_shape hn _ _ _ _ _ hx j).labels_unique
          have hc := serialize_charge_le request.catalog output.states last hcover hshape
          rw [← he]
          exact hc.trans (hvalid.1 ▸ hvalid.2)

theorem runGuarded_coupled (request : Request n) (budget : ℕ) (input : List (Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ request.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    runGuarded request budget input = .ok (run request input) ↔
      replyCharge request (run request input).records ≤ budget := by
  constructor
  · intro h
    exact runGuarded_charge_le request budget input hn hx _ h
  · intro h
    exact GuardedDriver.run_complete request budget input hn hs hp hA hx h

end StreamingReachability.Core.BatchAPI
