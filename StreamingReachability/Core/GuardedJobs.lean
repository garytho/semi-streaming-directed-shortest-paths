module

public import StreamingReachability.Core.RegisteredTaskExecution
public import StreamingReachability.Core.GuardedPrefix
public import StreamingReachability.Core.BatchCharges

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.BatchDriver

variable {n nb ns nq : ℕ}

theorem jobs_count (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (hshape : ∀ j, SparseDriver.Shape (old.get j)) :
    (jobs c r old).length ≤ recordCount old := by
  have hraw : (rawJobs c r old).length ≤ ∑ j : Fin nq, (old.get j).cache.length := by
    unfold rawJobs
    rw [List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]
    apply Finset.sum_le_sum
    intro j _
    split_ifs
    · exact List.length_filterMap_le _ _
    · exact Nat.zero_le _
  apply ((List.dedup_sublist (rawJobs c r old)).length_le.trans hraw).trans
  unfold recordCount
  apply Finset.sum_le_sum
  intro j _
  exact (SparseDriver.active_count_le _ (hshape j).active).trans (Nat.le_add_left _ _)

theorem job_origin_injective (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) :
    Function.Injective (fun i : Fin (jobs c r old).length => key ((jobs c r old).get i)) := by
  intro i k he
  let i' : Fin ((jobs c r old).map key).length := ⟨i.val, by simpa using i.isLt⟩
  let k' : Fin ((jobs c r old).map key).length := ⟨k.val, by simpa using k.isLt⟩
  have hg : ((jobs c r old).map key).get i' = ((jobs c r old).map key).get k' := by
    simpa only [List.get_eq_getElem, List.getElem_map] using he
  have heq : i' = k' := (job_key_nodup c r old hu).get_inj_iff.mp hg
  exact Fin.ext (congrArg (fun t : Fin ((jobs c r old).map key).length => t.val) heq)

theorem jobs_registered (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (registry : RecordGuard.Registry n nq) (hshape : ∀ j, SparseDriver.Shape (old.get j))
    (hcover : GuardedDriver.Cover registry old)
    (hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (old.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (old.get j).cache i).known ⊆
        SparseLabels.support (old.get j).labels ∩ c.blocks.get i) :
    ∀ i : Fin (jobs c r old).length,
      GuardedEngine.Registered c registry.seen (key ((jobs c r old).get i))
        ((tasks (jobs c r old)).get i) := by
  intro i
  let job := (jobs c r old).get i
  have hm : job ∈ jobs c r old := List.get_mem _ i
  have he := job_canonical c r old (fun j => (hshape j).unique) hm
  have hs : job.sources = (RecordMap.get Global.emptyBlock (old.get job.searchId).cache job.blockId).known :=
    congrArg Shared.Job.sources he
  rw [tasks, Vector.get_ofFn]
  change GuardedEngine.Registered c registry.seen (key job) (.active job)
  refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
  · rw [GuardedEngine.taskRecords, hs]
    exact (hknown _ _).1
  · change SparseLabels.support job.sources ⊆ _
    rw [hs]
    intro v hv
    obtain ⟨hl, hb⟩ := Finset.mem_inter.mp ((hknown _ _).2 hv)
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcover _ v hl⟩, hb⟩

end StreamingReachability.Core.BatchDriver

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem prefix_task_space (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget x rounds phases : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (first old last : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq)
    (result : Shared.Engine.Run n nb nq (BatchDriver.jobs c rounds state.states).length)
    (hi : initSources c budget = .ok first)
    (hd : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (old, state))
    (he : GuardedEngine.run hn c stored input budget rounds phases
      (BatchDriver.tasks (BatchDriver.jobs c rounds state.states)) old = .ok (last, result)) :
    GuardedEngine.tasksCells result.tasks ≤ 14 * budget ∧
      BatchDriver.stateCells state.states + (2 + 3 * last.seen.card) ≤ 4 + 16 * budget := by
  have hv := prefix_registry_valid hn c stored input budget x rounds first old state hi hd
  have hc := prefix_cover hn c stored input budget x rounds first old state hi hd
  have hdstate := prefix_state_eq hn c stored input budget x rounds first old state hd
  have hshape : ∀ j, SparseDriver.Shape (state.states.get j) := by
    rw [hdstate]
    exact BatchDriver.execute_shape hn c stored input x rounds hx
  have hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (state.states.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (state.states.get j).cache i).known ⊆
        SparseLabels.support (state.states.get j).labels ∩ c.blocks.get i := by
    rw [hdstate]
    exact raw_known_shapes hn c stored input x rounds hs hp hA hx
  have hrec := registered_records c old state.states hshape hc hknown
  have hnslots : (BatchDriver.jobs c rounds state.states).length ≤ budget :=
    (BatchDriver.jobs_count c rounds state.states hshape).trans (hrec.trans (hv.1 ▸ hv.2))
  have hvalid : RecordGuard.Valid c budget last :=
    GuardedEngine.runAux_post hn c stored input budget rounds phases (RecordGuard.Valid c budget)
      (fun job f old next task hv he => GuardedEngine.evaluate_valid c budget rounds job f old next task hv he)
      _ old last 0 0 0 result hv he
  have hregistered := GuardedEngine.runAux_registered hn c stored input budget rounds phases
    (fun i => BatchDriver.key ((BatchDriver.jobs c rounds state.states).get i))
    _ old last 0 0 0 result (BatchDriver.jobs_registered c rounds state.states old hshape hc hknown) he
  constructor
  · exact GuardedEngine.tasksCells_bound c budget last hvalid _
      (BatchDriver.job_origin_injective c rounds state.states (fun j => (hshape j).unique))
      result.tasks hnslots hregistered
  · have hs := registered_state_space c budget old state.states hv hshape hc hknown
    have hr := RecordGuard.registry_cells c budget last hvalid
    omega

end StreamingReachability.Core.GuardedDriver
