module

public import StreamingReachability.Core.GuardedJobs
public import StreamingReachability.Core.SharedResources

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.Shared

open StoredEdges

variable {n nb ns nq : ℕ}

theorem initial_invariant (c : Catalog n nb ns nq) (jobs : List (Job n nb nq)) (limit : ℕ)
    (hv : ∀ job ∈ jobs, Valid c job) (hc : Packing.load (capacity c) jobs ≤ limit) :
    Invariant c limit (jobs.map (start c)) := by
  constructor
  · intro w hw
    obtain ⟨job, hj, rfl⟩ := List.mem_map.mp hw
    refine ⟨hv job hj, ?_⟩
    constructor
    · simp [start]
    · intro row hr
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
      exact Nat.zero_le _
  · simpa only [List.map_map, Function.comp_def, start, Packing.load] using hc

theorem storedEdges_length (hn : 0 < n) (c : Catalog n nb ns nq) (limit : ℕ)
    (ws : List (Work n nb nq)) (hi : Invariant c limit ws) {w : Work n nb nq} (hw : w ∈ ws) :
    (storedEdges hn w).length ≤ limit := by
  have hr := (hi.1 w hw).2
  have hrows : (storedEdges hn w).length ≤ w.rows.length * w.job.threshold := by
    unfold storedEdges
    rw [List.length_flatMap]
    have hpoint : ∀ row ∈ w.rows, (Skeleton.rowEdges hn row).length ≤ w.job.threshold := by
      intro row hm
      simpa only [Skeleton.rowEdges, List.length_map, Finset.length_sort] using hr.2 row hm
    exact (List.sum_le_sum hpoint).trans_eq (by simp)
  have hcap : capacity c w.job ≤ limit :=
    (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨w, hw, rfl⟩)).trans hi.2
  rw [hr.1] at hrows
  exact hrows.trans hcap

theorem bf_workspace (hn : 0 < n) (c : Catalog n nb ns nq) (limit : ℕ)
    (ws : List (Work n nb nq)) (hi : Invariant c limit ws) {w : Work n nb nq} (hw : w ∈ ws)
    (initial : DistanceArray n) (round scanned : ℕ) :
    workspaceCells (storedEdges hn w) (runRounds (storedEdges hn w) round initial)
      (relaxEdges ((storedEdges hn w).take scanned) (runRounds (storedEdges hn w) round initial)
        (runRounds (storedEdges hn w) round initial)) ≤ 3 * limit + 2 * n := by
  rw [StoredSearch.memory]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 3 (storedEdges_length hn c limit ws hi hw)) _

end StreamingReachability.Core.Shared

namespace StreamingReachability.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem run_ready (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r x fuel : ℕ) (tasks : Vector (Task n nb nq) N) (ht : ∀ i, Ready c x (tasks.get i)) :
    ∀ i, Ready c x ((run hn c stored input r fuel tasks).tasks.get i) := by
  induction fuel generalizing tasks with
  | zero => exact ht
  | succ fuel ih =>
      change ∀ i, Ready c x ((run hn c stored input r fuel (nextTasks hn c stored input r tasks)).tasks.get i)
      exact ih _ (nextTasks_ready hn c stored input r x tasks ht)

theorem ready_capacity (c : Catalog n nb ns nq) (x : ℕ) (tasks : Vector (Task n nb nq) N)
    (ht : ∀ i, Ready c x (tasks.get i)) (hx : 2 * x * x ≤ n)
    {slot : Fin N × Job n nb nq} (hs : slot ∈ active tasks) :
    Valid c slot.2 ∧ capacity c slot.2 ≤ n := by
  have h := ht slot.1
  rw [(active_mem tasks slot.1 slot.2).mp hs] at h
  refine ⟨⟨h.1, h.2.2.1⟩, ?_⟩
  have hm := Nat.mul_le_mul h.2.1 h.2.2.2
  unfold capacity
  nlinarith only [hm, hx]

end StreamingReachability.Core.Shared.Engine

namespace StreamingReachability.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem jobs_ready (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (x r : ℕ) (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ i, Shared.Engine.Ready c x
      ((tasks (jobs c r (execute hn c stored input x r).states)).get i) := by
  let old := (execute hn c stored input x r).states
  intro i
  let job := (jobs c r old).get i
  obtain ⟨bs, hm, _, hsrc, ht, _, _, _⟩ := job_origin c r old (List.get_mem _ i)
  have hshape := execute_shape hn c stored input x r hx job.searchId
  have hget := RecordMap.get_mem Global.emptyBlock (old.get job.searchId).cache hshape.unique hm
  have hg := (execute_global_invariant hn c stored input x r hs hp hA hx job.searchId).2 job.blockId
  have hknown := hg.known_support
  have huniq := hg.known_unique
  simp only [SparseDriver.observe, Vector.get_ofFn, Shared.referenceProblem] at hknown huniq
  rw [hget, ← hsrc] at hknown huniq
  have hnonempty : (SparseLabels.support job.sources).Nonempty := by
    apply Finset.card_pos.mp
    rw [← SparseLabels.length_eq_card job.sources huniq, hsrc]
    exact hshape.active _ hm
  obtain ⟨v, hv⟩ := hnonempty
  have hB : 0 < (Shared.block c job.searchId job.blockId).card := by
    apply Finset.card_pos.mpr
    exact ⟨v, (Finset.mem_inter.mp (hknown ▸ hv)).2⟩
  have hBx := (Shared.block_card_le c job.searchId job.blockId).trans (hx _)
  rw [tasks, Vector.get_ofFn]
  change Shared.Engine.Ready c x (.active job)
  have ht' : job.threshold = 1 := ht
  exact ⟨hB, hBx, by rw [ht']; decide, by rw [ht']; omega⟩

end StreamingReachability.Core.BatchDriver

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem prefix_tasks_ready (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
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
    ∀ i, Shared.Engine.Ready c x (result.tasks.get i) := by
  have hstate := prefix_state_eq hn c stored input budget x rounds first old state hd
  have hstart : ∀ i, Shared.Engine.Ready c x
      ((BatchDriver.tasks (BatchDriver.jobs c rounds state.states)).get i) := by
    subst state
    exact BatchDriver.jobs_ready hn c stored input x rounds hs hp hA hx
  rw [GuardedEngine.run_erases hn c stored input budget rounds phases _ old last result he,
    Shared.Engine.runTail_eq]
  exact Shared.Engine.run_ready hn c stored input rounds x phases _ hstart

end StreamingReachability.Core.GuardedDriver
