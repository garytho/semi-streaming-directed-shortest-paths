module

public import StreamingReachability.Core.SearchStability

@[expose] public section

namespace StreamingReachability.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

def taskWork : Task n nb nq → ℕ
  | .active job => job.spentReservations
  | .finished out => out.reservations

def taskCapacity (c : Catalog n nb ns nq) : Task n nb nq → ℕ
  | .active job => capacity c job
  | .finished _ => 0

def workSum (tasks : Vector (Task n nb nq) N) : ℕ := ∑ i : Fin N, taskWork (tasks.get i)

theorem active_load (c : Catalog n nb ns nq) (tasks : Vector (Task n nb nq) N) :
    Packing.load (fun slot => capacity c slot.2) (active tasks) =
      ∑ i : Fin N, taskCapacity c (tasks.get i) := by
  have h (indices : List (Fin N)) :
      Packing.load (fun slot : Fin N × Job n nb nq => capacity c slot.2)
        (indices.filterMap fun i => match tasks.get i with
          | .active job => some (i, job) | .finished _ => none) =
        (indices.map fun i => taskCapacity c (tasks.get i)).sum := by
    induction indices with
    | nil => rfl
    | cons i is ih =>
        cases ht : tasks.get i with
        | active job =>
            simpa only [Packing.load, List.filterMap_cons, ht, taskCapacity,
              List.map_cons, List.sum_cons] using congrArg (capacity c job + ·) ih
        | finished out =>
            simpa only [Packing.load, List.filterMap_cons, ht, taskCapacity,
              List.map_cons, List.sum_cons, Nat.zero_add] using ih
  rw [← List.sum_ofFn, List.ofFn_eq_map]
  exact h (List.finRange N)

theorem localStep_work (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (task : Task n nb nq) :
    taskWork (localStep hn c stored input r task) = taskWork task + taskCapacity c task := by
  cases task with
  | finished out => simp [localStep, taskWork, taskCapacity]
  | active job =>
      unfold localStep evaluate
      dsimp only
      split_ifs <;>
        simp only [taskWork, taskCapacity, addSpent, double, BlockSearch.finish, capacity]

theorem nextTasks_work (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (tasks : Vector (Task n nb nq) N) :
    workSum (nextTasks hn c stored input r tasks) =
      workSum tasks + Packing.load (fun slot => capacity c slot.2) (active tasks) := by
  rw [active_load]
  unfold workSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [nextTasks_get, localStep_work]

theorem run_work (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r fuel : ℕ) (tasks : Vector (Task n nb nq) N) :
    workSum (run hn c stored input r fuel tasks).tasks =
      workSum tasks + (run hn c stored input r fuel tasks).reservations := by
  induction fuel generalizing tasks with
  | zero => simp [run]
  | succ fuel ih =>
      change workSum (run hn c stored input r fuel
        (commitTasks tasks (phase hn c stored input r tasks).updates)).tasks = _
      rw [ih]
      change workSum (nextTasks hn c stored input r tasks) +
        (run hn c stored input r fuel (nextTasks hn c stored input r tasks)).reservations = _
      rw [nextTasks_work]
      simp only [run, Nat.add_assoc]
      rfl

def Ready (c : Catalog n nb ns nq) (x : ℕ) : Task n nb nq → Prop
  | .finished _ => True
  | .active job => 0 < (block c job.searchId job.blockId).card ∧
      (block c job.searchId job.blockId).card ≤ x ∧ 0 < job.threshold ∧ job.threshold ≤ 2 * x

theorem ready_step (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r x : ℕ) (task : Task n nb nq) (ht : Ready c x task) :
    Ready c x (localStep hn c stored input r task) := by
  cases task with
  | finished out => trivial
  | active job =>
      unfold localStep evaluate
      dsimp only
      split_ifs with hs
      · trivial
      · have hc := BlockSearch.found_card_le (block c job.searchId job.blockId)
          (SparseLabels.support job.sources)
          (ViewedSkeleton.labels hn (view c job.searchId) (block c job.searchId job.blockId)
            (SparseLabels.support job.sources) job.threshold (SparseLabels.vector job.sources) stored input).get
          (c.scale * r)
        obtain ⟨hb0, hbx, ht0, _⟩ := ht
        exact ⟨hb0, hbx, by dsimp [double]; omega, by dsimp [double]; omega⟩

theorem nextTasks_ready (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r x : ℕ) (tasks : Vector (Task n nb nq) N) (ht : ∀ i, Ready c x (tasks.get i)) :
    ∀ i, Ready c x ((nextTasks hn c stored input r tasks).get i) := by
  intro i
  rw [nextTasks_get]
  exact ready_step hn c stored input r x _ (ht i)

theorem executePacks_memory (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (packs : List (List (Fin N × Job n nb nq)))
    (hv : ∀ pack ∈ packs, ∀ slot ∈ pack, Valid c slot.2)
    (hc : ∀ pack ∈ packs, Packing.load (fun slot => capacity c slot.2) pack ≤ n) :
    (executePacks hn c stored input r packs).peakRows ≤ 14 * n := by
  induction packs with
  | nil => exact Nat.zero_le _
  | cons pack rest ih =>
      apply max_le
      · apply scanPack_memory c _ stored input n
        · intro job hj
          obtain ⟨slot, hs, rfl⟩ := List.mem_map.mp hj
          exact hv pack (by simp) slot hs
        · unfold Packing.load
          rw [List.map_map]
          exact hc pack (by simp)
      · exact ih (fun p hp => hv p (by simp [hp])) (fun p hp => hc p (by simp [hp]))

theorem phase_memory (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r x : ℕ) (tasks : Vector (Task n nb nq) N)
    (ht : ∀ i, Ready c x (tasks.get i)) (hx : 2 * x * x ≤ n) :
    (phase hn c stored input r tasks).peakRows ≤ 14 * n := by
  have hv : ∀ slot ∈ active tasks, Valid c slot.2 := by
    rintro ⟨i, job⟩ hmem
    have h := ht i
    rw [(active_mem tasks i job).mp hmem] at h
    exact ⟨h.1, h.2.2.1⟩
  have hc : ∀ slot ∈ active tasks, capacity c slot.2 ≤ n := by
    rintro ⟨i, job⟩ hmem
    have h := ht i
    rw [(active_mem tasks i job).mp hmem] at h
    have hm := Nat.mul_le_mul h.2.1 h.2.2.2
    unfold capacity
    nlinarith only [hm, hx]
  apply executePacks_memory hn c stored input r _
  · intro pack hp slot hs
    have hm : slot ∈ (Packing.pack n (fun slot => capacity c slot.2) (active tasks)).flatten :=
      List.mem_flatten.mpr ⟨pack, hp, hs⟩
    rw [Packing.pack_flatten] at hm
    exact hv slot (List.mem_reverse.mp hm)
  · exact Packing.pack_bounded _ _ _ hc

theorem run_memory (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r x fuel : ℕ) (tasks : Vector (Task n nb nq) N)
    (ht : ∀ i, Ready c x (tasks.get i)) (hx : 2 * x * x ≤ n) :
    (run hn c stored input r fuel tasks).peakRows ≤ 14 * n := by
  induction fuel generalizing tasks with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
      apply max_le (phase_memory hn c stored input r x tasks ht hx)
      exact ih _ (nextTasks_ready hn c stored input r x tasks ht)

end StreamingReachability.Core.Shared.Engine
