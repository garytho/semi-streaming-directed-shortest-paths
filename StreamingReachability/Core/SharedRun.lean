module

public import StreamingReachability.Core.SharedEngine

@[expose] public section

namespace StreamingReachability.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

def commitTasks (tasks : Vector (Task n nb nq) N)
    (updates : RecordMap.Map (Fin N) (Task n nb nq)) : Vector (Task n nb nq) N :=
  Vector.ofFn fun i => RecordMap.get (tasks.get i) updates i

structure Run (n nb nq N : ℕ) where
  tasks : Vector (Task n nb nq) N
  scans : ℕ
  reservations : ℕ
  peakRows : ℕ

def run (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n)) (r : ℕ) :
    ℕ → Vector (Task n nb nq) N → Run n nb nq N
  | 0, tasks => ⟨tasks, 0, 0, 0⟩
  | fuel + 1, tasks =>
      let replies := phase hn c stored input r tasks
      let tasks' := commitTasks tasks replies.updates
      let tail := run hn c stored input r fuel tasks'
      ⟨tail.tasks, replies.scans + tail.scans,
        Packing.load (fun slot => capacity c slot.2) (active tasks) + tail.reservations,
        max replies.peakRows tail.peakRows⟩

noncomputable def iterate (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) : ℕ → Task n nb nq → Task n nb nq
  | 0, task => task
  | fuel + 1, task => iterate hn c stored input r fuel (localStep hn c stored input r task)

theorem run_tasks_get (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r fuel : ℕ) (tasks : Vector (Task n nb nq) N) (i : Fin N) :
    ((run hn c stored input r fuel tasks).tasks).get i =
      iterate hn c stored input r fuel (tasks.get i) := by
  induction fuel generalizing tasks with
  | zero => rfl
  | succ fuel ih =>
      change ((run hn c stored input r fuel
        (commitTasks tasks (phase hn c stored input r tasks).updates)).tasks).get i = _
      rw [ih]
      change iterate hn c stored input r fuel ((nextTasks hn c stored input r tasks).get i) = _
      rw [nextTasks_get]
      rfl

theorem iterate_finished (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r fuel : ℕ) (out : BlockSearch.Outcome n) :
    iterate hn c stored input r fuel (.finished out) = .finished out := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem addSpent_double (c : Catalog n nb ns nq) (job : Job n nb nq) (out : BlockSearch.Outcome n) :
    addSpent (double c job) out =
      addSpent job {out with
        scans := out.scans + 1
        reservations := out.reservations + capacity c job} := by
  cases out
  simp [addSpent, double, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem iterate_searchAux (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r fuel : ℕ) (job : Job n nb nq)
    {out : BlockSearch.Outcome n}
    (hout : ViewedSkeleton.searchAux hn (view c job.searchId) (block c job.searchId job.blockId)
      (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources)
      stored input fuel job.threshold = some out) :
    iterate hn c stored input r fuel (.active job) = .finished (addSpent job out) := by
  induction fuel generalizing job out with
  | zero => simp [ViewedSkeleton.searchAux] at hout
  | succ fuel ih =>
      rw [ViewedSkeleton.searchAux] at hout
      by_cases hs : (found (block c job.searchId job.blockId) (SparseLabels.support job.sources)
          (ViewedSkeleton.labels hn (view c job.searchId) (block c job.searchId job.blockId)
            (SparseLabels.support job.sources) job.threshold
            (SparseLabels.vector job.sources) stored input).get (c.scale * r)).card <
          job.threshold
      · rw [ite_eq_left hs] at hout
        have he := Option.some.inj hout
        subst out
        rw [iterate]
        simp only [localStep, evaluate, hs, ↓reduceIte]
        exact iterate_finished hn c stored input r fuel _
      · rw [ite_eq_right hs] at hout
        obtain ⟨out', ho, he⟩ := Option.map_eq_some_iff.mp hout
        subst out
        rw [iterate]
        simp only [localStep, evaluate, hs, ↓reduceIte]
        rw [ih (double c job) (out := out') ho, addSpent_double]
        rfl

theorem executePacks_scans (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (packs : List (List (Fin N × Job n nb nq))) :
    (executePacks hn c stored input r packs).scans = packs.length := by
  induction packs with
  | nil => rfl
  | cons pack rest ih =>
      simpa only [executePacks, List.length_cons] using congrArg (· + 1) ih

theorem phase_scan_bound (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (tasks : Vector (Task n nb nq) N) :
    n * (phase hn c stored input r tasks).scans ≤
      n + 2 * Packing.load (fun slot => capacity c slot.2) (active tasks) := by
  rw [phase, executePacks_scans]
  exact Packing.pack_scan_bound _ _ _

theorem run_scan_bound (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r fuel : ℕ) (tasks : Vector (Task n nb nq) N) :
    n * (run hn c stored input r fuel tasks).scans ≤
      n * fuel + 2 * (run hn c stored input r fuel tasks).reservations := by
  induction fuel generalizing tasks with
  | zero => simp [run]
  | succ fuel ih =>
      have h := ih (commitTasks tasks (phase hn c stored input r tasks).updates)
      have hp := phase_scan_bound hn c stored input r tasks
      simp only [run, Nat.mul_add, Nat.mul_one] at *
      omega

end StreamingReachability.Core.Shared.Engine
