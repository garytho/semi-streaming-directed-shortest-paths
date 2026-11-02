module

public import StreamingSSSP.Core.SharedRun

@[expose] public section

namespace StreamingSSSP.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

def runTailAux (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n)) (r : ℕ) :
    ℕ → Vector (Task n nb nq) N → ℕ → ℕ → ℕ → Run n nb nq N
  | 0, tasks, scans, reservations, peak => ⟨tasks, scans, reservations, peak⟩
  | fuel + 1, tasks, scans, reservations, peak =>
      let amount := Packing.load (fun slot => capacity c slot.2) (active tasks)
      let replies := phase hn c stored input r tasks
      let next := commitTasks tasks replies.updates
      runTailAux hn c stored input r fuel next
        (scans + replies.scans) (reservations + amount) (max peak replies.peakRows)

def runTail (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n)) (r fuel : ℕ)
    (tasks : Vector (Task n nb nq) N) : Run n nb nq N :=
  runTailAux hn c stored input r fuel tasks 0 0 0

theorem runTailAux_eq (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r fuel : ℕ) (tasks : Vector (Task n nb nq) N) (scans reservations peak : ℕ) :
    runTailAux hn c stored input r fuel tasks scans reservations peak =
      { tasks := (run hn c stored input r fuel tasks).tasks
        scans := scans + (run hn c stored input r fuel tasks).scans
        reservations := reservations + (run hn c stored input r fuel tasks).reservations
        peakRows := max peak (run hn c stored input r fuel tasks).peakRows } := by
  induction fuel generalizing tasks scans reservations peak with
  | zero => simp [runTailAux, run]
  | succ fuel ih =>
      rw [runTailAux, ih]
      simp only [run, Nat.add_assoc, max_assoc]

theorem runTail_eq (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r fuel : ℕ) (tasks : Vector (Task n nb nq) N) :
    runTail hn c stored input r fuel tasks = run hn c stored input r fuel tasks := by
  simpa only [runTail, Nat.zero_add, Nat.zero_max] using
    runTailAux_eq hn c stored input r fuel tasks 0 0 0

end StreamingSSSP.Core.Shared.Engine
