module

public import StreamingReachability.Core.MeasuredErasure

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem runAux_offset (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (registry : RecordGuard.Registry n nq) (scans reservations peak : ℕ) :
    runAux hn c stored input budget r fuel tasks registry scans reservations peak =
      (runAux hn c stored input budget r fuel tasks registry 0 0 0).map fun (last, out) =>
        (last, ⟨out.tasks, scans + out.scans, reservations + out.reservations, max peak out.peakRows⟩) := by
  induction fuel generalizing tasks registry scans reservations peak with
  | zero => simp [runAux, Except.map]
  | succ fuel ih =>
      rw [runAux, runAux]
      cases he : phase hn c stored input budget r tasks registry with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, replies⟩ := pair
          simp only [Nat.zero_add, Nat.zero_max]
          have hL := ih (Shared.Engine.commitTasks tasks replies.updates) next (scans + replies.scans)
            (reservations + Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks))
            (max peak replies.peakRows)
          have hR := ih (Shared.Engine.commitTasks tasks replies.updates) next replies.scans
            (Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)) replies.peakRows
          rw [hL, hR]
          cases runAux hn c stored input budget r fuel (Shared.Engine.commitTasks tasks replies.updates) next 0 0 0 with
          | error reason => rfl
          | ok pair =>
              obtain ⟨last, out⟩ := pair
              simp [Except.map, Nat.add_assoc, max_assoc]

theorem run_succ (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (registry : RecordGuard.Registry n nq) :
    run hn c stored input budget r (fuel + 1) tasks registry =
      match phase hn c stored input budget r tasks registry with
      | .error reason => .error reason
      | .ok (next, replies) =>
          (run hn c stored input budget r fuel (Shared.Engine.commitTasks tasks replies.updates) next).map
            fun (last, out) => (last, ⟨out.tasks, replies.scans + out.scans,
              Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks) + out.reservations,
              max replies.peakRows out.peakRows⟩) := by
  rw [run, runAux]
  cases he : phase hn c stored input budget r tasks registry with
  | error reason => rfl
  | ok pair =>
      obtain ⟨next, replies⟩ := pair
      simp only [Nat.zero_add, Nat.zero_max]
      exact runAux_offset hn c stored input budget r fuel _ next _ _ _

end StreamingReachability.Core.GuardedEngine

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem drive_add (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x first rest r : ℕ) (registry : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq) :
    drive hn c stored input budget x (first + rest) r registry state =
      match drive hn c stored input budget x first r registry state with
      | .error reason => .error reason
      | .ok (next, out) => drive hn c stored input budget x rest (r + first) next out := by
  induction first generalizing r registry state with
  | zero => simp only [Nat.zero_add, Nat.add_zero, drive]
  | succ first ih =>
      rw [Nat.succ_add, drive, drive]
      cases he : round hn c stored input budget x r state.states registry with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, step⟩ := pair
          simp only
          rw [ih]
          have hr : r + 1 + first = r + (first + 1) := by omega
          rw [hr]

end StreamingReachability.Core.GuardedDriver

namespace StreamingReachability.Core.PassMeter

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem runAux_pass_offset (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (registry : RecordGuard.Registry n nq) (scans reservations peak : ℕ) :
    (runAux hn c stored input budget r fuel tasks registry scans reservations peak).passes =
      scans + (run hn c stored input budget r fuel tasks registry).passes := by
  induction fuel generalizing tasks registry scans reservations peak with
  | zero => simp [runAux, run]
  | succ fuel ih =>
      rw [runAux, run, runAux]
      cases he : (phase hn c stored input budget r tasks registry).result with
      | error reason => simp only [Nat.zero_add]
      | ok pair =>
          obtain ⟨next, out⟩ := pair
          simp only [Nat.zero_add, Nat.zero_max]
          rw [ih _ next (scans + out.scans), ih _ next out.scans]
          exact Nat.add_assoc _ _ _

end StreamingReachability.Core.PassMeter
