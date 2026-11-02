module

public import StreamingReachability.Core.GuardedFusedEngine
public import StreamingReachability.Core.GuardedInterface

@[expose] public section

namespace StreamingReachability.Core.GuardedFusedDriver

open StoredEdges

variable {E : Type*} {n nb ns nq : ℕ}

def round (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget x r : ℕ)
    (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × BatchDriver.Round n nb nq) :=
  let pending := BatchDriver.jobs c r old
  match GuardedFusedEngine.run view hn c stored input budget r (Nat.log 2 x + 2)
      (BatchDriver.tasks pending) registry with
  | .error reason => .error reason
  | .ok (afterBlocks, blocks) =>
      let replies := BatchDriver.answers pending blocks.tasks
      match GuardedDriver.ordinaryView view c budget r old stored input afterBlocks with
      | .error reason => .error reason
      | .ok (afterEdges, candidates) =>
          match GuardedDriver.finishQueries c budget r old candidates replies (List.finRange nq) afterEdges old with
          | .error reason => .error reason
          | .ok (last, states) =>
              .ok (last, ⟨states, blocks.scans + 1, blocks.reservations, blocks.peakRows,
                BatchDriver.ordinaryCells candidates⟩)

theorem round_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget x r : ℕ)
    (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    round view hn c stored input budget x r old registry =
      GuardedDriver.round hn c stored (input.filterMap view) budget x r old registry := by
  simp only [round, GuardedFusedEngine.run_eq, GuardedDriver.ordinaryView_eq, GuardedDriver.round]
  rfl

def drive (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget x : ℕ) :
    ℕ → ℕ → RecordGuard.Registry n nq → BatchDriver.Run n nb nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × BatchDriver.Run n nb nq)
  | 0, _, registry, state => .ok (registry, state)
  | fuel + 1, r, registry, state =>
      match round view hn c stored input budget x r state.states registry with
      | .error reason => .error reason
      | .ok (next, step) =>
          drive view hn c stored input budget x fuel (r + 1) next
            ⟨step.states, state.passes + step.passes, state.reservations + step.reservations,
              max state.peakRows step.peakRows, max state.ordinaryPeak step.ordinaryPeak⟩

theorem drive_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget x fuel r : ℕ)
    (registry : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq) :
    drive view hn c stored input budget x fuel r registry state =
      GuardedDriver.drive hn c stored (input.filterMap view) budget x fuel r registry state := by
  induction fuel generalizing r registry state with
  | zero => rfl
  | succ fuel ih =>
      rw [drive, round_eq, GuardedDriver.drive]
      cases he : GuardedDriver.round hn c stored (input.filterMap view) budget x r state.states registry with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, step⟩ := pair
          exact ih (r + 1) next _

def run {E : Type*} {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ)
    (view : E → Option (Edge n)) (input : List E) : Except RecordGuard.Abort (BatchAPI.Result n) :=
  if hn : 0 < n then
    match GuardedDriver.initSources request.catalog budget with
    | .error reason => .error reason
    | .ok registry =>
        match drive view hn request.catalog request.explicit input budget request.workspace
            (request.radius + 1) 0 registry ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩ with
        | .error reason => .error reason
        | .ok (_, result) =>
            .ok ⟨BatchAPI.serialize request.catalog result.states, result.passes,
              result.reservations, result.peakRows, result.ordinaryPeak⟩
  else .ok ⟨[], 0, 0, 0, 0⟩

theorem run_eq {E : Type*} {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ)
    (view : E → Option (Edge n)) (input : List E) :
    run request budget view input = GuardedDriver.run request budget (input.filterMap view) := by
  unfold run GuardedDriver.run
  split_ifs with hn
  · cases hi : GuardedDriver.initSources request.catalog budget with
    | error reason => rfl
    | ok registry =>
        simp only
        rw [drive_eq]
        rfl
  · rfl

end StreamingReachability.Core.GuardedFusedDriver

namespace StreamingReachability.Core.BatchAPI

def runGuardedViewed {E : Type*} {n : ℕ} (request : Request n) (remainingRecordBudget : ℕ)
    (view : E → Option (StoredEdges.Edge n)) (input : List E) : Except Abort (Result n) :=
  GuardedFusedDriver.run request remainingRecordBudget view input

theorem runGuardedViewed_eq {E : Type*} {n : ℕ} (request : Request n) (remainingRecordBudget : ℕ)
    (view : E → Option (StoredEdges.Edge n)) (input : List E) :
    runGuardedViewed request remainingRecordBudget view input =
      runGuarded request remainingRecordBudget (input.filterMap view) :=
  GuardedFusedDriver.run_eq request remainingRecordBudget view input

end StreamingReachability.Core.BatchAPI
