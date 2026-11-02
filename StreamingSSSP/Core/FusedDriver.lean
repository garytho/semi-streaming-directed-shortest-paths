module

public import StreamingSSSP.Core.FusedEngine
public import StreamingSSSP.Core.Interface

@[expose] public section

namespace StreamingSSSP.Core.FusedDriver

open StoredEdges

variable {E : Type*} {n nb ns nq : ℕ}

def round (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (x r : ℕ) (old : BatchDriver.States n nb nq) :
    BatchDriver.Round n nb nq :=
  let pending := BatchDriver.jobs c r old
  let blockRun := FusedEngine.run view hn c stored input r (Nat.log 2 x + 2) (BatchDriver.tasks pending)
  let replies := BatchDriver.answers pending blockRun.tasks
  let scanned := BatchDriver.ordinaryView view c r old stored input
  ⟨Vector.ofFn (fun j => BatchDriver.finishQuery c r j (old.get j) (scanned.state.get j) replies),
    blockRun.scans + 1, blockRun.reservations, blockRun.peakRows, scanned.peakCells⟩

theorem round_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (x r : ℕ) (old : BatchDriver.States n nb nq) :
    round view hn c stored input x r old =
      BatchDriver.round hn c stored (input.filterMap view) x r old := by
  simp only [round, BatchDriver.round, FusedEngine.run_eq, BatchDriver.ordinaryView_state]
  congr 1
  exact Streaming.readPassView_peak _ _ _ _ _

def drive (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (x : ℕ) :
    ℕ → ℕ → BatchDriver.Run n nb nq → BatchDriver.Run n nb nq
  | 0, _, state => state
  | fuel + 1, r, state =>
      let next := round view hn c stored input x r state.states
      drive view hn c stored input x fuel (r + 1)
        ⟨next.states, state.passes + next.passes, state.reservations + next.reservations,
          max state.peakRows next.peakRows, max state.ordinaryPeak next.ordinaryPeak⟩

theorem drive_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (x fuel r : ℕ) (state : BatchDriver.Run n nb nq) :
    drive view hn c stored input x fuel r state =
      BatchDriver.driveAux hn c stored (input.filterMap view) x fuel r state := by
  induction fuel generalizing r state with
  | zero => rfl
  | succ fuel ih =>
      rw [drive, round_eq, ih]
      rfl

def run {E : Type*} {n : ℕ} (request : BatchAPI.Request n)
    (view : E → Option (Edge n)) (input : List E) : BatchAPI.Result n :=
  if hn : 0 < n then
    let result := drive view hn request.catalog request.explicit input request.workspace
      (request.radius + 1) 0 ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩
    ⟨BatchAPI.serialize request.catalog result.states, result.passes,
      result.reservations, result.peakRows, result.ordinaryPeak⟩
  else ⟨[], 0, 0, 0, 0⟩

theorem run_eq {E : Type*} {n : ℕ} (request : BatchAPI.Request n)
    (view : E → Option (Edge n)) (input : List E) :
    run request view input = BatchAPI.run request (input.filterMap view) := by
  unfold run BatchAPI.run
  split_ifs with hn
  · rw [drive_eq]
    rfl
  · rfl

end StreamingSSSP.Core.FusedDriver

namespace StreamingSSSP.Core.BatchAPI

def runFused {E : Type*} {n : ℕ} (request : Request n)
    (view : E → Option (StoredEdges.Edge n)) (input : List E) : Result n :=
  FusedDriver.run request view input

theorem runFused_eq {E : Type*} {n : ℕ} (request : Request n)
    (view : E → Option (StoredEdges.Edge n)) (input : List E) :
    runFused request view input = run request (input.filterMap view) :=
  FusedDriver.run_eq request view input

end StreamingSSSP.Core.BatchAPI
