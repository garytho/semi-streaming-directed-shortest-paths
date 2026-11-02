module

public import StreamingReachability.Core.PassPrefixes

@[expose] public section

namespace StreamingReachability.Core.PassMeter

open StoredEdges

structure Observed (S : Type*) where
  result : Except RecordGuard.Abort S
  passes : ℕ

variable {n nb ns nq N : ℕ}

def packs (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (budget r : ℕ) :
    List (List (Fin N × Shared.Job n nb nq)) → RecordGuard.Registry n nq →
      Observed (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N)
  | [], registry => ⟨.ok (registry, ⟨[], 0, 0, 0⟩), 0⟩
  | slots :: rest, registry =>
      match GuardedEngine.pack hn c stored input budget r slots registry with
      | .error reason => ⟨.error reason, 1⟩
      | .ok (next, first) =>
          let tail := packs hn c stored input budget r rest next
          ⟨tail.result.map fun (last, result) =>
              (last, ⟨first.updates ++ result.updates, result.scans + 1,
                first.reads + result.reads, max first.peakRows result.peakRows⟩),
            tail.passes + 1⟩

def phase (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (budget r : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    Observed (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  packs hn c stored input budget r
    (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)) registry

def runAux (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (budget r : ℕ) :
    ℕ → Vector (Shared.Engine.Task n nb nq) N → RecordGuard.Registry n nq → ℕ → ℕ → ℕ →
      Observed (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N)
  | 0, tasks, registry, scans, reservations, peak =>
      ⟨.ok (registry, ⟨tasks, scans, reservations, peak⟩), scans⟩
  | fuel + 1, tasks, registry, scans, reservations, peak =>
      let amount := Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)
      let next := phase hn c stored input budget r tasks registry
      match next.result with
      | .error reason => ⟨.error reason, scans + next.passes⟩
      | .ok (after, result) =>
          runAux hn c stored input budget r fuel (Shared.Engine.commitTasks tasks result.updates)
            after (scans + result.scans) (reservations + amount) (max peak result.peakRows)

def run (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    Observed (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N) :=
  runAux hn c stored input budget r fuel tasks registry 0 0 0

def round (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ) (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    Observed (RecordGuard.Registry n nq × BatchDriver.Round n nb nq) :=
  let pending := BatchDriver.jobs c r old
  let blocks := run hn c stored input budget r (Nat.log 2 x + 2) (BatchDriver.tasks pending) registry
  match blocks.result with
  | .error reason => ⟨.error reason, blocks.passes⟩
  | .ok (afterBlocks, out) =>
      let replies := BatchDriver.answers pending out.tasks
      match GuardedDriver.ordinary c budget r old stored input afterBlocks with
      | .error reason => ⟨.error reason, blocks.passes + 1⟩
      | .ok (afterEdges, candidates) =>
          ⟨(GuardedDriver.finishQueries c budget r old candidates replies (List.finRange nq) afterEdges old).map
              fun (last, states) =>
                (last, ⟨states, out.scans + 1, out.reservations, out.peakRows, BatchDriver.ordinaryCells candidates⟩),
            blocks.passes + 1⟩

def drive (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x : ℕ) :
    ℕ → ℕ → RecordGuard.Registry n nq → BatchDriver.Run n nb nq →
      Observed (RecordGuard.Registry n nq × BatchDriver.Run n nb nq)
  | 0, _, registry, state => ⟨.ok (registry, state), state.passes⟩
  | fuel + 1, r, registry, state =>
      let step := round hn c stored input budget x r state.states registry
      match step.result with
      | .error reason => ⟨.error reason, state.passes + step.passes⟩
      | .ok (next, result) =>
          drive hn c stored input budget x fuel (r + 1) next
            ⟨result.states, state.passes + result.passes, state.reservations + result.reservations,
              max state.peakRows result.peakRows, max state.ordinaryPeak result.ordinaryPeak⟩

def solve {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ) (input : List (Edge n)) :
    Observed (BatchAPI.Result n) :=
  if hn : 0 < n then
    match GuardedDriver.initSources request.catalog budget with
    | .error reason => ⟨.error reason, 0⟩
    | .ok registry =>
        let out := drive hn request.catalog request.explicit input budget request.workspace
          (request.radius + 1) 0 registry ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩
        ⟨out.result.map fun (_, result) =>
            ⟨BatchAPI.serialize request.catalog result.states, result.passes,
              result.reservations, result.peakRows, result.ordinaryPeak⟩,
          out.passes⟩
  else ⟨.ok ⟨[], 0, 0, 0, 0⟩, 0⟩

end StreamingReachability.Core.PassMeter

namespace StreamingReachability.Core.BatchAPI

def runGuardedMeasured {n : ℕ} (request : Request n) (budget : ℕ) (input : List (StoredEdges.Edge n)) :
    PassMeter.Observed (Result n) :=
  PassMeter.solve request budget input

end StreamingReachability.Core.BatchAPI
