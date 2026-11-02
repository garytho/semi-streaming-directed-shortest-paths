module

public import StreamingReachability.Streaming.Auxiliary
public import StreamingReachability.Core.Main

@[expose] public section

namespace StreamingReachability.Core.AuxPassMeter

open StoredEdges

variable {E : Type*} {n nb ns nq N : ℕ}

def pack (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  let scanned := (Streaming.fusedAuxPass view (Shared.update c) Shared.cells input auxiliary
    (stored.foldl (Shared.update c) ((slots.map Prod.snd).map (Shared.start c)))).erase
  match GuardedEngine.process hn c budget r slots scanned.state registry with
  | .error reason => .error reason
  | .ok (next, updates) => .ok (next, ⟨updates, 1, scanned.reads, scanned.peakCells⟩)

theorem pack_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (registry : RecordGuard.Registry n nq) :
    pack view hn c stored input auxiliary budget r slots registry =
      GuardedEngine.pack hn c stored (input.filterMap view ++ auxiliary) budget r slots registry := by
  simp only [pack, Streaming.fusedAuxPass_erase, GuardedEngine.pack, Shared.scanPack]
  rfl

def ordinary (view : E → Option (Edge n)) (c : Shared.Catalog n nb ns nq)
    (budget r : ℕ) (old : BatchDriver.States n nb nq) (stored : List (Edge n)) (input : List E)
    (auxiliary : List (Edge n)) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Vector (Finset (Fin n)) nq) :=
  match GuardedDriver.ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | .error reason => .error reason
  | .ok (next, candidates) =>
      Streaming.passExceptAux view
        (fun state raw => GuardedDriver.ordinaryQueries c budget r old raw (List.finRange nq) state.1 state.2)
        input auxiliary (next, candidates)

theorem ordinary_eq (view : E → Option (Edge n)) (c : Shared.Catalog n nb ns nq)
    (budget r : ℕ) (old : BatchDriver.States n nb nq) (stored : List (Edge n)) (input : List E)
    (auxiliary : List (Edge n)) (registry : RecordGuard.Registry n nq) :
    ordinary view c budget r old stored input auxiliary registry =
      GuardedDriver.ordinary c budget r old stored (input.filterMap view ++ auxiliary) registry := by
  unfold ordinary GuardedDriver.ordinary
  cases hs : GuardedDriver.ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | error reason => rfl
  | ok pair =>
      simp only [Streaming.passExceptAux_eq, GuardedDriver.ordinaryScan_eq_pass]

def packs (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ) :
    List (List (Fin N × Shared.Job n nb nq)) → RecordGuard.Registry n nq →
      PassMeter.Observed (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N)
  | [], registry => ⟨.ok (registry, ⟨[], 0, 0, 0⟩), 0⟩
  | slots :: rest, registry =>
      match pack view hn c stored input auxiliary budget r slots registry with
      | .error reason => ⟨.error reason, 1⟩
      | .ok (next, first) =>
          let tail := packs view hn c stored input auxiliary budget r rest next
          ⟨tail.result.map fun (last, result) =>
              (last, ⟨first.updates ++ result.updates, result.scans + 1,
                first.reads + result.reads, max first.peakRows result.peakRows⟩),
            tail.passes + 1⟩

theorem packs_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ)
    (packages : List (List (Fin N × Shared.Job n nb nq))) (registry : RecordGuard.Registry n nq) :
    packs view hn c stored input auxiliary budget r packages registry =
      PassMeter.packs hn c stored (input.filterMap view ++ auxiliary) budget r packages registry := by
  induction packages generalizing registry with
  | nil => rfl
  | cons slots rest ih =>
      rw [packs, pack_eq, PassMeter.packs]
      cases GuardedEngine.pack hn c stored (input.filterMap view ++ auxiliary) budget r slots registry with
      | error reason => rfl
      | ok pair => simp only [ih]

def phase (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    PassMeter.Observed (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  packs view hn c stored input auxiliary budget r
    (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)) registry

theorem phase_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    phase view hn c stored input auxiliary budget r tasks registry =
      PassMeter.phase hn c stored (input.filterMap view ++ auxiliary) budget r tasks registry :=
  packs_eq _ _ _ _ _ _ _ _ _ _

def runAux (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r : ℕ) :
    ℕ → Vector (Shared.Engine.Task n nb nq) N → RecordGuard.Registry n nq → ℕ → ℕ → ℕ →
      PassMeter.Observed (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N)
  | 0, tasks, registry, scans, reservations, peak =>
      ⟨.ok (registry, ⟨tasks, scans, reservations, peak⟩), scans⟩
  | fuel + 1, tasks, registry, scans, reservations, peak =>
      let amount := Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)
      let next := phase view hn c stored input auxiliary budget r tasks registry
      match next.result with
      | .error reason => ⟨.error reason, scans + next.passes⟩
      | .ok (after, result) =>
          runAux view hn c stored input auxiliary budget r fuel (Shared.Engine.commitTasks tasks result.updates)
            after (scans + result.scans) (reservations + amount) (max peak result.peakRows)

theorem runAux_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq)
    (scans reservations peak : ℕ) :
    runAux view hn c stored input auxiliary budget r fuel tasks registry scans reservations peak =
      PassMeter.runAux hn c stored (input.filterMap view ++ auxiliary) budget r fuel tasks registry scans reservations peak := by
  induction fuel generalizing tasks registry scans reservations peak with
  | zero => rfl
  | succ fuel ih =>
      rw [runAux, phase_eq, PassMeter.runAux]
      cases (PassMeter.phase hn c stored (input.filterMap view ++ auxiliary) budget r tasks registry).result with
      | error reason => rfl
      | ok pair => exact ih _ pair.1 _ _ _

def run (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    PassMeter.Observed (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N) :=
  runAux view hn c stored input auxiliary budget r fuel tasks registry 0 0 0

theorem run_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    run view hn c stored input auxiliary budget r fuel tasks registry =
      PassMeter.run hn c stored (input.filterMap view ++ auxiliary) budget r fuel tasks registry :=
  runAux_eq view hn c stored input auxiliary budget r fuel tasks registry 0 0 0

def round (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget x r : ℕ)
    (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    PassMeter.Observed (RecordGuard.Registry n nq × BatchDriver.Round n nb nq) :=
  let pending := BatchDriver.jobs c r old
  let blocks := run view hn c stored input auxiliary budget r (Nat.log 2 x + 2) (BatchDriver.tasks pending) registry
  match blocks.result with
  | .error reason => ⟨.error reason, blocks.passes⟩
  | .ok (afterBlocks, out) =>
      let replies := BatchDriver.answers pending out.tasks
      match ordinary view c budget r old stored input auxiliary afterBlocks with
      | .error reason => ⟨.error reason, blocks.passes + 1⟩
      | .ok (afterEdges, candidates) =>
          ⟨(GuardedDriver.finishQueries c budget r old candidates replies (List.finRange nq) afterEdges old).map
              fun (last, states) =>
                (last, ⟨states, out.scans + 1, out.reservations, out.peakRows, BatchDriver.ordinaryCells candidates⟩),
            blocks.passes + 1⟩

theorem round_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget x r : ℕ)
    (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    round view hn c stored input auxiliary budget x r old registry =
      PassMeter.round hn c stored (input.filterMap view ++ auxiliary) budget x r old registry := by
  simp only [round, run_eq, ordinary_eq, PassMeter.round]
  rfl

def drive (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget x : ℕ) :
    ℕ → ℕ → RecordGuard.Registry n nq → BatchDriver.Run n nb nq →
      PassMeter.Observed (RecordGuard.Registry n nq × BatchDriver.Run n nb nq)
  | 0, _, registry, state => ⟨.ok (registry, state), state.passes⟩
  | fuel + 1, r, registry, state =>
      let step := round view hn c stored input auxiliary budget x r state.states registry
      match step.result with
      | .error reason => ⟨.error reason, state.passes + step.passes⟩
      | .ok (next, result) =>
          drive view hn c stored input auxiliary budget x fuel (r + 1) next
            ⟨result.states, state.passes + result.passes, state.reservations + result.reservations,
              max state.peakRows result.peakRows, max state.ordinaryPeak result.ordinaryPeak⟩

theorem drive_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (auxiliary : List (Edge n)) (budget x fuel r : ℕ)
    (registry : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq) :
    drive view hn c stored input auxiliary budget x fuel r registry state =
      PassMeter.drive hn c stored (input.filterMap view ++ auxiliary) budget x fuel r registry state := by
  induction fuel generalizing r registry state with
  | zero => rfl
  | succ fuel ih =>
      rw [drive, round_eq, PassMeter.drive]
      cases (PassMeter.round hn c stored (input.filterMap view ++ auxiliary) budget x r state.states registry).result with
      | error reason => rfl
      | ok pair => exact ih _ pair.1 _

def solve {E : Type*} {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ)
    (view : E → Option (Edge n)) (input : List E) (auxiliary : List (Edge n)) : PassMeter.Observed (BatchAPI.Result n) :=
  if hn : 0 < n then
    match GuardedDriver.initSources request.catalog budget with
    | .error reason => ⟨.error reason, 0⟩
    | .ok registry =>
        let out := drive view hn request.catalog request.explicit input auxiliary budget request.workspace
          (request.radius + 1) 0 registry ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩
        ⟨out.result.map fun (_, result) =>
            ⟨BatchAPI.serialize request.catalog result.states, result.passes,
              result.reservations, result.peakRows, result.ordinaryPeak⟩,
          out.passes⟩
  else ⟨.ok ⟨[], 0, 0, 0, 0⟩, 0⟩

theorem solve_eq {E : Type*} {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ)
    (view : E → Option (Edge n)) (input : List E) (auxiliary : List (Edge n)) :
    solve request budget view input auxiliary = PassMeter.solve request budget (input.filterMap view ++ auxiliary) := by
  unfold solve PassMeter.solve
  split_ifs with hn
  · cases hi : GuardedDriver.initSources request.catalog budget with
    | error reason => rfl
    | ok registry =>
        simp only
        rw [drive_eq]
  · rfl

end StreamingReachability.Core.AuxPassMeter

namespace StreamingReachability.Core.BatchAPI

def runGuardedMeasuredAuxiliary {E : Type*} {n : ℕ} (request : Request n) (budget : ℕ)
    (view : E → Option (StoredEdges.Edge n)) (input : List E) (auxiliary : List (StoredEdges.Edge n)) :
    PassMeter.Observed (Result n) :=
  AuxPassMeter.solve request budget view input auxiliary

theorem runGuardedMeasuredAuxiliary_eq {E : Type*} {n : ℕ} (request : Request n) (budget : ℕ)
    (view : E → Option (StoredEdges.Edge n)) (input : List E) (auxiliary : List (StoredEdges.Edge n)) :
    runGuardedMeasuredAuxiliary request budget view input auxiliary =
      runGuardedMeasured request budget (input.filterMap view ++ auxiliary) :=
  AuxPassMeter.solve_eq request budget view input auxiliary

end StreamingReachability.Core.BatchAPI
