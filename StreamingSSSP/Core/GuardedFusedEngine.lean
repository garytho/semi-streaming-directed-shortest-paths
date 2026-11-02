module

public import StreamingSSSP.Core.FusedScans

@[expose] public section

namespace StreamingSSSP.Core.GuardedFusedEngine

open StoredEdges

variable {E : Type*} {n nb ns nq N : ℕ}

def pack (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  let scanned := (Shared.scanPackFused view c (slots.map Prod.snd) stored input).erase
  match GuardedEngine.process hn c budget r slots scanned.state registry with
  | .error reason => .error reason
  | .ok (next, updates) => .ok (next, ⟨updates, 1, scanned.reads, scanned.peakCells⟩)

theorem pack_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (registry : RecordGuard.Registry n nq) :
    pack view hn c stored input budget r slots registry =
      GuardedEngine.pack hn c stored (input.filterMap view) budget r slots registry := by
  simp only [pack, Shared.scanPackFused_erase, GuardedEngine.pack]
  rfl

def packs (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ) :
    List (List (Fin N × Shared.Job n nb nq)) → RecordGuard.Registry n nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N)
  | [], registry => .ok (registry, ⟨[], 0, 0, 0⟩)
  | slots :: rest, registry =>
      match pack view hn c stored input budget r slots registry with
      | .error reason => .error reason
      | .ok (next, first) =>
          match packs view hn c stored input budget r rest next with
          | .error reason => .error reason
          | .ok (last, tail) =>
              .ok (last, ⟨first.updates ++ tail.updates, tail.scans + 1,
                first.reads + tail.reads, max first.peakRows tail.peakRows⟩)

theorem packs_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ)
    (packages : List (List (Fin N × Shared.Job n nb nq))) (registry : RecordGuard.Registry n nq) :
    packs view hn c stored input budget r packages registry =
      GuardedEngine.packs hn c stored (input.filterMap view) budget r packages registry := by
  induction packages generalizing registry with
  | nil => rfl
  | cons slots rest ih =>
      rw [packs, pack_eq, GuardedEngine.packs]
      cases he : GuardedEngine.pack hn c stored (input.filterMap view) budget r slots registry with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, first⟩ := pair
          simp only [ih]
          rfl

def phase (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  packs view hn c stored input budget r
    (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)) registry

theorem phase_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    phase view hn c stored input budget r tasks registry =
      GuardedEngine.phase hn c stored (input.filterMap view) budget r tasks registry :=
  packs_eq _ _ _ _ _ _ _ _ _

def runAux (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r : ℕ) :
    ℕ → Vector (Shared.Engine.Task n nb nq) N → RecordGuard.Registry n nq → ℕ → ℕ → ℕ →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N)
  | 0, tasks, registry, scans, reservations, peak => .ok (registry, ⟨tasks, scans, reservations, peak⟩)
  | fuel + 1, tasks, registry, scans, reservations, peak =>
      let amount := Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)
      match phase view hn c stored input budget r tasks registry with
      | .error reason => .error reason
      | .ok (next, replies) =>
          runAux view hn c stored input budget r fuel (Shared.Engine.commitTasks tasks replies.updates)
            next (scans + replies.scans) (reservations + amount) (max peak replies.peakRows)

theorem runAux_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq)
    (scans reservations peak : ℕ) :
    runAux view hn c stored input budget r fuel tasks registry scans reservations peak =
      GuardedEngine.runAux hn c stored (input.filterMap view) budget r fuel tasks registry scans reservations peak := by
  induction fuel generalizing tasks registry scans reservations peak with
  | zero => rfl
  | succ fuel ih =>
      rw [runAux, phase_eq, GuardedEngine.runAux]
      cases he : GuardedEngine.phase hn c stored (input.filterMap view) budget r tasks registry with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, replies⟩ := pair
          exact ih _ next _ _ _

def run (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N) :=
  runAux view hn c stored input budget r fuel tasks registry 0 0 0

theorem run_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (budget r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    run view hn c stored input budget r fuel tasks registry =
      GuardedEngine.run hn c stored (input.filterMap view) budget r fuel tasks registry :=
  runAux_eq view hn c stored input budget r fuel tasks registry 0 0 0

end StreamingSSSP.Core.GuardedFusedEngine
