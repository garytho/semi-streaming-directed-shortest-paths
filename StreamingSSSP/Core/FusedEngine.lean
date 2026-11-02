module

public import StreamingSSSP.Core.ScanFusion
public import StreamingSSSP.Core.SharedTail

@[expose] public section

namespace StreamingSSSP.Core.FusedEngine

open StoredEdges

variable {E : Type*} {n nb ns nq N : ℕ}

def pack (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) : Shared.Engine.Phase n nb nq N :=
  let scanned := Shared.scanPackView view c (slots.map Prod.snd) stored input
  ⟨slots.zipWith (Shared.Engine.completeWork hn c r) scanned.state, 1, scanned.reads, scanned.peakCells⟩

theorem pack_updates (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) :
    (pack view hn c stored input r slots).updates =
      (Shared.Engine.executePackResult hn c stored (input.filterMap view) r slots).updates := by
  simp only [pack, Shared.Engine.executePackResult, Shared.scanPackView_state]

theorem pack_peak (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) :
    (pack view hn c stored input r slots).peakRows =
      (Shared.Engine.executePackResult hn c stored (input.filterMap view) r slots).peakRows :=
  Streaming.readPassView_peak _ _ _ _ _

def packs (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ) :
    List (List (Fin N × Shared.Job n nb nq)) → Shared.Engine.Phase n nb nq N
  | [] => ⟨[], 0, 0, 0⟩
  | slots :: rest =>
      let first := pack view hn c stored input r slots
      let tail := packs view hn c stored input r rest
      ⟨first.updates ++ tail.updates, tail.scans + 1,
        first.reads + tail.reads, max first.peakRows tail.peakRows⟩

theorem packs_fields (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ)
    (packages : List (List (Fin N × Shared.Job n nb nq))) :
    (packs view hn c stored input r packages).updates =
        (Shared.Engine.executePacks hn c stored (input.filterMap view) r packages).updates ∧
      (packs view hn c stored input r packages).scans =
        (Shared.Engine.executePacks hn c stored (input.filterMap view) r packages).scans ∧
      (packs view hn c stored input r packages).peakRows =
        (Shared.Engine.executePacks hn c stored (input.filterMap view) r packages).peakRows := by
  induction packages with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons slots rest ih =>
      simp only [packs, Shared.Engine.executePacks, pack_updates, pack_peak, ih.1, ih.2.1, ih.2.2]
      simp

def phase (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N) :
    Shared.Engine.Phase n nb nq N :=
  packs view hn c stored input r
    (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks))

def runAux (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r : ℕ) :
    ℕ → Vector (Shared.Engine.Task n nb nq) N → ℕ → ℕ → ℕ → Shared.Engine.Run n nb nq N
  | 0, tasks, scans, reservations, peak => ⟨tasks, scans, reservations, peak⟩
  | fuel + 1, tasks, scans, reservations, peak =>
      let amount := Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)
      let replies := phase view hn c stored input r tasks
      runAux view hn c stored input r fuel (Shared.Engine.commitTasks tasks replies.updates)
        (scans + replies.scans) (reservations + amount) (max peak replies.peakRows)

theorem runAux_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (scans reservations peak : ℕ) :
    runAux view hn c stored input r fuel tasks scans reservations peak =
      Shared.Engine.runTailAux hn c stored (input.filterMap view) r fuel tasks scans reservations peak := by
  induction fuel generalizing tasks scans reservations peak with
  | zero => rfl
  | succ fuel ih =>
      have h := packs_fields view hn c stored input r
        (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks))
      rw [runAux, ih, Shared.Engine.runTailAux]
      simp only [phase, Shared.Engine.phase] at *
      rw [h.1, h.2.1, h.2.2]

def run (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) : Shared.Engine.Run n nb nq N :=
  runAux view hn c stored input r fuel tasks 0 0 0

theorem run_eq (view : E → Option (Edge n)) (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored : List (Edge n)) (input : List E) (r fuel : ℕ)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) :
    run view hn c stored input r fuel tasks =
      Shared.Engine.runTail hn c stored (input.filterMap view) r fuel tasks :=
  runAux_eq view hn c stored input r fuel tasks 0 0 0

end StreamingSSSP.Core.FusedEngine
