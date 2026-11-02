module

public import StreamingReachability.Core.RecordGuard
public import StreamingReachability.Core.SharedTail

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

def reserveFound (c : Shared.Catalog n nb ns nq) (budget : ℕ) (j : Fin nq)
    (U : Finset (Fin n)) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq) :=
  RecordGuard.reserveMany c budget ((U.sort (· ≤ ·)).map fun v => (j, v)) registry

def evaluate (c : Shared.Catalog n nb ns nq) (budget r : ℕ) (job : Shared.Job n nb nq)
    (f : DistanceArray n) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Task n nb nq) :=
  let B := Shared.block c job.searchId job.blockId
  let K := SparseLabels.support job.sources
  let U := found B K f.get (c.scale * r)
  match reserveFound c budget job.searchId U registry with
  | .error reason => .error reason
  | .ok next =>
      if U.card < job.threshold then
        .ok (next, .finished (Shared.Engine.addSpent job
          (BlockSearch.finish B K (c.scale * r) job.threshold f)))
      else .ok (next, .active (Shared.double c job))

def process (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ) :
    List (Fin N × Shared.Job n nb nq) → List (Shared.Work n nb nq) → RecordGuard.Registry n nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq ×
        RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
  | [], _, registry => .ok (registry, [])
  | _, [], registry => .ok (registry, [])
  | slot :: slots, work :: works, registry =>
      let labels := StoredSearch.run (Shared.storedEdges hn work) (SparseLabels.vector slot.2.sources)
      match evaluate c budget r slot.2 labels registry with
      | .error reason => .error reason
      | .ok (next, task) =>
          match process hn c budget r slots works next with
          | .error reason => .error reason
          | .ok (last, updates) => .ok (last, (slot.1, task) :: updates)

def pack (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (slots : List (Fin N × Shared.Job n nb nq))
    (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  let scanned := Shared.scanPack c (slots.map Prod.snd) stored input
  match process hn c budget r slots scanned.state registry with
  | .error reason => .error reason
  | .ok (next, updates) =>
      .ok (next, ⟨updates, 1, scanned.reads, scanned.peakCells⟩)

def packs (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) :
    List (List (Fin N × Shared.Job n nb nq)) → RecordGuard.Registry n nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N)
  | [], registry => .ok (registry, ⟨[], 0, 0, 0⟩)
  | slots :: rest, registry =>
      match pack hn c stored input budget r slots registry with
      | .error reason => .error reason
      | .ok (next, first) =>
          match packs hn c stored input budget r rest next with
          | .error reason => .error reason
          | .ok (last, tail) =>
              .ok (last, ⟨first.updates ++ tail.updates, tail.scans + 1,
                first.reads + tail.reads, max first.peakRows tail.peakRows⟩)

def phase (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Phase n nb nq N) :=
  packs hn c stored input budget r
    (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)) registry

def runAux (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (budget r : ℕ) :
    ℕ → Vector (Shared.Engine.Task n nb nq) N → RecordGuard.Registry n nq → ℕ → ℕ → ℕ →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N)
  | 0, tasks, registry, scans, reservations, peak => .ok (registry, ⟨tasks, scans, reservations, peak⟩)
  | fuel + 1, tasks, registry, scans, reservations, peak =>
      let amount := Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)
      match phase hn c stored input budget r tasks registry with
      | .error reason => .error reason
      | .ok (next, replies) =>
          runAux hn c stored input budget r fuel (Shared.Engine.commitTasks tasks replies.updates)
            next (scans + replies.scans) (reservations + amount) (max peak replies.peakRows)

def run (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Shared.Engine.Run n nb nq N) :=
  runAux hn c stored input budget r fuel tasks registry 0 0 0

theorem evaluate_erases (c : Shared.Catalog n nb ns nq) (budget r : ℕ) (job : Shared.Job n nb nq)
    (f : DistanceArray n) (old next : RecordGuard.Registry n nq) (task : Shared.Engine.Task n nb nq)
    (h : evaluate c budget r job f old = .ok (next, task)) :
    task = Shared.Engine.evaluate c r job f := by
  unfold evaluate at h
  cases hg : reserveFound c budget job.searchId
      (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)) old with
  | error reason => simp [hg] at h
  | ok middle =>
      simp only [hg] at h
      unfold Shared.Engine.evaluate
      dsimp only
      split_ifs at h ⊢ <;> cases h <;> rfl

theorem evaluate_valid (c : Shared.Catalog n nb ns nq) (budget r : ℕ) (job : Shared.Job n nb nq)
    (f : DistanceArray n) (old next : RecordGuard.Registry n nq) (task : Shared.Engine.Task n nb nq)
    (hv : RecordGuard.Valid c budget old)
    (h : evaluate c budget r job f old = .ok (next, task)) : RecordGuard.Valid c budget next := by
  unfold evaluate at h
  cases hg : reserveFound c budget job.searchId
      (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)) old with
  | error reason => simp [hg] at h
  | ok middle =>
      simp only [hg] at h
      have hm := RecordGuard.reserveMany_valid c budget _ old middle hv hg
      split_ifs at h <;> cases h <;> exact hm

end StreamingReachability.Core.GuardedEngine
