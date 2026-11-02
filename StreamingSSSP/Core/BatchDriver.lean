module

public import StreamingSSSP.Core.SearchStability
public import StreamingSSSP.Core.SharedTail
public import StreamingSSSP.Core.SparseSpace

@[expose] public section

namespace StreamingSSSP.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

abbrev States (n nb nq : ℕ) := Vector (SparseDriver.State n nb) nq

def initial (c : Shared.Catalog n nb ns nq) : States n nb nq :=
  Vector.ofFn fun j => SparseDriver.initial (SparseDriver.ofCatalog c j)

def rawJobs (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq) :
    List (Shared.Job n nb nq) :=
  (List.finRange nq).flatMap fun j =>
    if r ≤ (c.searches.get j).radius then
      (old.get j).cache.filterMap fun pair =>
        if pair.2.next = (r : Distance)
        then some ⟨j, pair.1, pair.2.known, 1, 0, 0⟩ else none
    else []

def jobs (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq) :
    List (Shared.Job n nb nq) := (rawJobs c r old).dedup

def key (job : Shared.Job n nb nq) : Fin nq × Fin nb := (job.searchId, job.blockId)

def tasks (jobs : List (Shared.Job n nb nq)) : Vector (Shared.Engine.Task n nb nq) jobs.length :=
  Vector.ofFn fun i => .active (jobs.get i)

def answers (jobs : List (Shared.Job n nb nq))
    (done : Vector (Shared.Engine.Task n nb nq) jobs.length) :
    RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)) :=
  (List.finRange jobs.length).map fun i =>
    (key (jobs.get i), match done.get i with | .finished out => some out | .active _ => none)

def accept (A : ℕ) (old : Global.BlockState n) (out : BlockSearch.Outcome n) : Global.BlockResult n :=
  ⟨⟨old.known ++ out.records, roundDistance A out.nextNumerator,
      ScheduleCharge.searched old.charge out.vertices.card, old.reservations + out.reservations⟩,
    out.vertices, out.scans, out.reservations⟩

def searchResults (c : Shared.Catalog n nb ns nq) (r : ℕ) (j : Fin nq) (old : SparseDriver.State n nb)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) :
    RecordMap.Map (Fin nb) (Global.BlockResult n) :=
  old.cache.map fun pair =>
    (pair.1, if pair.2.next = (r : Distance) then
      match RecordMap.get none replies (j, pair.1) with
      | some out => accept c.scale pair.2 out
      | none => ⟨pair.2, ∅, 0, 0⟩
    else ⟨pair.2, ∅, 0, 0⟩)

def ordinaryStep (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (C : Vector (Finset (Fin n)) nq) (raw : Edge n) : Vector (Finset (Fin n)) nq :=
  Vector.ofFn fun j =>
    if r ≤ (c.searches.get j).radius
    then SparseDriver.edgeStep (SparseDriver.ofCatalog c j) r (old.get j) (C.get j) raw
    else C.get j

def ordinaryCells (C : Vector (Finset (Fin n)) nq) : ℕ :=
  nq + 3 * ∑ j : Fin nq, (C.get j).card

def ordinary (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (stored input : List (Edge n)) : Streaming.Metered (Vector (Finset (Fin n)) nq) :=
  Streaming.readPass (ordinaryStep c r old) ordinaryCells input
    (stored.foldl (ordinaryStep c r old) (Vector.replicate nq ∅))

def finishQuery (c : Shared.Catalog n nb ns nq) (r : ℕ) (j : Fin nq)
    (old : SparseDriver.State n nb) (C : Finset (Fin n))
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) :
    SparseDriver.State n nb :=
  if r ≤ (c.searches.get j).radius then
    let found := searchResults c r j old replies
    let U := ((if r = 0 then {(c.searches.get j).source} else ∅) ∪ C ∪
      SparseDriver.resultUnion found) \ old.settled
    { labels := SparseLabels.addNew old.labels U (r : Distance)
      settled := old.settled ∪ U
      cache := SparseDriver.commitCache (SparseDriver.ofCatalog c j) r U
        (found.map fun pair => (pair.1, pair.2.state)) }
  else old

structure Round (n nb nq : ℕ) where
  states : States n nb nq
  passes : ℕ
  reservations : ℕ
  peakRows : ℕ
  ordinaryPeak : ℕ

def round (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (x r : ℕ) (old : States n nb nq) : Round n nb nq :=
  let pending := jobs c r old
  let blockRun := Shared.Engine.runTail hn c stored input r (Nat.log 2 x + 2) (tasks pending)
  let replies := answers pending blockRun.tasks
  let scanned := ordinary c r old stored input
  { states := Vector.ofFn fun j => finishQuery c r j (old.get j) (scanned.state.get j) replies
    passes := blockRun.scans + 1
    reservations := blockRun.reservations
    peakRows := blockRun.peakRows
    ordinaryPeak := scanned.peakCells }

structure Run (n nb nq : ℕ) where
  states : States n nb nq
  passes : ℕ
  reservations : ℕ
  peakRows : ℕ
  ordinaryPeak : ℕ

def execute (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (x : ℕ) :
    ℕ → Run n nb nq
  | 0 => ⟨initial c, 0, 0, 0, 0⟩
  | r + 1 =>
      let old := execute hn c stored input x r
      let next := round hn c stored input x r old.states
      ⟨next.states, old.passes + next.passes, old.reservations + next.reservations,
        max old.peakRows next.peakRows, max old.ordinaryPeak next.ordinaryPeak⟩

def output (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (x R : ℕ) (j : Fin nq) (v : Fin n) : Distance :=
  let state := (execute hn c stored input x (R + 1)).states.get j
  if v ∈ state.settled then SparseLabels.get state.labels v else ⊤

end StreamingSSSP.Core.BatchDriver
