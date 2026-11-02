module

public import StreamingSSSP.Core.GuardedEngine
public import StreamingSSSP.Core.Interface
public import StreamingSSSP.Core.VectorStore

@[expose] public section

namespace StreamingSSSP.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

def ordinaryTarget (c : Shared.Catalog n nb ns nq) (r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq) : Option (Fin n) :=
  if r ≤ (c.searches.get j).radius then
    match Shared.view c j raw with
    | none => none
    | some e =>
        if e.source ∈ (old.get j).settled ∧ e.target ∉ (old.get j).settled ∧
            SparseLabels.get (old.get j).labels e.source + (ceilNat c.scale e.weight : Distance) ≤ (r : Distance)
        then some e.target else none
  else none

def ordinaryOne (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq)
    (registry : RecordGuard.Registry n nq) (candidates : Vector (Finset (Fin n)) nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Vector (Finset (Fin n)) nq) :=
  match ordinaryTarget c r old raw j with
  | none => .ok (registry, candidates)
  | some v =>
      match RecordGuard.reserve c budget (j, v) registry with
      | .error reason => .error reason
      | .ok next => .ok (next, VectorStore.set candidates j (insert v (candidates.get j)))

def ordinaryQueries (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) :
    List (Fin nq) → RecordGuard.Registry n nq → Vector (Finset (Fin n)) nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × Vector (Finset (Fin n)) nq)
  | [], registry, candidates => .ok (registry, candidates)
  | j :: js, registry, candidates =>
      match ordinaryOne c budget r old raw j registry candidates with
      | .error reason => .error reason
      | .ok (next, found) => ordinaryQueries c budget r old raw js next found

def ordinaryScan (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) :
    List (Edge n) → RecordGuard.Registry n nq → Vector (Finset (Fin n)) nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × Vector (Finset (Fin n)) nq)
  | [], registry, candidates => .ok (registry, candidates)
  | raw :: rest, registry, candidates =>
      match ordinaryQueries c budget r old raw (List.finRange nq) registry candidates with
      | .error reason => .error reason
      | .ok (next, found) => ordinaryScan c budget r old rest next found

def ordinary (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Vector (Finset (Fin n)) nq) :=
  match ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | .error reason => .error reason
  | .ok (next, found) => ordinaryScan c budget r old input next found

def proposed (c : Shared.Catalog n nb ns nq) (r : ℕ) (j : Fin nq)
    (old : SparseDriver.State n nb) (C : Finset (Fin n))
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) : Finset (Fin n) :=
  if r ≤ (c.searches.get j).radius then
    ((if r = 0 then {(c.searches.get j).source} else ∅) ∪ C ∪
      SparseDriver.resultUnion (BatchDriver.searchResults c r j old replies)) \ old.settled
  else ∅

def finishQueries (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) :
    List (Fin nq) → RecordGuard.Registry n nq → BatchDriver.States n nb nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × BatchDriver.States n nb nq)
  | [], registry, acc => .ok (registry, acc)
  | j :: js, registry, acc =>
      match GuardedEngine.reserveFound c budget j (proposed c r j (old.get j) (C.get j) replies) registry with
      | .error reason => .error reason
      | .ok next =>
          finishQueries c budget r old C replies js next
            (VectorStore.set acc j (BatchDriver.finishQuery c r j (old.get j) (C.get j) replies))

def round (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ) (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × BatchDriver.Round n nb nq) :=
  let pending := BatchDriver.jobs c r old
  match GuardedEngine.run hn c stored input budget r (Nat.log 2 x + 2) (BatchDriver.tasks pending) registry with
  | .error reason => .error reason
  | .ok (afterBlocks, blocks) =>
      let replies := BatchDriver.answers pending blocks.tasks
      match ordinary c budget r old stored input afterBlocks with
      | .error reason => .error reason
      | .ok (afterEdges, candidates) =>
          match finishQueries c budget r old candidates replies (List.finRange nq) afterEdges old with
          | .error reason => .error reason
          | .ok (last, states) =>
              .ok (last, ⟨states, blocks.scans + 1, blocks.reservations, blocks.peakRows,
                BatchDriver.ordinaryCells candidates⟩)

def drive (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x : ℕ) :
    ℕ → ℕ → RecordGuard.Registry n nq → BatchDriver.Run n nb nq →
      Except RecordGuard.Abort (RecordGuard.Registry n nq × BatchDriver.Run n nb nq)
  | 0, _, registry, state => .ok (registry, state)
  | fuel + 1, r, registry, state =>
      match round hn c stored input budget x r state.states registry with
      | .error reason => .error reason
      | .ok (next, step) =>
          drive hn c stored input budget x fuel (r + 1) next
            ⟨step.states, state.passes + step.passes, state.reservations + step.reservations,
              max state.peakRows step.peakRows, max state.ordinaryPeak step.ordinaryPeak⟩

def initSources (c : Shared.Catalog n nb ns nq) (budget : ℕ) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq) :=
  RecordGuard.reserveMany c budget
    ((List.finRange nq).map fun j => (j, (c.searches.get j).source)) RecordGuard.empty

def run {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ) (input : List (Edge n)) :
    Except RecordGuard.Abort (BatchAPI.Result n) :=
  if hn : 0 < n then
    match initSources request.catalog budget with
    | .error reason => .error reason
    | .ok registry =>
        match drive hn request.catalog request.explicit input budget request.workspace
            (request.radius + 1) 0 registry ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩ with
        | .error reason => .error reason
        | .ok (_, result) =>
            .ok ⟨BatchAPI.serialize request.catalog result.states, result.passes,
              result.reservations, result.peakRows, result.ordinaryPeak⟩
  else .ok ⟨[], 0, 0, 0, 0⟩

inductive Program (n : ℕ) where
  | solve (request : BatchAPI.Request n) (remainingRecordBudget : ℕ)

def interpret {n : ℕ} (input : List (Edge n)) : Program n → Except RecordGuard.Abort (BatchAPI.SparseReply n)
  | .solve request budget => (run request budget input).map BatchAPI.Result.records

end StreamingSSSP.Core.GuardedDriver
