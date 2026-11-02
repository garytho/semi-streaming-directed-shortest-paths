module

public import StreamingReachability.Core.BatchTail

@[expose] public section

namespace StreamingReachability.Core.BatchAPI

open StoredEdges

abbrev Query := Shared.Search
abbrev Catalog := Shared.Catalog

structure Request (n : ℕ) where
  blockCount : ℕ
  setCount : ℕ
  queryCount : ℕ
  explicit : List (Edge n)
  catalog : Catalog n blockCount setCount queryCount
  workspace : ℕ

def Request.ofCatalog {n nb ns nq : ℕ} (explicit : List (Edge n))
    (catalog : Catalog n nb ns nq) (workspace : ℕ) : Request n :=
  ⟨nb, ns, nq, explicit, catalog, workspace⟩

def Request.radius {n : ℕ} (request : Request n) : ℕ :=
  (request.catalog.searches.toList.map Shared.Search.radius).foldr Nat.max 0

structure DistanceRecord (n : ℕ) where
  queryId : ℕ
  vertex : Fin n
  distance : ℕ
  deriving DecidableEq, Repr

abbrev SparseReply (n : ℕ) := List (DistanceRecord n)

def serialize {n nb ns nq : ℕ} (catalog : Catalog n nb ns nq)
    (states : BatchDriver.States n nb nq) : SparseReply n :=
  (List.finRange nq).flatMap fun j =>
    (states.get j).labels.filterMap fun record =>
      if record.1 ∈ (states.get j).settled ∧
          record.2 ≤ ((catalog.searches.get j).radius : Distance)
      then some ⟨j.val, record.1, record.2.untopD 0⟩ else none

structure Result (n : ℕ) where
  records : SparseReply n
  passes : ℕ
  reservations : ℕ
  peakSkeletonCells : ℕ
  peakOrdinaryCells : ℕ

def run {n : ℕ} (request : Request n) (input : List (Edge n)) : Result n :=
  if hn : 0 < n then
    let result := BatchDriver.executeTail hn request.catalog request.explicit input request.workspace
      (request.radius + 1)
    { records := serialize request.catalog result.states
      passes := result.passes
      reservations := result.reservations
      peakSkeletonCells := result.peakRows
      peakOrdinaryCells := result.ordinaryPeak }
  else ⟨[], 0, 0, 0, 0⟩

inductive Program (n : ℕ) where
  | solve (request : Request n)

def interpret {n : ℕ} (input : List (Edge n)) : Program n → SparseReply n
  | .solve request => (run request input).records

end StreamingReachability.Core.BatchAPI
