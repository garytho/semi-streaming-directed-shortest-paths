module

public import StreamingReachability.Core.Main
public meta import StreamingReachability.Core.Interface
public meta import StreamingReachability.Core.InterfaceCorrect
public meta import StreamingReachability.Core.MeasuredDriver
public meta import StreamingReachability.Core.MeasuredViewed

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace StreamingReachability.Core.DriverRegression

open StoredEdges

def edges : List (Edge 4) := [⟨0, 1, 1⟩, ⟨1, 2, 2⟩, ⟨2, 3, 1⟩]

def request : BatchAPI.Request 4 :=
  BatchAPI.Request.ofCatalog []
    ⟨2, Vector.singleton Finset.univ, Vector.singleton Finset.univ,
      Vector.singleton ⟨0, 0, false, 2⟩⟩ 4

def aborted {n : ℕ} : Except RecordGuard.Abort (BatchAPI.Result n) → Bool
  | .error _ => true
  | .ok _ => false

def remaining : List (Edge 4) := [⟨1, 2, 2⟩, ⟨2, 3, 1⟩]

theorem known_numerator_not_global_round :
    (StoredSearch.run remaining (SparseLabels.vector [(0, 0), (1, 1)])).get 3 = 4 ∧
      (StoredSearch.run remaining (SparseLabels.vector [(0, 0), (1, 2)])).get 3 = 5 := by decide

theorem source_charge_checked_before_allocation :
    RecordGuard.reserve request.catalog 1 ((0 : Fin 1), (0 : Fin 4)) RecordGuard.empty = .error .recordBudget := by
  rfl

def check (name : String) (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError name)

-- Re-rounding the numerator 1 at round 1, or rounding every block-path edge,
-- would incorrectly give distance 3 at the last vertex.
#eval check "true numerators survive global rounds"
  (decide (BatchAPI.lookup (BatchAPI.run request edges).records 0 3 = (2 : Distance)))

#eval check "guard aborts while processing a failed F-skeleton"
  (aborted (BatchAPI.runGuardedMeasured request 7 edges).result &&
    decide ((BatchAPI.runGuardedMeasured request 7 edges).passes = 5))

#eval check "exact weighted allowance succeeds"
  (!aborted (BatchAPI.runGuardedMeasured request 8 edges).result &&
    decide ((BatchAPI.runGuardedMeasured request 8 edges).passes = 8))

def duplicateEdges : List (Edge 4) :=
  [⟨0, 1, 9⟩, ⟨1, 2, 2⟩, ⟨0, 1, 1⟩, ⟨2, 3, 1⟩, ⟨0, 1, 1⟩]

#eval check "parallel targets retain the minimum in the global driver"
  (decide (BatchAPI.lookup (BatchAPI.run request duplicateEdges).records 0 3 = (2 : Distance)))

def raw : List (Option (Edge 4)) :=
  [none, some ⟨0, 1, 1⟩, none, some ⟨1, 2, 2⟩, some ⟨2, 3, 1⟩, none]

#eval check "fused option view counts aborting scans"
  (aborted (BatchAPI.runGuardedMeasuredViewed request 7 id raw).result &&
    decide ((BatchAPI.runGuardedMeasuredViewed request 7 id raw).passes = 5))

def batch : BatchAPI.Request 4 :=
  BatchAPI.Request.ofCatalog []
    ⟨2, Vector.singleton Finset.univ, Vector.singleton Finset.univ,
      Vector.ofFn fun i : Fin 2 => if i = 0 then ⟨0, 0, false, 1⟩ else ⟨0, 3, true, 2⟩⟩ 4

#eval check "shared sets, independent radii, and reverse direction"
  (decide (BatchAPI.lookup (BatchAPI.run batch edges).records 0 3 = ⊤) &&
    decide (BatchAPI.lookup (BatchAPI.run batch edges).records 1 0 = (2 : Distance)))

end StreamingReachability.Core.DriverRegression
