module

public import StreamingReachability.Core.GuardedDriver
public import StreamingReachability.Core.InterfaceCosts

@[expose] public section

namespace StreamingReachability.Core.BatchAPI

abbrev Abort := RecordGuard.Abort
abbrev GuardedProgram := GuardedDriver.Program

def runGuarded {n : ℕ} (request : Request n) (remainingRecordBudget : ℕ)
    (input : List (StoredEdges.Edge n)) : Except Abort (Result n) :=
  GuardedDriver.run request remainingRecordBudget input

def interpretGuarded {n : ℕ} (input : List (StoredEdges.Edge n)) :
    GuardedProgram n → Except Abort (SparseReply n) :=
  GuardedDriver.interpret input

end StreamingReachability.Core.BatchAPI
