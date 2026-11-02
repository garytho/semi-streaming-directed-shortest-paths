module

public import StreamingSSSP.Core.GuardedDriver
public import StreamingSSSP.Core.InterfaceCosts

@[expose] public section

namespace StreamingSSSP.Core.BatchAPI

abbrev Abort := RecordGuard.Abort
abbrev GuardedProgram := GuardedDriver.Program

def runGuarded {n : ℕ} (request : Request n) (remainingRecordBudget : ℕ)
    (input : List (StoredEdges.Edge n)) : Except Abort (Result n) :=
  GuardedDriver.run request remainingRecordBudget input

def interpretGuarded {n : ℕ} (input : List (StoredEdges.Edge n)) :
    GuardedProgram n → Except Abort (SparseReply n) :=
  GuardedDriver.interpret input

end StreamingSSSP.Core.BatchAPI
