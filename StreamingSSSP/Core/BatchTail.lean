module

public import StreamingSSSP.Core.BatchDriver

@[expose] public section

namespace StreamingSSSP.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

def driveAux (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) (x : ℕ) :
    ℕ → ℕ → Run n nb nq → Run n nb nq
  | 0, _, state => state
  | fuel + 1, r, state =>
      let next := round hn c stored input x r state.states
      driveAux hn c stored input x fuel (r + 1)
        ⟨next.states, state.passes + next.passes, state.reservations + next.reservations,
          max state.peakRows next.peakRows, max state.ordinaryPeak next.ordinaryPeak⟩

def executeTail (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (x rounds : ℕ) : Run n nb nq :=
  driveAux hn c stored input x rounds 0 ⟨initial c, 0, 0, 0, 0⟩

theorem driveAux_execute (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x fuel r : ℕ) :
    driveAux hn c stored input x fuel r (execute hn c stored input x r) =
      execute hn c stored input x (r + fuel) := by
  induction fuel generalizing r with
  | zero => simp [driveAux]
  | succ fuel ih =>
      rw [driveAux]
      change driveAux hn c stored input x fuel (r + 1) (execute hn c stored input x (r + 1)) = _
      rw [ih]
      congr 1
      omega

theorem executeTail_eq (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x rounds : ℕ) :
    executeTail hn c stored input x rounds = execute hn c stored input x rounds := by
  simpa only [executeTail, execute, Nat.zero_add] using
    driveAux_execute hn c stored input x rounds 0

end StreamingSSSP.Core.BatchDriver
