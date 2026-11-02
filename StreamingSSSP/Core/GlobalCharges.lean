module

public import StreamingSSSP.Core.GlobalMain

@[expose] public section

namespace StreamingSSSP.Core.Global

open StoredEdges

variable {n b : ℕ}

theorem external_reservations (A r : ℕ) (B U : Finset (Fin n)) (old : BlockState n) :
    (externalBlock A r B U old).reservations = old.reservations := rfl

theorem search_reservations (hn : 0 < n) (A : ℕ) (B : Finset (Fin n)) (input : List (Edge n))
    (r : ℕ) (old : BlockState n) :
    (searchBlock hn A B input r old).state.reservations =
      old.reservations + (searchBlock hn A B input r old).reservations := by
  unfold searchBlock
  split_ifs
  · rfl
  · simp

theorem round_reservations (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (r : ℕ) (old : State n b) :
    reservationCount (round hn p input r old) =
      reservationCount old +
        ∑ i : Fin b, (searchOne hn p input r i (old.blocks.get i)).reservations := by
  unfold reservationCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [round, Vector.get_ofFn, insertExternal, external_reservations]
  exact search_reservations hn p.scale (p.blocks.get i) input r (old.blocks.get i)

end StreamingSSSP.Core.Global
