module

public import StreamingSSSP.Core.BatchDriver

@[expose] public section

namespace StreamingSSSP.Streaming

theorem readPass_peak_eq {E S : Type*} (step : S → E → S) (cells : S → ℕ)
    (input : List E) (initial : S) (hm : ∀ s e, cells s ≤ cells (step s e)) :
    (readPass step cells input initial).peakCells = cells (readPass step cells input initial).state := by
  have h (xs : List E) (m : Metered S) (he : m.peakCells = cells m.state) :
      (xs.foldl (readEdge step cells) m).peakCells =
        cells (xs.foldl (readEdge step cells) m).state := by
    induction xs generalizing m with
    | nil => exact he
    | cons e es ih =>
        apply ih
        change max m.peakCells (cells (step m.state e)) = cells (step m.state e)
        rw [he, max_eq_right (hm m.state e)]
  exact h input _ rfl

end StreamingSSSP.Streaming

namespace StreamingSSSP.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem edgeStep_subset (p : SparseDriver.Parameters n nb) (r : ℕ) (old : SparseDriver.State n nb)
    (C : Finset (Fin n)) (raw : Edge n) : C ⊆ SparseDriver.edgeStep p r old C raw := by
  unfold SparseDriver.edgeStep
  cases he : p.edgeView raw with
  | none => exact Finset.Subset.refl _
  | some e =>
      dsimp only
      unfold Global.edgeStep
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _

theorem ordinaryCells_mono (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (C : Vector (Finset (Fin n)) nq) (raw : Edge n) :
    ordinaryCells C ≤ ordinaryCells (ordinaryStep c r old C raw) := by
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left 3
  apply Finset.sum_le_sum
  intro j _
  rw [ordinaryStep, Vector.get_ofFn]
  split_ifs
  · exact Finset.card_le_card (edgeStep_subset _ _ _ _ _)
  · exact le_rfl

theorem ordinary_peak_eq (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (stored input : List (Edge n)) :
    (ordinary c r old stored input).peakCells = ordinaryCells (ordinary c r old stored input).state :=
  Streaming.readPass_peak_eq _ _ _ _ (ordinaryCells_mono c r old)

end StreamingSSSP.Core.BatchDriver
