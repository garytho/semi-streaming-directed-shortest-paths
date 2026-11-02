module

public import StreamingSSSP.Core.Skeleton
public import StreamingSSSP.StreamingModel

@[expose] public section

namespace StreamingSSSP.Core.Skeleton

open StoredEdges

variable {n : ℕ}

def stateCells (rows : List (Row n)) : ℕ :=
  (rows.map fun row => 4 + 2 * row.kept.card).sum

def StateBound (b τ : ℕ) (rows : List (Row n)) : Prop :=
  rows.length = b ∧ ∀ row ∈ rows, row.kept.card ≤ τ

theorem stateCells_le (b τ : ℕ) (rows : List (Row n)) (h : StateBound b τ rows) :
    stateCells rows ≤ 4 * b + 2 * (b * τ) := by
  obtain ⟨hlen, hrows⟩ := h
  have hb (rs : List (Row n)) (hrs : ∀ row ∈ rs, row.kept.card ≤ τ) :
      stateCells rs ≤ 4 * rs.length + 2 * (rs.length * τ) := by
    induction rs with
    | nil => simp [stateCells]
    | cons row rs ih =>
        have hr := hrs row (by simp)
        have ht := ih (fun q hq => hrs q (by simp [hq]))
        simp only [stateCells, List.map_cons, List.sum_cons, List.length_cons] at *
        nlinarith
  simpa only [hlen] using hb rows hrows

theorem update_stateBound (B known : Finset (Fin n)) (b τ : ℕ)
    (e : Edge n) (rows : List (Row n)) (h : StateBound b τ rows) :
    StateBound b τ (rows.map (updateRow B known τ e)) := by
  refine ⟨by simpa using h.1, ?_⟩
  intro row hrow
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
  dsimp only [updateRow]
  split_ifs
  · exact TopRows.offer_card n τ _ _ (h.2 old hold)
  · exact h.2 old hold

def streamed (B known : Finset (Fin n)) (τ : ℕ) (input : List (Edge n)) :
    Streaming.Metered (List (Row n)) :=
  Streaming.readPass (fun rows e => rows.map (updateRow B known τ e)) stateCells input
    ((B.sort (· ≤ ·)).map fun a => ⟨a, ∅⟩)

theorem scanRows_fold (B known : Finset (Fin n)) (τ : ℕ)
    (input : List (Edge n)) (rows : List (Row n)) :
    scanRows B known τ input rows =
      input.foldl (fun rows e => rows.map (updateRow B known τ e)) rows := by
  induction input generalizing rows with
  | nil => rfl
  | cons e es ih => exact ih _

theorem streamed_state (B known : Finset (Fin n)) (τ : ℕ) (input : List (Edge n)) :
    (streamed B known τ input).state = rows B known τ input := by
  rw [streamed, Streaming.readPass_state, rows, scanRows_fold]

theorem streamed_reads (B known : Finset (Fin n)) (τ : ℕ) (input : List (Edge n)) :
    (streamed B known τ input).reads = input.length :=
  Streaming.readPass_reads _ _ _ _

theorem streamed_memory (B known : Finset (Fin n)) (τ : ℕ) (input : List (Edge n)) :
    (streamed B known τ input).peakCells ≤ 4 * B.card + 2 * (B.card * τ) := by
  have hi : StateBound B.card τ
      ((B.sort (· ≤ ·)).map fun a => (⟨a, ∅⟩ : Row n)) := by
    refine ⟨by simp, ?_⟩
    intro row hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
    exact Nat.zero_le τ
  exact (Streaming.readPass_bound _ _ input _ (StateBound B.card τ)
    (4 * B.card + 2 * (B.card * τ)) hi
    (fun rs e h => update_stateBound B known B.card τ e rs h)
    (fun rs h => stateCells_le B.card τ rs h)).2

theorem workspace_reservation (hn : 0 < n) (B known : Finset (Fin n)) (τ x : ℕ)
    (input : List (Edge n)) (hx : B.card ≤ x) (hτ : τ ≤ 2 * x) (hspace : 2 * x * x ≤ n) :
    (build hn B known τ input).length ≤ n ∧
      (streamed B known τ input).peakCells ≤ 4 * x + 2 * n := by
  have hcap : B.card * τ ≤ n := by
    have h := Nat.mul_le_mul hx hτ
    nlinarith only [h, hspace]
  exact ⟨(length_le hn B known τ input).trans hcap,
    (streamed_memory B known τ input).trans (by omega)⟩

end StreamingSSSP.Core.Skeleton
