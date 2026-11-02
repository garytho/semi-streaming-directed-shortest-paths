module

public import StreamingSSSP.Core.SkeletonMemory
public import StreamingSSSP.Core.Doubling
public import StreamingSSSP.Core.OrdinaryScan

@[expose] public section

namespace StreamingSSSP.Core.ViewedSkeleton

open StoredEdges

variable {n : ℕ}

def update (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (raw : Edge n) (row : Skeleton.Row n) : Skeleton.Row n :=
  match view raw with
  | none => row
  | some e => Skeleton.updateRow B known τ e row

theorem update_none (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    {raw : Edge n} (h : view raw = none) : update view B known τ raw = id := by
  funext row
  simp [update, h]

theorem update_some (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    {raw e : Edge n} (h : view raw = some e) :
    update view B known τ raw = Skeleton.updateRow B known τ e := by
  funext row
  simp [update, h]

def scanRows (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ) :
    List (Edge n) → List (Skeleton.Row n) → List (Skeleton.Row n)
  | [], rows => rows
  | e :: es, rows => scanRows view B known τ es (rows.map (update view B known τ e))

theorem scanRows_eq (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (input : List (Edge n)) (rows : List (Skeleton.Row n)) :
    scanRows view B known τ input rows =
      Skeleton.scanRows B known τ (input.filterMap view) rows := by
  induction input generalizing rows with
  | nil => rfl
  | cons e es ih =>
      cases he : view e with
      | none =>
          simp only [scanRows, List.filterMap_cons, he, update_none view B known τ he, List.map_id]
          exact ih rows
      | some f =>
          simp only [scanRows, List.filterMap_cons, he, update_some view B known τ he, Skeleton.scanRows]
          exact ih _

def rows (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (stored input : List (Edge n)) : List (Skeleton.Row n) :=
  scanRows view B known τ input
    (scanRows view B known τ stored ((B.sort (· ≤ ·)).map fun a => ⟨a, ∅⟩))

theorem scanRows_append (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (xs ys : List (Edge n)) (initial : List (Skeleton.Row n)) :
    scanRows view B known τ (xs ++ ys) initial =
      scanRows view B known τ ys (scanRows view B known τ xs initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons e es ih => exact ih _

theorem rows_eq (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (stored input : List (Edge n)) :
    rows view B known τ stored input = Skeleton.rows B known τ ((stored ++ input).filterMap view) := by
  rw [rows, ← scanRows_append, scanRows_eq]
  rfl

def build (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (τ : ℕ) (stored input : List (Edge n)) : List (Edge n) :=
  (rows view B known τ stored input).flatMap (Skeleton.rowEdges hn)

theorem build_eq (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (τ : ℕ) (stored input : List (Edge n)) :
    build hn view B known τ stored input =
      Skeleton.build hn B known τ ((stored ++ input).filterMap view) := by
  rw [build, rows_eq]
  rfl

def labels (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (τ : ℕ) (initial : DistanceArray n) (stored input : List (Edge n)) : DistanceArray n :=
  StoredSearch.run (build hn view B known τ stored input) initial

theorem labels_eq (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (τ : ℕ) (initial : DistanceArray n) (stored input : List (Edge n)) :
    labels hn view B known τ initial stored input =
      BlockSearch.labels hn B known τ initial ((stored ++ input).filterMap view) := by
  rw [labels, build_eq]
  rfl

def searchAux (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (r : ℕ) (initial : DistanceArray n) (stored input : List (Edge n)) :
    ℕ → ℕ → Option (BlockSearch.Outcome n)
  | 0, _ => none
  | fuel + 1, τ =>
      let f := labels hn view B known τ initial stored input
      if (found B known f.get r).card < τ then some (BlockSearch.finish B known r τ f)
      else (searchAux hn view B known r initial stored input fuel (2 * τ)).map fun out =>
        { out with scans := out.scans + 1
                   reservations := out.reservations + B.card * τ }

theorem searchAux_eq (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (r : ℕ) (initial : DistanceArray n) (stored input : List (Edge n)) (fuel τ : ℕ) :
    searchAux hn view B known r initial stored input fuel τ =
      BlockSearch.searchAux hn B known r initial ((stored ++ input).filterMap view) fuel τ := by
  induction fuel generalizing τ with
  | zero => rfl
  | succ fuel ih =>
      simp only [searchAux, BlockSearch.searchAux, labels_eq, ih]

def search (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (r : ℕ) (initial : DistanceArray n) (stored input : List (Edge n)) :
    Option (BlockSearch.Outcome n) :=
  searchAux hn view B known r initial stored input (Nat.log 2 B.card + 2) 1

theorem search_eq (hn : 0 < n) (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (r : ℕ) (initial : DistanceArray n) (stored input : List (Edge n)) :
    search hn view B known r initial stored input =
      BlockSearch.search hn B known r initial ((stored ++ input).filterMap view) :=
  searchAux_eq hn view B known r initial stored input _ _

theorem update_bound (view : Edge n → Option (Edge n)) (B known : Finset (Fin n))
    (b τ : ℕ) (e : Edge n) (rows : List (Skeleton.Row n)) (h : Skeleton.StateBound b τ rows) :
    Skeleton.StateBound b τ (rows.map (update view B known τ e)) := by
  cases he : view e with
  | none => simpa only [update_none view B known τ he, List.map_id] using h
  | some f =>
      simpa only [update_some view B known τ he] using Skeleton.update_stateBound B known b τ f rows h

def streamed (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (stored input : List (Edge n)) : Streaming.Metered (List (Skeleton.Row n)) :=
  Streaming.readPass (fun rows raw => rows.map (update view B known τ raw)) Skeleton.stateCells input
    (scanRows view B known τ stored ((B.sort (· ≤ ·)).map fun a => ⟨a, ∅⟩))

theorem scanRows_bound (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (b τ : ℕ)
    (input : List (Edge n)) (rows : List (Skeleton.Row n)) (h : Skeleton.StateBound b τ rows) :
    Skeleton.StateBound b τ (scanRows view B known τ input rows) := by
  induction input generalizing rows with
  | nil => exact h
  | cons e es ih => exact ih _ (update_bound view B known b τ e rows h)

theorem streamed_memory (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (stored input : List (Edge n)) :
    (streamed view B known τ stored input).peakCells ≤ 4 * B.card + 2 * (B.card * τ) := by
  have hi : Skeleton.StateBound B.card τ
      ((B.sort (· ≤ ·)).map fun a => (⟨a, ∅⟩ : Skeleton.Row n)) := by
    constructor
    · simp
    · intro row hr
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
      exact Nat.zero_le τ
  exact (Streaming.readPass_bound _ _ input _ (Skeleton.StateBound B.card τ)
    (4 * B.card + 2 * (B.card * τ))
    (scanRows_bound view B known B.card τ stored _ hi)
    (fun rs e h => update_bound view B known B.card τ e rs h)
    (fun rs h => Skeleton.stateCells_le B.card τ rs h)).2

theorem streamed_reads (view : Edge n → Option (Edge n)) (B known : Finset (Fin n)) (τ : ℕ)
    (stored input : List (Edge n)) :
    (streamed view B known τ stored input).reads = input.length :=
  Streaming.readPass_reads _ _ _ _

end StreamingSSSP.Core.ViewedSkeleton
