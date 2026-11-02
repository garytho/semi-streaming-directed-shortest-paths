module

public import StreamingReachability.StreamingModel

@[expose] public section

namespace StreamingReachability.Streaming

variable {E F S A : Type*}

def liftStep (view : E → Option F) (step : S → F → S) (state : S) (raw : E) : S :=
  match view raw with | none => state | some e => step state e

theorem foldl_view (view : E → Option F) (step : S → F → S) (input : List E) (initial : S) :
    input.foldl (liftStep view step) initial = (input.filterMap view).foldl step initial := by
  induction input generalizing initial with
  | nil => rfl
  | cons raw rest ih =>
      cases he : view raw <;> simpa only [List.foldl_cons, List.filterMap_cons, he, liftStep] using ih _

def readPassView (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) : Metered S :=
  readPass (liftStep view step) cells input initial

theorem readPassView_state (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) :
    (readPassView view step cells input initial).state =
      (readPass step cells (input.filterMap view) initial).state := by
  rw [readPassView, readPass_state, readPass_state, foldl_view]

theorem readPassView_reads (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) :
    (readPassView view step cells input initial).reads = input.length :=
  readPass_reads _ _ _ _

theorem fold_frame_eq (step : S → F → S) (cells : S → ℕ) (input : List F)
    (left right : Metered S) (hs : left.state = right.state) (hp : left.peakCells = right.peakCells) :
    ((input.foldl (readEdge step cells) left).state,
        (input.foldl (readEdge step cells) left).peakCells) =
      ((input.foldl (readEdge step cells) right).state,
        (input.foldl (readEdge step cells) right).peakCells) := by
  induction input generalizing left right with
  | nil => exact Prod.ext hs hp
  | cons e es ih =>
      apply ih
      · simp only [readEdge, hs]
      · simp only [readEdge, hs, hp]

theorem fold_view_frame (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : Metered S) (hi : cells initial.state ≤ initial.peakCells) :
    ((input.foldl (readEdge (liftStep view step) cells) initial).state,
        (input.foldl (readEdge (liftStep view step) cells) initial).peakCells) =
      (((input.filterMap view).foldl (readEdge step cells) initial).state,
        ((input.filterMap view).foldl (readEdge step cells) initial).peakCells) := by
  induction input generalizing initial with
  | nil => rfl
  | cons raw rest ih =>
      cases he : view raw with
      | none =>
          simp only [List.foldl_cons, List.filterMap_cons, he]
          apply (fold_frame_eq (liftStep view step) cells rest
            (readEdge (liftStep view step) cells initial raw) initial
            (by simp [readEdge, liftStep, he]) (by simp [readEdge, liftStep, he, max_eq_left hi])).trans
          exact ih initial hi
      | some e =>
          simp only [List.foldl_cons, List.filterMap_cons, he]
          have hm : readEdge (liftStep view step) cells initial raw = readEdge step cells initial e := by
            simp [readEdge, liftStep, he]
          rw [hm]
          exact ih _ (le_max_right _ _)

theorem readPassView_peak (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) :
    (readPassView view step cells input initial).peakCells =
      (readPass step cells (input.filterMap view) initial).peakCells :=
  congrArg Prod.snd (fold_view_frame view step cells input ⟨initial, 0, cells initial⟩ le_rfl)

def passExcept (step : S → F → Except A S) : List F → S → Except A S
  | [], state => .ok state
  | e :: rest, state =>
      match step state e with
      | .error reason => .error reason
      | .ok next => passExcept step rest next

def passExceptView (view : E → Option F) (step : S → F → Except A S) : List E → S → Except A S
  | [], state => .ok state
  | raw :: rest, state =>
      match view raw with
      | none => passExceptView view step rest state
      | some e =>
          match step state e with
          | .error reason => .error reason
          | .ok next => passExceptView view step rest next

theorem passExceptView_eq (view : E → Option F) (step : S → F → Except A S)
    (input : List E) (initial : S) :
    passExceptView view step input initial = passExcept step (input.filterMap view) initial := by
  induction input generalizing initial with
  | nil => rfl
  | cons raw rest ih =>
      cases he : view raw with
      | none => simpa only [passExceptView, List.filterMap_cons, he] using ih initial
      | some e =>
          simp only [passExceptView, List.filterMap_cons, he, passExcept]
          cases hs : step initial e <;> simp only [hs, ih]

end StreamingReachability.Streaming
