module

public import StreamingSSSP.Streaming.FusedPass
public import StreamingSSSP.Streaming.View

@[expose] public section

namespace StreamingSSSP.Streaming

variable {E F S A : Type*}

/-- Read the original stream once, then the small in-memory auxiliary list.
Neither the mapped original stream nor their concatenation is allocated. -/
def fusedAuxPass (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (auxiliary : List F) (initial : S) : FusedMetered S :=
  auxiliary.foldl (fusedEdge some step cells) (fusedPass view step cells input initial)

theorem fusedAuxPass_erase (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (auxiliary : List F) (initial : S) :
    (fusedAuxPass view step cells input auxiliary initial).erase =
      readPass step cells (input.filterMap view ++ auxiliary) initial := by
  rw [fusedAuxPass, fused_fold_erase, fusedPass_erase, List.filterMap_some]
  exact (List.foldl_append).symm

theorem fusedAuxPass_rawReads (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (auxiliary : List F) (initial : S) :
    (fusedAuxPass view step cells input auxiliary initial).rawReads = input.length + auxiliary.length := by
  have h (xs : List F) (old : FusedMetered S) :
      (xs.foldl (fusedEdge some step cells) old).rawReads = old.rawReads + xs.length := by
    induction xs generalizing old with
    | nil => simp
    | cons edge xs ih =>
        simp only [List.foldl_cons, ih, fusedEdge, Nat.add_assoc, List.length_cons]
        omega
  rw [fusedAuxPass, h, fusedPass_rawReads]

theorem passExcept_append (step : S → F → Except A S) (left right : List F) (initial : S) :
    passExcept step (left ++ right) initial =
      (passExcept step left initial).bind (passExcept step right) := by
  induction left generalizing initial with
  | nil => rfl
  | cons edge left ih =>
      simp only [List.cons_append, passExcept]
      cases hs : step initial edge <;> simp only [hs, Except.bind, ih]

def passExceptAux (view : E → Option F) (step : S → F → Except A S)
    (input : List E) (auxiliary : List F) (initial : S) : Except A S :=
  (passExceptView view step input initial).bind (passExcept step auxiliary)

theorem passExceptAux_eq (view : E → Option F) (step : S → F → Except A S)
    (input : List E) (auxiliary : List F) (initial : S) :
    passExceptAux view step input auxiliary initial = passExcept step (input.filterMap view ++ auxiliary) initial := by
  rw [passExceptAux, passExceptView_eq, passExcept_append]

def foldAux (view : E → Option F) (step : S → F → S)
    (input : List E) (auxiliary : List F) (initial : S) : S :=
  auxiliary.foldl step (input.foldl (liftStep view step) initial)

theorem foldAux_eq (view : E → Option F) (step : S → F → S)
    (input : List E) (auxiliary : List F) (initial : S) :
    foldAux view step input auxiliary initial = (input.filterMap view ++ auxiliary).foldl step initial := by
  rw [foldAux, foldl_view, List.foldl_append]

end StreamingSSSP.Streaming
