module

public import StreamingReachability.StreamingModel

@[expose] public section

namespace StreamingReachability.Streaming

structure FusedMetered (S : Type*) where
  state : S
  interpretedReads : ℕ
  rawReads : ℕ
  peakCells : ℕ

def FusedMetered.erase {S : Type*} (state : FusedMetered S) : Metered S :=
  ⟨state.state, state.interpretedReads, state.peakCells⟩

def fusedEdge {E F S : Type*} (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (old : FusedMetered S) (raw : E) : FusedMetered S :=
  match view raw with
  | none => { old with rawReads := old.rawReads + 1 }
  | some e =>
      let next := step old.state e
      ⟨next, old.interpretedReads + 1, old.rawReads + 1, max old.peakCells (cells next)⟩

def fusedPass {E F S : Type*} (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) : FusedMetered S :=
  input.foldl (fusedEdge view step cells) ⟨initial, 0, 0, cells initial⟩

theorem fused_fold_erase {E F S : Type*} (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : FusedMetered S) :
    (input.foldl (fusedEdge view step cells) initial).erase =
      (input.filterMap view).foldl (readEdge step cells) initial.erase := by
  induction input generalizing initial with
  | nil => rfl
  | cons raw rest ih =>
      rw [List.foldl_cons, ih]
      cases he : view raw <;>
        simp only [List.filterMap_cons, he, List.foldl_cons, fusedEdge, FusedMetered.erase, readEdge]

theorem fusedPass_erase {E F S : Type*} (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) :
    (fusedPass view step cells input initial).erase = readPass step cells (input.filterMap view) initial :=
  fused_fold_erase view step cells input _

theorem fusedPass_rawReads {E F S : Type*} (view : E → Option F) (step : S → F → S) (cells : S → ℕ)
    (input : List E) (initial : S) : (fusedPass view step cells input initial).rawReads = input.length := by
  have h (xs : List E) (m : FusedMetered S) :
      (xs.foldl (fusedEdge view step cells) m).rawReads = m.rawReads + xs.length := by
    induction xs generalizing m with
    | nil => simp
    | cons raw rest ih =>
        rw [List.foldl_cons, ih]
        cases he : view raw <;> simp [fusedEdge, he, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  simpa only [fusedPass, Nat.zero_add] using h input ⟨initial, 0, 0, cells initial⟩

end StreamingReachability.Streaming
