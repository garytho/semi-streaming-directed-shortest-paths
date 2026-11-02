module

public import StreamingReachability.Streaming.View
public import StreamingReachability.Core.GuardedDriver

@[expose] public section

namespace StreamingReachability.Core

open StoredEdges

variable {E : Type*} {n nb ns nq : ℕ}

namespace Shared

def scanPackView (outerView : E → Option (Edge n)) (c : Catalog n nb ns nq)
    (jobs : List (Job n nb nq)) (stored : List (Edge n)) (input : List E) :
    Streaming.Metered (List (Work n nb nq)) :=
  Streaming.readPassView outerView (update c) cells input
    (stored.foldl (update c) (jobs.map (start c)))

theorem scanPackView_state (outerView : E → Option (Edge n)) (c : Catalog n nb ns nq)
    (jobs : List (Job n nb nq)) (stored : List (Edge n)) (input : List E) :
    (scanPackView outerView c jobs stored input).state =
      (scanPack c jobs stored (input.filterMap outerView)).state :=
  Streaming.readPassView_state _ _ _ _ _

end Shared

namespace BatchDriver

def ordinaryView (outerView : E → Option (Edge n)) (c : Shared.Catalog n nb ns nq)
    (r : ℕ) (old : States n nb nq) (stored : List (Edge n)) (input : List E) :
    Streaming.Metered (Vector (Finset (Fin n)) nq) :=
  Streaming.readPassView outerView (ordinaryStep c r old) ordinaryCells input
    (stored.foldl (ordinaryStep c r old) (Vector.replicate nq ∅))

theorem ordinaryView_state (outerView : E → Option (Edge n)) (c : Shared.Catalog n nb ns nq)
    (r : ℕ) (old : States n nb nq) (stored : List (Edge n)) (input : List E) :
    (ordinaryView outerView c r old stored input).state =
      (ordinary c r old stored (input.filterMap outerView)).state :=
  Streaming.readPassView_state _ _ _ _ _

end BatchDriver

namespace GuardedDriver

def ordinaryView (outerView : E → Option (Edge n)) (c : Shared.Catalog n nb ns nq)
    (budget r : ℕ) (old : BatchDriver.States n nb nq) (stored : List (Edge n)) (input : List E)
    (registry : RecordGuard.Registry n nq) :
    Except RecordGuard.Abort (RecordGuard.Registry n nq × Vector (Finset (Fin n)) nq) :=
  match ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | .error reason => .error reason
  | .ok (next, C) =>
      Streaming.passExceptView outerView
        (fun state raw => ordinaryQueries c budget r old raw (List.finRange nq) state.1 state.2) input (next, C)

theorem ordinaryScan_eq_pass (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (input : List (Edge n))
    (registry : RecordGuard.Registry n nq) (C : Vector (Finset (Fin n)) nq) :
    ordinaryScan c budget r old input registry C =
      Streaming.passExcept (fun state raw =>
        ordinaryQueries c budget r old raw (List.finRange nq) state.1 state.2) input (registry, C) := by
  induction input generalizing registry C with
  | nil => rfl
  | cons raw rest ih =>
      rw [ordinaryScan, Streaming.passExcept]
      cases hs : ordinaryQueries c budget r old raw (List.finRange nq) registry C with
      | error reason => simp only [hs]
      | ok pair =>
          obtain ⟨next, D⟩ := pair
          simpa only [hs] using ih next D

theorem ordinaryView_eq (outerView : E → Option (Edge n)) (c : Shared.Catalog n nb ns nq)
    (budget r : ℕ) (old : BatchDriver.States n nb nq) (stored : List (Edge n)) (input : List E)
    (registry : RecordGuard.Registry n nq) :
    ordinaryView outerView c budget r old stored input registry =
      ordinary c budget r old stored (input.filterMap outerView) registry := by
  unfold ordinaryView ordinary
  cases hs : ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | error reason => simp only [hs]
  | ok pair =>
      obtain ⟨next, C⟩ := pair
      simp only [hs]
      rw [Streaming.passExceptView_eq, ordinaryScan_eq_pass]

end GuardedDriver

end StreamingReachability.Core
