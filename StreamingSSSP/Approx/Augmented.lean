module

public import StreamingSSSP.Approx.Main
public import StreamingSSSP.Core.AuxiliaryDriver

@[expose] public section

namespace StreamingSSSP.Hopset.Backend

variable {n : ℕ} {E : Type*}

def guardedAuxiliaryHandler (view : E → Option (StoredEdges.Edge n))
    (input : List E) (auxiliary : List (StoredEdges.Edge n)) : Code.Handler n :=
  fun request budget => Law.pure <|
    match (Core.BatchAPI.runGuardedMeasuredAuxiliary request budget view input auxiliary).result with
    | .error _ => none
    | .ok result => some result.records

theorem guardedAuxiliaryHandler_eq (view : E → Option (StoredEdges.Edge n))
    (input : List E) (auxiliary : List (StoredEdges.Edge n)) :
    guardedAuxiliaryHandler view input auxiliary = guardedHandler (input.filterMap view ++ auxiliary) := by
  funext request budget
  simp only [guardedAuxiliaryHandler, Core.BatchAPI.runGuardedMeasuredAuxiliary_eq,
    Core.BatchAPI.runGuardedMeasured_erases, guardedHandler]
  rfl

end StreamingSSSP.Hopset.Backend

namespace StreamingSSSP.Approx

open Hopset

variable {n : ℕ}

def scanAuxiliary {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) : Bounds :=
  Streaming.foldAux view Bounds.push input auxiliary initialBounds

theorem scanAuxiliary_eq {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) :
    scanAuxiliary view input auxiliary = scan (input.filterMap view ++ auxiliary) :=
  Streaming.foldAux_eq _ _ _ _ _

noncomputable def Program.evaluateAuxiliary {E A : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) (auxiliary : List (StoredEdges.Edge n)) : Program n A → Law A
  | .pure value => Law.pure value
  | .metadata next => evaluateAuxiliary view input auxiliary (next (scanAuxiliary view input auxiliary))
  | .construct unit builder next =>
      (Hopset.Builder.evaluate (Backend.guardedAuxiliaryHandler (microViewed unit view) input
        (auxiliary.map (microMap unit))) builder).bind
          (fun stored => evaluateAuxiliary view input auxiliary (next stored))
  | .query unit request allowance next =>
      (Backend.guardedAuxiliaryHandler (microViewed unit view) input (auxiliary.map (microMap unit)) request allowance).bind
        (fun reply => evaluateAuxiliary view input auxiliary (next reply))

theorem microAuxiliary_handler {E : Type*} (unit : ℕ) (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) :
    Backend.guardedAuxiliaryHandler (microViewed unit view) input (auxiliary.map (microMap unit)) =
      Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view ++ auxiliary) := by
  simp only [Backend.guardedAuxiliaryHandler_eq, Backend.guardedViewedHandler_eq, microViewed_filterMap,
    List.filterMap_some, List.filterMap_append, microView_list]

theorem Program.evaluateAuxiliary_eq {E A : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (program : Program n A) :
    evaluateAuxiliary view input auxiliary program = evaluate (input.filterMap view ++ auxiliary) program := by
  induction program with
  | pure value => rfl
  | metadata next ih =>
      have hs : scanViewed some (input.filterMap view ++ auxiliary) = scanAuxiliary view input auxiliary := by
        rw [scanViewed_eq, List.filterMap_some, scanAuxiliary_eq]
      change evaluateAuxiliary view input auxiliary (next (scanAuxiliary view input auxiliary)) =
        evaluateViewed some (input.filterMap view ++ auxiliary) (next (scanViewed some (input.filterMap view ++ auxiliary)))
      rw [hs]
      exact ih _
  | construct unit builder next ih =>
      change (Hopset.Builder.evaluate (Backend.guardedAuxiliaryHandler (microViewed unit view) input
          (auxiliary.map (microMap unit))) builder).bind
            (fun stored => evaluateAuxiliary view input auxiliary (next stored)) =
        (Hopset.Builder.evaluate (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view ++ auxiliary))
          builder).bind (fun stored => evaluateViewed some (input.filterMap view ++ auxiliary) (next stored))
      rw [microAuxiliary_handler]
      apply congrArg (Hopset.Builder.evaluate
        (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view ++ auxiliary)) builder).bind
      funext stored
      exact ih stored
  | query unit request allowance next ih =>
      change (Backend.guardedAuxiliaryHandler (microViewed unit view) input (auxiliary.map (microMap unit)) request allowance).bind
          (fun reply => evaluateAuxiliary view input auxiliary (next reply)) =
        (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view ++ auxiliary) request allowance).bind
          (fun reply => evaluateViewed some (input.filterMap view ++ auxiliary) (next reply))
      rw [microAuxiliary_handler]
      apply congrArg (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view ++ auxiliary) request allowance).bind
      funext reply
      exact ih reply

theorem solve_auxiliary_accurate {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy confidence : ℕ)
    (ha : 0 < accuracy) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Program.evaluateAuxiliary view input auxiliary (solve hn accuracy (Parameters.blockSize n) confidence ha source)).prob
        (Accurate (input.filterMap view ++ auxiliary) source accuracy) := by
  rw [Program.evaluateAuxiliary_eq]
  exact solve_cube_accurate hn accuracy confidence ha source _ hp

end StreamingSSSP.Approx
