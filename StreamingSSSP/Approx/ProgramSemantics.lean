module

public import StreamingSSSP.Approx.Program

@[expose] public section

namespace StreamingSSSP.Approx

open Hopset

variable {n : ℕ}

theorem microViewed_handler {E : Type*} (unit : ℕ) (view : E → Option (StoredEdges.Edge n)) (input : List E) :
    Backend.guardedViewedHandler (microViewed unit view) input =
      Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view) := by
  simp only [Backend.guardedViewedHandler_eq, microViewed_filterMap, List.filterMap_some]

theorem Program.evaluateViewed_eq {E A : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (program : Program n A) :
    evaluateViewed view input program = evaluate (input.filterMap view) program := by
  induction program with
  | pure value => rfl
  | metadata next ih =>
      have hs : scanViewed some (input.filterMap view) = scanViewed view input := by
        rw [scanViewed_eq, scanViewed_eq, List.filterMap_some]
      change evaluateViewed view input (next (scanViewed view input)) =
        evaluateViewed some (input.filterMap view) (next (scanViewed some (input.filterMap view)))
      rw [hs]
      exact ih _
  | construct unit builder next ih =>
      change (Hopset.Builder.evaluate (Backend.guardedViewedHandler (microViewed unit view) input) builder).bind
          (fun stored => evaluateViewed view input (next stored)) =
        (Hopset.Builder.evaluate (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view)) builder).bind
          (fun stored => evaluateViewed some (input.filterMap view) (next stored))
      rw [microViewed_handler]
      apply congrArg (Hopset.Builder.evaluate
        (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view)) builder).bind
      funext stored
      exact ih stored
  | query unit request allowance next ih =>
      change (Backend.guardedViewedHandler (microViewed unit view) input request allowance).bind
          (fun reply => evaluateViewed view input (next reply)) =
        (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view) request allowance).bind
          (fun reply => evaluateViewed some (input.filterMap view) (next reply))
      rw [microViewed_handler]
      apply congrArg (Backend.guardedViewedHandler (microViewed unit some) (input.filterMap view) request allowance).bind
      funext reply
      exact ih reply

end StreamingSSSP.Approx
