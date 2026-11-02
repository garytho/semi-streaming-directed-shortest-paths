module

public import StreamingReachability.Hopset.Backend
public import StreamingReachability.Core.GuardedComplete
public import StreamingReachability.Core.GuardedFusedDriver

@[expose] public section

namespace StreamingReachability.Hopset.Backend

variable {n : ℕ} {A B : Type*}

def Checked (input : List (StoredEdges.Edge n)) : Code n A → (A → Prop) → Prop
  | .pure a, P => P a
  | .abort, _ => True
  | .uniform _ _ next, P => ∀ i, Checked input (next i) P
  | .batch request _ next, P =>
      Checked input (next (Core.BatchAPI.run request input).records) P

theorem checked_true (input : List (StoredEdges.Edge n)) (p : Code n A) :
    Checked input p (fun _ => True) := by
  induction p with
  | pure a => trivial
  | abort => trivial
  | uniform d hd next ih => exact ih
  | batch request budget next ih => exact ih _

theorem checked_mono (input : List (StoredEdges.Edge n)) (p : Code n A)
    (P Q : A → Prop) (hp : Checked input p P) (h : ∀ a, P a → Q a) : Checked input p Q := by
  induction p with
  | pure a => exact h a hp
  | abort => trivial
  | uniform d hd next ih => exact fun i => ih i (hp i)
  | batch request budget next ih => exact ih _ hp

theorem checked_bind (input : List (StoredEdges.Edge n)) (p : Code n A)
    (f : A → Code n B) (P : A → Prop) (Q : B → Prop)
    (hp : Checked input p P) (hf : ∀ a, P a → Checked input (f a) Q) :
    Checked input (p.bind f) Q := by
  induction p with
  | pure a => exact hf a hp
  | abort => trivial
  | uniform d hd next ih => exact fun i => ih i (hp i)
  | batch request budget next ih => exact ih _ hp

theorem checked_raw_probability (input : List (StoredEdges.Edge n)) (p : Code n A)
    (P : A → Prop) (hp : Checked input p P) :
    (Code.evaluate (rawHandler input) p).prob
      (fun result => match result with | none => True | some a => P a) = 1 := by
  induction p with
  | pure a =>
      change P a at hp
      simp [Code.evaluate, Law.prob, hp]
  | abort => simp [Code.evaluate, Law.prob]
  | uniform d hd next ih =>
      rw [Code.evaluate, Law.prob_bind]
      have h : (fun i => (Code.evaluate (rawHandler input) (next i)).prob
          (fun result => match result with | none => True | some a => P a)) =
          fun _ => (1 : ℝ) := funext (fun i => ih i (hp i))
      rw [h, Law.expect_const]
  | batch request budget next ih =>
      simpa only [Code.evaluate, rawHandler, Law.prob_bind, Law.expect_pure] using ih _ hp

theorem checked_guarded_probability (input : List (StoredEdges.Edge n)) (p : Code n A)
    (P : A → Prop) (hp : Checked input p P) :
    (Code.evaluate (guardedHandler input) p).prob
      (fun result => match result with | none => True | some a => P a) = 1 := by
  induction p with
  | pure a =>
      change P a at hp
      simp [Code.evaluate, Law.prob, hp]
  | abort => simp [Code.evaluate, Law.prob]
  | uniform d hd next ih =>
      rw [Code.evaluate, Law.prob_bind]
      have h : (fun i => (Code.evaluate (guardedHandler input) (next i)).prob
          (fun result => match result with | none => True | some a => P a)) =
          fun _ => (1 : ℝ) := funext (fun i => ih i (hp i))
      rw [h, Law.expect_const]
  | batch request budget next ih =>
      simp only [Code.evaluate, guardedHandler, Law.prob_bind, Law.expect_pure]
      cases hr : Core.BatchAPI.runGuarded request budget input with
      | error reason => simp [Law.prob]
      | ok result =>
          have he : result = Core.BatchAPI.run request input :=
            Core.GuardedDriver.run_erases request budget input result hr
          rw [he]
          exact ih _ hp

def guardedViewedHandler {E : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) : Code.Handler n :=
  fun request budget => Law.pure <|
    match Core.BatchAPI.runGuardedViewed request budget view input with
    | .error _ => none
    | .ok result => some result.records

theorem guardedViewedHandler_eq {E : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) :
    guardedViewedHandler view input = guardedHandler (input.filterMap view) := by
  funext request budget
  simp only [guardedViewedHandler, guardedHandler, Core.BatchAPI.runGuardedViewed_eq]
  cases Core.BatchAPI.runGuarded request budget (input.filterMap view) <;> rfl

theorem checked_viewed_probability {E : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) (p : Code n A) (P : A → Prop)
    (hp : Checked (input.filterMap view) p P) :
    (Code.evaluate (guardedViewedHandler view input) p).prob
      (fun result => match result with | none => True | some a => P a) = 1 := by
  rw [guardedViewedHandler_eq]
  exact checked_guarded_probability _ _ _ hp

end StreamingReachability.Hopset.Backend
