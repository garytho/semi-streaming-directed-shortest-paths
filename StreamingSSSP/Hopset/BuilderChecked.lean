module

public import StreamingSSSP.Hopset.BuilderFacts

@[expose] public section

namespace StreamingSSSP.Hopset

namespace Backend

variable {n : ℕ} {A : Type*}

theorem checked_and (input : List (StoredEdges.Edge n)) (program : Code n A) (P Q : A → Prop)
    (hP : Checked input program P) (hQ : Checked input program Q) :
    Checked input program (fun a => P a ∧ Q a) := by
  induction program with
  | pure a => exact ⟨hP, hQ⟩
  | abort => trivial
  | uniform d hd next ih => exact fun i => ih i (hP i) (hQ i)
  | batch request budget next ih => exact ih _ hP hQ

theorem checked_guarded_holds (input : List (StoredEdges.Edge n)) (program : Code n A)
    (P : A → Prop) (hP : Checked input program P) :
    Early.Sampling.Holds (Code.evaluate (guardedHandler input) program)
      (fun result => match result with | none => True | some a => P a) := by
  induction program with
  | pure a => exact Early.Sampling.holds_pure (some a) _ hP
  | abort => exact Early.Sampling.holds_pure none _ trivial
  | uniform d hd next ih =>
      apply Early.Sampling.holds_bind
      intro i
      exact ih i (hP i)
  | batch request budget next ih =>
      cases hr : Core.BatchAPI.runGuarded request budget input with
      | error reason =>
          simp only [Code.evaluate, guardedHandler, hr]
          refine Reference.holds_bind_on _ _ (fun result => result = none) _
            (Early.Sampling.holds_pure none _ rfl) ?_
          intro result he
          subst result
          exact Early.Sampling.holds_pure none _ trivial
      | ok result =>
          have he : result = Core.BatchAPI.run request input :=
            Core.GuardedDriver.run_erases request budget input result hr
          simp only [Code.evaluate, guardedHandler, hr]
          refine Reference.holds_bind_on _ _ (fun reply => reply = some result.records) _
            (Early.Sampling.holds_pure _ _ rfl) ?_
          intro reply hreply
          subst reply
          rw [he]
          exact ih _ hP

end Backend

namespace Code

variable {n : ℕ} {A : Type*}

theorem ensures_checked (input : List (StoredEdges.Edge n)) (program : Code n A) (P : A → Prop)
    (h : program.Ensures P) : Backend.Checked input program P := by
  induction program with
  | pure a => exact h
  | abort => trivial
  | uniform d hd next ih => exact fun i => ih i (h i)
  | batch request budget next ih => exact ih _ (h _)

end Code

namespace Builder

variable {n : ℕ} {A B : Type*}

def Checked (input : List (StoredEdges.Edge n)) : Builder n A → (A → Prop) → Prop
  | .pure a, P => P a
  | .trial cfg hn stored next, P =>
      Checked input (next none) P ∧
        Backend.Checked input (fixedGuess cfg hn stored) (fun out => Checked input (next (some out)) P)

theorem checked_mono (input : List (StoredEdges.Edge n)) (program : Builder n A) (P Q : A → Prop)
    (hP : Checked input program P) (h : ∀ a, P a → Q a) : Checked input program Q := by
  induction program with
  | pure a => exact h a hP
  | trial cfg hn stored next ih =>
      exact ⟨ih none hP.1, Backend.checked_mono _ _ _ _ hP.2 (fun out ho => ih (some out) ho)⟩

theorem checked_bind (input : List (StoredEdges.Edge n)) (program : Builder n A)
    (next : A → Builder n B) (P : A → Prop) (Q : B → Prop)
    (hP : Checked input program P) (hnext : ∀ a, P a → Checked input (next a) Q) :
    Checked input (program.bind next) Q := by
  induction program with
  | pure a => exact hnext a hP
  | trial cfg hn stored resume ih =>
      exact ⟨ih none hP.1, Backend.checked_mono _ _ _ _ hP.2 (fun out ho => ih (some out) ho)⟩

theorem checked_evaluate (input : List (StoredEdges.Edge n)) (program : Builder n A) (P : A → Prop)
    (h : Checked input program P) : Early.Sampling.Holds (evaluate (Backend.guardedHandler input) program) P := by
  induction program with
  | pure a => exact Early.Sampling.holds_pure a P h
  | trial cfg hn stored next ih =>
      refine Reference.holds_bind_on _ _ (fun result => Checked input (next result) P) P ?_ ?_
      · refine Early.Sampling.holds_mono (Backend.checked_guarded_holds input (fixedGuess cfg hn stored)
          (fun out => Checked input (next (some out)) P) h.2) ?_
        intro result hr
        cases result with
        | none => exact h.1
        | some out => exact hr
      · intro result hr
        exact ih result hr

end Builder

end StreamingSSSP.Hopset
