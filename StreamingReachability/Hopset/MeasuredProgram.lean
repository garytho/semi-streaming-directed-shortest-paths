module

public import StreamingReachability.Hopset.BuilderChecked
public import StreamingReachability.Core.AuxiliaryDriver

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ} {A B : Type*}

structure Call (n : ℕ) where
  request : Core.BatchAPI.Request n
  allowance : ℕ
  passes : ℕ

structure Draw where
  bound : ℕ
  value : ℕ
  value_lt : value < bound

/-- The reports are accounting data. Erasure retains only the streamed
algorithm's result, and no report contains the original edge stream. -/
structure Report (n : ℕ) (A : Type*) where
  result : A
  passes : ℕ := 0
  calls : List (Call n) := []
  draws : List Draw := []

def Report.map (f : A → B) (out : Report n A) : Report n B :=
  ⟨f out.result, out.passes, out.calls, out.draws⟩

def Report.then (first : Report n A) (next : Report n B) : Report n B :=
  ⟨next.result, first.passes + next.passes, first.calls ++ next.calls, first.draws ++ next.draws⟩

def Report.draw (bound : ℕ) (value : Fin bound) (out : Report n A) : Report n A :=
  { out with draws := ⟨bound, value.val, value.isLt⟩ :: out.draws }

abbrev Handler (n : ℕ) := Core.BatchAPI.Request n → ℕ → Report n (Option (Core.BatchAPI.SparseReply n))

def eraseHandler (handler : Handler n) : Code.Handler n :=
  fun request budget => Law.pure (handler request budget).result

def auxiliaryHandler {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) : Handler n :=
  fun request budget =>
    let out := Core.BatchAPI.runGuardedMeasuredAuxiliary request budget view input auxiliary
    ⟨match out.result with | .error _ => none | .ok result => some result.records,
      out.passes, [⟨request, budget, out.passes⟩], []⟩

theorem auxiliaryHandler_erases {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) :
    eraseHandler (auxiliaryHandler view input auxiliary) =
      Backend.guardedHandler (input.filterMap view ++ auxiliary) := by
  funext request budget
  simp only [eraseHandler, auxiliaryHandler, Core.BatchAPI.runGuardedMeasuredAuxiliary_eq,
    Core.BatchAPI.runGuardedMeasured_erases, Backend.guardedHandler]
  rfl

noncomputable def code (handler : Handler n) : Code n A → Law (Report n (Option A))
  | .pure value => Law.pure ⟨some value, 0, [], []⟩
  | .abort => Law.pure ⟨none, 0, [], []⟩
  | .uniform bound positive next =>
      (Law.uniform bound positive).bind fun i => (code handler (next i)).map (Report.draw bound i)
  | .batch request budget next =>
      let first := handler request budget
      match first.result with
      | none => Law.pure (first.map (fun _ => none))
      | some reply => (code handler (next reply)).map first.then

theorem code_erases (handler : Handler n) (program : Code n A) (f : Option A → ℝ) :
    (code handler program).expect (fun out => f out.result) =
      (Code.evaluate (eraseHandler handler) program).expect f := by
  induction program with
  | pure value => rfl
  | abort => rfl
  | uniform bound positive next ih =>
      simp only [code, Code.evaluate, Law.expect_bind, Law.expect_map, Report.draw]
      apply congrArg (Law.uniform bound positive).expect
      funext i
      exact ih i
  | batch request budget next ih =>
      simp only [code, Code.evaluate, eraseHandler, Law.expect_bind, Law.expect_pure]
      cases hr : (handler request budget).result with
      | none => rfl
      | some reply =>
          simp only [Law.expect_map, Report.then]
          exact ih reply

noncomputable def builder (handler : Handler n) : Builder n A → Law (Report n A)
  | .pure value => Law.pure ⟨value, 0, [], []⟩
  | .trial cfg hn stored next =>
      (code handler (fixedGuess cfg hn stored)).bind fun first =>
        (builder handler (next first.result)).map first.then

theorem builder_erases (handler : Handler n) (program : Builder n A) (f : A → ℝ) :
    (builder handler program).expect (fun out => f out.result) =
      (Builder.evaluate (eraseHandler handler) program).expect f := by
  induction program with
  | pure value => rfl
  | trial cfg hn stored next ih =>
      simp only [builder, Builder.evaluate, Law.expect_bind, Law.expect_map, Report.then]
      calc
        _ = (code handler (fixedGuess cfg hn stored)).expect
            (fun first => (Builder.evaluate (eraseHandler handler) (next first.result)).expect f) := by
              apply congrArg (code handler (fixedGuess cfg hn stored)).expect
              funext first
              exact ih first.result
        _ = _ := code_erases handler (fixedGuess cfg hn stored)
          (fun result => (Builder.evaluate (eraseHandler handler) (next result)).expect f)

theorem code_expect_bind (handler : Handler n) (program : Code n A) (next : A → Code n B)
    (f : Report n (Option B) → ℝ) :
    (code handler (program.bind next)).expect f =
      (code handler program).expect (fun first =>
        match first.result with
        | none => f (first.map (fun _ => none))
        | some value => (code handler (next value)).expect (fun last => f (first.then last))) := by
  induction program generalizing f with
  | pure value =>
      simp only [Code.bind, code, Law.expect_pure, Report.then, zero_add, List.nil_append]
  | abort => rfl
  | uniform bound positive resume ih =>
      simp only [Code.bind, code, Law.expect_bind, Law.expect_map]
      apply congrArg (Law.uniform bound positive).expect
      funext i
      rw [ih i]
      apply congrArg (code handler (resume i)).expect
      funext first
      rw [show (Report.draw bound i first).result = first.result from rfl]
      cases hr : first.result with
      | none => rfl
      | some value =>
          apply congrArg (code handler (next value)).expect
          funext last
          rfl
  | batch request budget resume ih =>
      simp only [Code.bind, code]
      cases hr : (handler request budget).result with
      | none => rfl
      | some reply =>
          simp only [Law.expect_map]
          rw [ih reply]
          apply congrArg (code handler (resume reply)).expect
          funext first
          rw [show ((handler request budget).then first).result = first.result from rfl]
          cases hf : first.result with
          | none => rfl
          | some value =>
              apply congrArg (code handler (next value)).expect
              funext last
              congr 1
              cases handler request budget
              cases first
              cases last
              simp only [Report.then, Nat.add_assoc, List.append_assoc]

theorem builder_expect_bind (handler : Handler n) (program : Builder n A) (next : A → Builder n B)
    (f : Report n B → ℝ) :
    (builder handler (program.bind next)).expect f =
      (builder handler program).expect (fun first =>
        (builder handler (next first.result)).expect (fun last => f (first.then last))) := by
  induction program generalizing f with
  | pure value =>
      simp only [Builder.bind, builder, Law.expect_pure, Report.then, zero_add, List.nil_append]
  | trial cfg hn stored resume ih =>
      simp only [Builder.bind, builder, Law.expect_bind, Law.expect_map]
      apply congrArg (code handler (fixedGuess cfg hn stored)).expect
      funext first
      rw [ih first.result]
      apply congrArg (builder handler (resume first.result)).expect
      funext middle
      apply congrArg (builder handler (next middle.result)).expect
      funext last
      congr 1
      cases first
      cases middle
      cases last
      simp only [Report.then, Nat.add_assoc, List.append_assoc]

end StreamingReachability.Hopset.Measured
