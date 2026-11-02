module

public import StreamingReachability.Exact.StreamingCorrectness
public import StreamingReachability.Exact.RawQueryBounds
public import StreamingReachability.Approx.MetadataWordBounds

@[expose] public section

namespace StreamingReachability.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram

variable {n : ℕ} {A B : Type*}

inductive Call (n : ℕ) where
  | base (call : Hopset.Measured.Call n)
  | level (call : Hopset.Measured.Call (n + 1))

structure Work (n : ℕ) (A : Type*) where
  result : A
  passes : ℕ := 0
  calls : List (Call n) := []
  draws : List Hopset.Measured.Draw := []

def Work.map (f : A → B) (out : Work n A) : Work n B :=
  ⟨f out.result, out.passes, out.calls, out.draws⟩

def Work.then (first : Work n A) (last : Work n B) : Work n B :=
  ⟨last.result, first.passes + last.passes, first.calls ++ last.calls, first.draws ++ last.draws⟩

def fromBase (out : Hopset.Measured.Report n A) : Work n A :=
  ⟨out.result, out.passes, out.calls.map Call.base, out.draws⟩

def fromLevel (out : Hopset.Measured.Report (n + 1) A) : Work n A :=
  ⟨out.result, out.passes, out.calls.map Call.level, out.draws⟩

noncomputable def handler (originalSource : Fin n) (exponent confidence : ℕ)
    (input : List (StoredEdges.Edge n)) : (request : Request n) → Law (Work n request.Reply)
  | .base descriptor source denominator _ =>
      (Approx.Measured.evaluate (baseView descriptor) input
        (baseAuxiliary descriptor originalSource (n ^ exponent))
        (Approx.solve (sourcePositive source) (safeAccuracy denominator) (Parameters.blockSize n) confidence
          (safeAccuracy_pos denominator) source)).map (fun out => (fromBase out).map integerLabels)
  | .level descriptor denominator _ =>
      (Approx.Measured.evaluate (levelView descriptor) input
        (levelAuxiliary descriptor originalSource (n ^ exponent))
        (Approx.solve (Nat.succ_pos n) (safeAccuracy denominator) (Parameters.blockSize (n + 1)) confidence
          (safeAccuracy_pos denominator) (Fin.last n))).map (fun out => (fromLevel out).map integerLevelAnswer)
  | .parents source weightBound distances =>
      Law.pure ⟨Vector.ofFn (ParentPass.run source weightBound distances.get input), 1, [], []⟩

theorem handler_erases (originalSource : Fin n) (exponent confidence : ℕ)
    (input : List (StoredEdges.Edge n)) (request : Request n) (f : request.Reply → ℝ) :
    (handler originalSource exponent confidence input request).expect (fun out => f out.result) =
      (requestHandler originalSource exponent confidence input request).expect f := by
  cases request with
  | base descriptor source denominator clock =>
      change Labels n → ℝ at f
      simp only [handler, requestHandler, Law.expect_map, fromBase, Work.map]
      exact (Approx.Measured.evaluate_erases _ _ _ _ (fun out => f (integerLabels out))).trans
        (Law.expect_map _ integerLabels f).symm
  | level descriptor denominator clock =>
      change LevelAnswer n → ℝ at f
      simp only [handler, requestHandler, Law.expect_map, fromLevel, Work.map]
      exact (Approx.Measured.evaluate_erases _ _ _ _ (fun out => f (integerLevelAnswer out))).trans
        (Law.expect_map _ integerLevelAnswer f).symm
  | parents => rfl

noncomputable def execute (handler : (request : Request n) → Law (Work n request.Reply)) :
    Program n A → Cache n → Law (Work n (Outcome n A))
  | .pure value, cache => Law.pure ⟨⟨value, cache, []⟩, 0, [], []⟩
  | .ask request next, cache =>
      match cache.response request with
      | some answer =>
          (execute handler (next answer) cache).map
            (fun out => out.map (Outcome.prepend ⟨request, answer, false⟩))
      | none =>
          (handler request).bind fun first =>
            (execute handler (next first.result) (cache.store request first.result)).map
              (fun last => first.then (last.map (Outcome.prepend ⟨request, first.result, true⟩)))

theorem execute_erases (handler : (request : Request n) → Law (Work n request.Reply))
    (plain : (request : Request n) → Law request.Reply)
    (hh : ∀ request f, (handler request).expect (fun out => f out.result) = (plain request).expect f)
    (program : Program n A) (cache : Cache n) (f : Outcome n A → ℝ) :
    (execute handler program cache).expect (fun out => f out.result) =
      (Implementation.execute plain program cache).expect f := by
  induction program generalizing cache f with
  | pure value => rfl
  | ask request next ih =>
      cases hr : cache.response request with
      | some answer =>
          simp only [execute, Implementation.execute, hr, Law.expect_map, Work.map]
          exact ih answer cache (fun out => f (Outcome.prepend ⟨request, answer, false⟩ out))
      | none =>
          simp only [execute, Implementation.execute, hr, Law.expect_bind, Law.expect_map, Work.then, Work.map]
          calc
            _ = (handler request).expect (fun first =>
                (Implementation.execute plain (next first.result) (cache.store request first.result)).expect
                  (fun out => f (Outcome.prepend ⟨request, first.result, true⟩ out))) := by
                    apply congrArg (handler request).expect
                    funext first
                    exact ih first.result (cache.store request first.result)
                      (fun out => f (Outcome.prepend ⟨request, first.result, true⟩ out))
            _ = _ := hh request (fun answer =>
              (Implementation.execute plain (next answer) (cache.store request answer)).expect
                (fun out => f (Outcome.prepend ⟨request, answer, true⟩ out)))

theorem handler_parents (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (request : Request n) :
    Early.Sampling.Holds (handler source exponent confidence input request)
      (fun out => ParentCorrect (parentReplyOfEdges input) request out.result) := by
  cases request with
  | base => intro _ _; trivial
  | level => intro _ _; trivial
  | parents => exact Early.Sampling.holds_pure _ _ rfl

theorem execute_run (handler : (request : Request n) → Law (Work n request.Reply)) (parent : ParentReply n)
    (hp : ∀ request, Early.Sampling.Holds (handler request) (fun out => ParentCorrect parent request out.result))
    (program : Program n A) (cache : Cache n) :
    Early.Sampling.Holds (execute handler program cache)
      (fun out => Run parent program cache out.result.result out.result.cache out.result.trace) := by
  induction program generalizing cache with
  | pure value => exact Early.Sampling.holds_pure _ _ (.pure value cache)
  | ask request next ih =>
      cases hr : cache.response request with
      | some answer =>
          simp only [execute, hr]
          refine Early.Sampling.holds_map (ih answer cache)
            (fun out => out.map (Outcome.prepend ⟨request, answer, false⟩)) _ ?_
          intro out ho
          exact .hit hr ho
      | none =>
          simp only [execute, hr]
          refine Hopset.Reference.holds_bind_on _ _ _ _ (hp request) ?_
          intro first hf
          refine Early.Sampling.holds_map (ih first.result (cache.store request first.result))
            (fun last => first.then (last.map (Outcome.prepend ⟨request, first.result, true⟩))) _ ?_
          intro last hl
          exact .fresh hr hf hl

noncomputable def evaluate (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n)) :
    Law (Work n (Outcome n (Result n))) :=
  execute (handler source exponent (oracleConfidence exponent confidence) input)
    (DescriptorProgram.exact source exponent) {}

theorem evaluate_erases (source : Fin n) (exponent confidence : ℕ)
    (input : List (StoredEdges.Edge n)) (f : Result n → ℝ) :
    (evaluate source exponent confidence input).expect (fun out => f out.result.result) =
      (Implementation.evaluate source exponent confidence input).expect f := by
  have h := execute_erases (handler source exponent (oracleConfidence exponent confidence) input)
    (requestHandler source exponent (oracleConfidence exponent confidence) input)
    (handler_erases source exponent (oracleConfidence exponent confidence) input)
    (DescriptorProgram.exact source exponent) {} (fun out => f out.result)
  simpa only [evaluate, Implementation.evaluate, Law.expect_map] using h

theorem evaluate_correct (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (evaluate source exponent confidence input).prob (fun out => CorrectResult input source out.result.result) := by
  change 1 - 1 / (n : ℝ) ^ confidence ≤ (evaluate source exponent confidence input).expect
    (fun out => if CorrectResult input source out.result.result then 1 else 0)
  rw [evaluate_erases source exponent confidence input (fun result => if CorrectResult input source result then 1 else 0)]
  exact exact_streaming_correct source exponent confidence input hw

end StreamingReachability.Exact.Implementation.Measured
