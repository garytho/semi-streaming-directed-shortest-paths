module

public import StreamingReachability.Approx.Queries

@[expose] public section

namespace StreamingReachability.Approx

open Hopset

variable {n : ℕ}

abbrev Labels (n : ℕ) := Vector Distance n

inductive Program (n : ℕ) (A : Type*) where
  | pure (value : A)
  | metadata (next : Bounds → Program n A)
  | construct (unit : ℕ) (builder : Hopset.Builder n (Implicit.Representation n))
      (next : Implicit.Representation n → Program n A)
  | query (unit : ℕ) (request : Core.BatchAPI.Request n) (allowance : ℕ)
      (next : Option (Core.BatchAPI.SparseReply n) → Program n A)

def Program.bind {A B : Type*} : Program n A → (A → Program n B) → Program n B
  | .pure value, next => next value
  | .metadata resume, next => .metadata (fun bounds => bind (resume bounds) next)
  | .construct unit builder resume, next => .construct unit builder (fun stored => bind (resume stored) next)
  | .query unit request allowance resume, next => .query unit request allowance (fun reply => bind (resume reply) next)

def microViewed {E : Type*} (unit : ℕ) (view : E → Option (StoredEdges.Edge n))
    (raw : E) : Option (StoredEdges.Edge n) :=
  (view raw).map (microMap unit)

theorem microViewed_filterMap {E : Type*} (unit : ℕ) (view : E → Option (StoredEdges.Edge n)) (input : List E) :
    input.filterMap (microViewed unit view) = (input.filterMap view).filterMap (microView unit) := by
  induction input with
  | nil => rfl
  | cons raw input ih =>
      cases hv : view raw <;> simp only [List.filterMap_cons, microViewed, hv, Option.map_none,
        Option.map_some, microView, ih]

noncomputable def Program.evaluateViewed {E A : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E) :
    Program n A → Law A
  | .pure value => Law.pure value
  | .metadata next => evaluateViewed view input (next (scanViewed view input))
  | .construct unit builder next =>
      (Hopset.Builder.evaluate (Backend.guardedViewedHandler (microViewed unit view) input) builder).bind
        (fun stored => evaluateViewed view input (next stored))
  | .query unit request allowance next =>
      (Backend.guardedViewedHandler (microViewed unit view) input request allowance).bind
        (fun reply => evaluateViewed view input (next reply))

noncomputable def Program.evaluate {A : Type*} (input : List (StoredEdges.Edge n)) : Program n A → Law A :=
  evaluateViewed some input

theorem Program.expect_bind {E A B : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (program : Program n A) (next : A → Program n B) (f : B → ℝ) :
    (evaluateViewed view input (program.bind next)).expect f =
      (evaluateViewed view input program).expect (fun a => (evaluateViewed view input (next a)).expect f) := by
  induction program with
  | pure value => simp only [bind, evaluateViewed, Law.expect_pure]
  | metadata resume ih => exact ih (scanViewed view input)
  | construct unit builder resume ih =>
      simp only [bind, evaluateViewed, Law.expect_bind]
      apply congrArg (Hopset.Builder.evaluate (Backend.guardedViewedHandler (microViewed unit view) input) builder).expect
      funext stored
      exact ih stored
  | query unit request allowance resume ih =>
      simp only [bind, evaluateViewed, Law.expect_bind]
      apply congrArg (Backend.guardedViewedHandler (microViewed unit view) input request allowance).expect
      funext reply
      exact ih reply

def decoded (unit scale : ℕ) (reply : Core.BatchAPI.SparseReply n) (v : Fin n) : Distance :=
  WithTop.map (fun distance => scale * distance / unit) (Core.BatchAPI.lookup reply 0 v)

def extractGuesses (accuracy x : ℕ) (source : Fin n) (stored : Implicit.Representation n) :
    List {delta : ℕ // 0 < delta} → Labels n → Program n (Labels n)
  | [], answer => .pure answer
  | delta :: rest, answer =>
      let unit := Parameters.queryUnit n accuracy x
      .query unit (queryRequest stored x delta.val (8 * unit) source) (n + volume stored.blocks) fun result =>
        extractGuesses accuracy x source stored rest
          (match result with
            | none => answer
            | some reply => Vector.ofFn (fun v => min (answer.get v) (decoded unit delta.val reply v)))

/-- The persistent program contains only endpoint data, integer parameters,
stored stars/blocks, and streamed-query continuations. -/
def solve (hn : 0 < n) (accuracy x confidence : ℕ) (ha : 0 < accuracy) (source : Fin n) :
    Program n (Labels n) :=
  .metadata fun bounds =>
    if hmin : 0 < bounds.minWeight then
      let unit := Parameters.queryUnit n accuracy x
      .construct unit
        (Hopset.construct hn accuracy x confidence bounds.minWeight bounds.maximum ha hmin (emptyRepresentation n))
        (fun stored => extractGuesses accuracy x source stored
          (guesses n bounds.minWeight bounds.maximum hmin) (Vector.replicate n ⊤))
    else .pure (Vector.replicate n ⊤)

end StreamingReachability.Approx
