module

public import StreamingSSSP.Hopset.GeometricTrace

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def fullTraceLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → Law (List (GeometricEntry n cfg))
  | 0, _, _ => Law.pure []
  | fuel + 1, r, queue =>
      (frameLaw cfg hn stored input rank r queue.toArray.toVector).bind fun frame =>
        (fullTraceLaw cfg hn stored input rank fuel (r + 1) frame.result.children).map (⟨r, queue, frame⟩ :: ·)

def stopTrace (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    List (GeometricEntry n cfg) → List (GeometricEntry n cfg)
  | [] => []
  | entry :: trace =>
      if AllGood cfg stored input entry.level entry.queue then entry :: stopTrace cfg stored input trace else []

def TraceGood (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (trace : List (GeometricEntry n cfg)) : Prop :=
  ∀ entry ∈ trace, AllGood cfg stored input entry.level entry.queue

theorem stopTrace_good (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (trace : List (GeometricEntry n cfg)) : TraceGood cfg stored input (stopTrace cfg stored input trace) := by
  induction trace with
  | nil => simp [stopTrace, TraceGood]
  | cons entry trace ih =>
      by_cases hg : AllGood cfg stored input entry.level entry.queue
      · simp only [stopTrace, hg, ↓reduceIte]
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hg
        · exact ih e he
      · simp [stopTrace, hg, TraceGood]

theorem stopTrace_eq_iff (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (trace : List (GeometricEntry n cfg)) :
    stopTrace cfg stored input trace = trace ↔ TraceGood cfg stored input trace := by
  constructor
  · intro he
    rw [← he]
    exact stopTrace_good cfg stored input trace
  · intro hg
    induction trace with
    | nil => rfl
    | cons entry trace ih =>
        have hhead := hg entry (List.mem_cons_self)
        have htail := ih (fun e he => hg e (List.mem_cons_of_mem _ he))
        simp only [stopTrace, hhead, ↓reduceIte, htail]

theorem stopTrace_eq_of_length (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (trace : List (GeometricEntry n cfg))
    (h : (stopTrace cfg stored input trace).length = trace.length) :
    stopTrace cfg stored input trace = trace := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      by_cases hg : AllGood cfg stored input entry.level entry.queue
      · simp only [stopTrace, hg, ↓reduceIte, List.length_cons, Nat.add_right_cancel_iff] at h ⊢
        exact congrArg (List.cons entry) (ih h)
      · simp [stopTrace, hg] at h

theorem fullTrace_length (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ) (queue : List (Finset (Fin n))) :
    Early.Sampling.Holds (fullTraceLaw cfg hn stored input rank fuel r queue) (fun trace => trace.length = fuel) := by
  induction fuel generalizing r queue with
  | zero => exact Early.Sampling.holds_pure [] _ rfl
  | succ fuel ih =>
      apply Early.Sampling.holds_bind
      intro frame
      refine Early.Sampling.holds_map (ih (r + 1) frame.result.children) (⟨r, queue, frame⟩ :: ·) _ ?_
      intro trace ht
      simpa only [List.length_cons] using congrArg (· + 1) ht

/-- Extending unused randomness past a first bad queue does not change any
observable of the predictably stopped execution. -/
theorem fullTrace_stopped (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ) (queue : List (Finset (Fin n)))
    (f : List (GeometricEntry n cfg) → ℝ) :
    (fullTraceLaw cfg hn stored input rank fuel r queue).expect (fun trace => f (stopTrace cfg stored input trace)) =
      (geometricTraceLaw cfg hn stored input rank fuel r queue).expect f := by
  induction fuel generalizing r queue f with
  | zero => simp [fullTraceLaw, geometricTraceLaw, stopTrace]
  | succ fuel ih =>
      by_cases hg : AllGood cfg stored input r queue
      · simp only [fullTraceLaw, geometricTraceLaw, hg, ↓reduceIte, Law.expect_bind, Law.expect_map, stopTrace]
        apply congrArg (frameLaw cfg hn stored input rank r queue.toArray.toVector).expect
        funext frame
        exact ih (r + 1) frame.result.children (fun trace => f (⟨r, queue, frame⟩ :: trace))
      · simp only [fullTraceLaw, geometricTraceLaw, hg, ↓reduceIte, Law.expect_bind, Law.expect_map,
          stopTrace, Law.expect_pure, Law.expect_const]

end

end StreamingSSSP.Hopset.Batched
