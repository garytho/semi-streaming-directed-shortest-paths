module

public import StreamingReachability.Hopset.FrameGeometry
public import StreamingReachability.Hopset.TraceShape

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

/-- Owner rows are latent proof variables; the executable controller does not
allocate this enriched trace or the unselected owner coordinates. -/
structure GeometricEntry (n : ℕ) (cfg : Config) where
  level : ℕ
  queue : List (Finset (Fin n))
  frame : Frame n cfg queue.toArray.size

def GeometricEntry.erase {cfg : Config} (entry : GeometricEntry n cfg) : Entry n :=
  ⟨entry.level, entry.queue, entry.frame.result⟩

def geometricTraceLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → Law (List (GeometricEntry n cfg))
  | 0, _, _ => Law.pure []
  | fuel + 1, r, queue =>
      if AllGood cfg stored input r queue then
        (frameLaw cfg hn stored input rank r queue.toArray.toVector).bind fun frame =>
          (geometricTraceLaw cfg hn stored input rank fuel (r + 1) frame.result.children).map
            (⟨r, queue, frame⟩ :: ·)
      else Law.pure []

theorem geometricTrace_erase (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (f : List (Entry n) → ℝ) :
    (geometricTraceLaw cfg hn stored input rank fuel r queue).expect
        (fun trace => f (trace.map GeometricEntry.erase)) =
      (traceLaw cfg hn stored input rank fuel r queue).expect f := by
  induction fuel generalizing r queue f with
  | zero => simp [geometricTraceLaw, traceLaw]
  | succ fuel ih =>
      by_cases hg : AllGood cfg stored input r queue
      · simp only [geometricTraceLaw, traceLaw, hg, ↓reduceIte, Law.expect_bind, Law.expect_map]
        have he (frame : Frame n cfg queue.toArray.size) :
            (geometricTraceLaw cfg hn stored input rank fuel (r + 1) frame.result.children).expect
                (fun tail => f ((⟨r, queue, frame⟩ :: tail).map GeometricEntry.erase)) =
              (traceLaw cfg hn stored input rank fuel (r + 1) frame.result.children).expect
                (fun tail => f (⟨r, queue, frame.result⟩ :: tail)) := by
          simpa only [List.map_cons, GeometricEntry.erase] using
            ih (r + 1) frame.result.children (fun tail => f (⟨r, queue, frame.result⟩ :: tail))
        simp_rw [he]
        exact frameLaw_result cfg hn stored input rank r queue.toArray.toVector
          (fun step => (traceLaw cfg hn stored input rank fuel (r + 1) step.children).expect
            (fun tail => f (⟨r, queue, step⟩ :: tail)))
      · simp only [geometricTraceLaw, traceLaw, hg, ↓reduceIte, Law.expect_pure, List.map_nil]

theorem geometricTrace_erase_probability (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (P : List (Entry n) → Prop) :
    (geometricTraceLaw cfg hn stored input rank fuel r queue).prob
        (fun trace => P (trace.map GeometricEntry.erase)) =
      (traceLaw cfg hn stored input rank fuel r queue).prob P :=
  geometricTrace_erase cfg hn stored input rank fuel r queue (fun trace => if P trace then 1 else 0)

end

end StreamingReachability.Hopset.Batched
