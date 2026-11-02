module

public import StreamingReachability.Hopset.FullTrace

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def afterQueue {cfg : Config} : List (Finset (Fin n)) →
    List (GeometricEntry n cfg) → List (Finset (Fin n))
  | queue, [] => queue
  | _, entry :: tail => afterQueue entry.frame.result.children tail

theorem fullTrace_split (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (left right r : ℕ)
    (queue : List (Finset (Fin n))) (f : List (GeometricEntry n cfg) → ℝ) :
    (fullTraceLaw cfg hn stored input rank (left + right) r queue).expect f =
      (fullTraceLaw cfg hn stored input rank left r queue).expect (fun pre =>
        (fullTraceLaw cfg hn stored input rank right (r + left) (afterQueue queue pre)).expect
          (fun tail => f (pre ++ tail))) := by
  induction left generalizing r queue f with
  | zero => simp only [Nat.zero_add, fullTraceLaw, Law.expect_pure, afterQueue, Nat.add_zero, List.nil_append]
  | succ left ih =>
      have hlevel : r + (left + 1) = (r + 1) + left := by omega
      simp only [Nat.succ_add, fullTraceLaw, Law.expect_bind, Law.expect_map]
      apply congrArg (frameLaw cfg hn stored input rank r queue.toArray.toVector).expect
      funext frame
      simpa only [afterQueue, List.cons_append, hlevel] using
        ih (r + 1) frame.result.children (fun trace => f (⟨r, queue, frame⟩ :: trace))

end

end StreamingReachability.Hopset.Batched
