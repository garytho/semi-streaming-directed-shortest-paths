module

public import StreamingReachability.Hopset.GeometricTrace
public import StreamingReachability.Hopset.PrefixTransitions

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

def choiceRowsLaw (cfg : Config) (hn : 0 < n) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) : Law (Fin ns → Reference.Choice n cfg) :=
  let owners := Law.family ns (fun _ => Reference.ownerLaw n cfg)
  if r < cfg.earlyLevel then owners.map (fun rows i =>
    ⟨CopyHistory.pivots (sets.get i) r (fun v => rank.get v), rows i⟩)
  else (Law.family ns (lateDraw cfg hn r sets)).bind fun P =>
    owners.map fun rows i => ⟨P i, rows i⟩

theorem frameLaw_choices (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (f : (Fin ns → Reference.Choice n cfg) → ℝ) :
    (frameLaw cfg hn stored input rank r sets).expect (fun frame => f frame.choices) =
      (choiceRowsLaw cfg hn rank r sets).expect f := by
  by_cases he : r < cfg.earlyLevel <;>
    simp only [frameLaw, queryFrameLaw, choiceRowsLaw, he, ↓reduceIte,
      Law.expect_bind, Law.expect_map, frameFromOwners]

structure ControlEntry (n : ℕ) (cfg : Config) where
  level : ℕ
  queue : List (Finset (Fin n))
  choices : Fin queue.toArray.size → Reference.Choice n cfg

def GeometricEntry.control {cfg : Config} (entry : GeometricEntry n cfg) : ControlEntry n cfg :=
  ⟨entry.level, entry.queue, entry.frame.choices⟩

/-- This projected filtration intentionally omits advance/global target
metadata: those searches reveal future ranks but do not change recursion. -/
def controlTraceLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → Law (List (ControlEntry n cfg))
  | 0, _, _ => Law.pure []
  | fuel + 1, r, queue =>
      if AllGood cfg stored input r queue then
        (choiceRowsLaw cfg hn rank r queue.toArray.toVector).bind fun choices =>
          (controlTraceLaw cfg hn stored input rank fuel (r + 1)
            (geometricChildren cfg r stored input queue.toArray.toVector choices)).map
              (⟨r, queue, choices⟩ :: ·)
      else Law.pure []

theorem geometricTrace_control (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n)))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (f : List (ControlEntry n cfg) → ℝ) :
    (geometricTraceLaw cfg hn stored input rank fuel r queue).expect
        (fun trace => f (trace.map GeometricEntry.control)) =
      (controlTraceLaw cfg hn stored input rank fuel r queue).expect f := by
  induction fuel generalizing r queue f with
  | zero => simp [geometricTraceLaw, controlTraceLaw]
  | succ fuel ih =>
      by_cases hg : AllGood cfg stored input r queue
      · simp only [geometricTraceLaw, controlTraceLaw, hg, ↓reduceIte, Law.expect_bind, Law.expect_map]
        let next := fun choices => geometricChildren cfg r stored input queue.toArray.toVector choices
        have he (frame : Frame n cfg queue.toArray.size) :
            (geometricTraceLaw cfg hn stored input rank fuel (r + 1) frame.result.children).expect
                (fun tail => f ((⟨r, queue, frame⟩ :: tail).map GeometricEntry.control)) =
              (controlTraceLaw cfg hn stored input rank fuel (r + 1) frame.result.children).expect
                (fun tail => f (⟨r, queue, frame.choices⟩ :: tail)) := by
          simpa only [List.map_cons, GeometricEntry.control] using
            ih (r + 1) frame.result.children (fun tail => f (⟨r, queue, frame.choices⟩ :: tail))
        simp_rw [he]
        calc
          _ = (frameLaw cfg hn stored input rank r queue.toArray.toVector).expect (fun frame =>
              (controlTraceLaw cfg hn stored input rank fuel (r + 1) (next frame.choices)).expect
                (fun tail => f (⟨r, queue, frame.choices⟩ :: tail))) := by
            apply Reference.expect_congr_on
            refine Early.Sampling.holds_mono
              (frameLaw_geometry cfg hn stored input rank r queue.toArray.toVector hs hp hsize hnum) ?_
            intro frame hframe
            rw [hframe.1]
          _ = _ := frameLaw_choices cfg hn stored input rank r queue.toArray.toVector
            (fun choices => (controlTraceLaw cfg hn stored input rank fuel (r + 1) (next choices)).expect
              (fun tail => f (⟨r, queue, choices⟩ :: tail)))
      · simp only [geometricTraceLaw, controlTraceLaw, hg, ↓reduceIte, Law.expect_pure, List.map_nil]

end

end StreamingReachability.Hopset.Batched
