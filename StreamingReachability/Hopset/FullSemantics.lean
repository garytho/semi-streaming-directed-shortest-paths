module

public import StreamingReachability.Hopset.FullTrace

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

structure FrameValid (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (rank : Vector ℕ n) (r : ℕ) (sets : Vector (Finset (Fin n)) ns) (frame : Frame n cfg ns) : Prop where
  children : frame.result.children = geometricChildren cfg r stored input sets frame.choices
  blocks : frame.result.output.blocks = geometricBlocks cfg r stored input sets frame.choices
  subset : ∀ i, (frame.choices i).pivots ⊆ sets.get i
  earlyPivots : r < cfg.earlyLevel →
    ∀ i, (frame.choices i).pivots = CopyHistory.pivots (sets.get i) r (fun v => rank.get v)
  stars : r < cfg.earlyLevel →
    frame.result.output.explicit = emittedStars cfg (earlyTargets cfg r rank sets)
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg r stored.blocks sets (earlyTargets cfg r rank sets)) cfg.blockSize) input).records

theorem frame_early_fields (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) :
    Early.Sampling.Holds (frameLaw cfg hn stored input rank r sets) (fun frame =>
      (r < cfg.earlyLevel →
        ∀ i, (frame.choices i).pivots = CopyHistory.pivots (sets.get i) r (fun v => rank.get v)) ∧
      (r < cfg.earlyLevel → frame.result.output.explicit = emittedStars cfg (earlyTargets cfg r rank sets)
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg r stored.blocks sets (earlyTargets cfg r rank sets)) cfg.blockSize) input).records)) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [frameLaw, he, ↓reduceIte, queryFrameLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro owners _
    exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  · intro z hz
    exact ⟨fun h => False.elim (he h), fun h => False.elim (he h)⟩

theorem frame_valid (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator) :
    Early.Sampling.Holds (frameLaw cfg hn stored input rank r sets) (FrameValid cfg stored input rank r sets) := by
  intro z hz
  have hg := frameLaw_geometry cfg hn stored input rank r sets hs hp hsize hnum z hz
  have hs := frameLaw_pivots_subset cfg hn stored input rank r sets z hz
  have he := frame_early_fields cfg hn stored input rank r sets z hz
  exact ⟨hg.1, hg.2, hs, he.1, he.2⟩

inductive FullValid (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (rank : Vector ℕ n) : ℕ → ℕ → List (Finset (Fin n)) → List (GeometricEntry n cfg) → Prop
  | done (r : ℕ) (queue : List (Finset (Fin n))) : FullValid cfg stored input rank 0 r queue []
  | next {fuel r : ℕ} {queue : List (Finset (Fin n))} {frame : Frame n cfg queue.toArray.size}
      {tail : List (GeometricEntry n cfg)}
      (valid : FrameValid cfg stored input rank r queue.toArray.toVector frame)
      (rest : FullValid cfg stored input rank fuel (r + 1) frame.result.children tail) :
      FullValid cfg stored input rank (fuel + 1) r queue (⟨r, queue, frame⟩ :: tail)

theorem fullTrace_valid (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ) (queue : List (Finset (Fin n)))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator) :
    Early.Sampling.Holds (fullTraceLaw cfg hn stored input rank fuel r queue)
      (FullValid cfg stored input rank fuel r queue) := by
  induction fuel generalizing r queue with
  | zero => exact Early.Sampling.holds_pure [] _ (FullValid.done r queue)
  | succ fuel ih =>
      refine Reference.holds_bind_on _ _ (FrameValid cfg stored input rank r queue.toArray.toVector) _
        (frame_valid cfg hn stored input rank r queue.toArray.toVector hs hp hsize hnum) ?_
      intro frame hf
      refine Early.Sampling.holds_map (ih (r + 1) frame.result.children) (⟨r, queue, frame⟩ :: ·) _ ?_
      intro tail ht
      exact FullValid.next hf ht

end

end StreamingReachability.Hopset.Batched
