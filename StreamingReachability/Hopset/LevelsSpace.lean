module

public import StreamingReachability.Hopset.ControllerSpace

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n ns : ℕ}

theorem late_targets_count (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (indices : List (Fin ns)) :
    (lateTargetLoop cfg hn r sets indices).Ensures (fun targets => targets.length ≤ indexVolume sets indices) := by
  induction indices with
  | nil => simp [lateTargetLoop, Code.Ensures, indexVolume]
  | cons i indices ih =>
      have hchosen : (if r < cfg.maximumLevel then
          Code.subset (PivotProfile.rate n hn cfg.k cfg.logarithm r) (members (sets.get i))
          else Code.pure (sets.get i)).Ensures (fun P => P ⊆ sets.get i) := by
        split
        · exact subset_of_members _ _
        · exact Finset.Subset.refl _
      apply Code.ensures_bind _ _ _ _ hchosen
      intro P hP
      apply Code.ensures_map
      apply Code.ensures_mono _ _ _ ih
      intro targets ht
      simp only [List.length_append, List.length_map, members_count, indexVolume, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (Finset.card_le_card hP) ht

def queueVector (queue : List (Finset (Fin n))) := queue.toArray.toVector

theorem queue_volume (queue : List (Finset (Fin n))) : setVolume (queueVector queue) = volume queue := by
  simp only [queueVector, setVolume, Array.toVector, Vector.toList_mk, List.toList_toArray]

/-- The operational boundary rules are the literal branches of `fixedGuess`
and `levels`. A returned batch or pivot list is witnessed by an actual atom of
the same free-program interpreter, not by an assumed numerical invariant. -/
inductive LevelBoundary (cfg : Config) (hn : 0 < n) (handler : Code.Handler n)
    (stored : Implicit.Representation n) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → State n → Prop
  | initial (hcopy : n ≤ cfg.copyCap) (result : Core.BatchAPI.SparseReply n × State n)
      (returned : Returned handler
        (batch cfg 0 stored (Vector.replicate 1 Finset.univ) (globalTargets cfg rank) ⟨{}, n, 0⟩) result) :
      LevelBoundary cfg hn handler stored rank (cfg.maximumLevel + 1) 0 [Finset.univ] result.2
  | early {fuel r : ℕ} {queue : List (Finset (Fin n))} {state : State n}
      (before : LevelBoundary cfg hn handler stored rank (fuel + 1) r queue state)
      (early : r < cfg.earlyLevel) (result : Core.BatchAPI.SparseReply n × State n)
      (returned : Returned handler (batch cfg r stored (queueVector queue)
        (earlyTargets cfg r rank (queueVector queue)) state) result)
      (pivots : List (Pivot n queue.toArray.size))
      (chosen : Returned handler (pivotLoop cfg r (queueVector queue) result.1
        (earlyTargets cfg r rank (queueVector queue)) 0) pivots)
      (checked : result.2.copies + volume
        (earlyFringes cfg r (queueVector queue) pivots result.1 ++ earlyCore cfg r (queueVector queue) pivots result.1) ≤
          cfg.copyCap) :
      LevelBoundary cfg hn handler stored rank fuel (r + 1)
        (earlyFringes cfg r (queueVector queue) pivots result.1 ++ earlyCore cfg r (queueVector queue) pivots result.1)
        { result.2 with copies := (result.2.copies + volume
          (earlyFringes cfg r (queueVector queue) pivots result.1 ++ earlyCore cfg r (queueVector queue) pivots result.1)) }
  | late {fuel r : ℕ} {queue : List (Finset (Fin n))} {state : State n}
      (before : LevelBoundary cfg hn handler stored rank (fuel + 1) r queue state)
      (late : ¬ r < cfg.earlyLevel) (targets : List (Target n queue.toArray.size))
      (sampled : Returned handler (lateTargetLoop cfg hn r (queueVector queue) (List.finRange _)) targets)
      (result : Core.BatchAPI.SparseReply n × State n)
      (returned : Returned handler (batch cfg r stored (queueVector queue) targets state) result)
      (pivots : List (Pivot n queue.toArray.size))
      (chosen : Returned handler (pivotLoop cfg r (queueVector queue) result.1 targets 0) pivots)
      (blocks : ((lateBlocks cfg r (queueVector queue) pivots result.1).all (fun B => decide (B.card ≤ cfg.blockSize)) &&
        decide (volume (result.2.output.blocks ++ lateBlocks cfg r (queueVector queue) pivots result.1) ≤ cfg.blockCap)) = true)
      (checked : result.2.copies + volume
        (if r < cfg.maximumLevel then lateCore cfg r (queueVector queue) pivots result.1 else []) ≤ cfg.copyCap) :
      LevelBoundary cfg hn handler stored rank fuel (r + 1)
        (if r < cfg.maximumLevel then lateCore cfg r (queueVector queue) pivots result.1 else [])
        { result.2 with
          copies := result.2.copies + volume (if r < cfg.maximumLevel then lateCore cfg r (queueVector queue) pivots result.1 else [])
          output := { result.2.output with blocks := result.2.output.blocks ++ lateBlocks cfg r (queueVector queue) pivots result.1 } }

theorem LevelBoundary.invariant {cfg : Config} {hn : 0 < n} {handler : Code.Handler n}
    {stored : Implicit.Representation n} {rank : Vector ℕ n} {fuel r : ℕ}
    {queue : List (Finset (Fin n))} {state : State n}
    (h : LevelBoundary cfg hn handler stored rank fuel r queue state) :
    state.Bounded cfg ∧ volume queue ≤ cfg.copyCap ∧ queue.length ≤ 3 * cfg.copyCap ∧
      fuel ≤ cfg.maximumLevel + 1 ∧
      state.output.blocks.length ≤ 2 * (cfg.maximumLevel + 1 - fuel) * cfg.copyCap := by
  induction h with
  | initial hcopy result returned =>
      have hb : (State.mk {} n 0 : State n).Bounded cfg :=
        ⟨by simp, by simp, by simp [volume], by simp, hcopy⟩
      have hs := Returned.ensures _ _ _ returned _ (batch_bounded _ _ _ _ _ _ hb)
      have he := Returned.ensures _ _ _ returned _ (batch_blocks_unchanged _ _ _ _ _ _)
      refine ⟨hs, by simpa [volume] using hcopy, by simp; omega, le_rfl, ?_⟩
      rw [he]
      simp
  | @early fuel r queue state before early result returned pivots chosen checked ih =>
      have hs := Returned.ensures _ _ _ returned _ (batch_bounded _ _ _ _ _ _ ih.1)
      have he := Returned.ensures _ _ _ returned _ (batch_blocks_unchanged _ _ _ _ _ _)
      have hp := Returned.ensures _ _ _ chosen _ (pivot_loop_count _ _ _ _ _ _)
      have ht := early_targets_count cfg r rank (queueVector queue)
      have hvol : setVolume (queueVector queue) ≤ cfg.copyCap := by rw [queue_volume]; exact ih.2.1
      have hc := early_children_count cfg r (queueVector queue) pivots result.1 (hp.trans ht)
      have hnew : ({ result.2 with copies := (result.2.copies + volume
          (earlyFringes cfg r (queueVector queue) pivots result.1 ++ earlyCore cfg r (queueVector queue) pivots result.1)) } : State n).Bounded cfg :=
        ⟨hs.records_le, hs.stars_le, hs.blocks_le, hs.block_size, checked⟩
      refine ⟨hnew, by omega, hc.trans (Nat.mul_le_mul_left 3 hvol), by omega, ?_⟩
      change result.2.output.blocks.length ≤ _
      rw [he]
      have hh := ih.2.2.2.2
      have hdiff : cfg.maximumLevel + 1 - fuel = (cfg.maximumLevel + 1 - (fuel + 1)) + 1 := by omega
      rw [hdiff, Nat.mul_add, Nat.add_mul]
      omega
  | @late fuel r queue state before late targets sampled result returned pivots chosen blocks checked ih =>
      have hs := Returned.ensures _ _ _ returned _ (batch_bounded _ _ _ _ _ _ ih.1)
      have he := Returned.ensures _ _ _ returned _ (batch_blocks_unchanged _ _ _ _ _ _)
      have hp := Returned.ensures _ _ _ chosen _ (pivot_loop_count _ _ _ _ _ _)
      have ht := Returned.ensures _ _ _ sampled _ (late_targets_count _ _ _ _ _)
      rw [index_volume_all] at ht
      have hvol : setVolume (queueVector queue) ≤ cfg.copyCap := by rw [queue_volume]; exact ih.2.1
      have hb := checked_blocks cfg result.2.output.blocks _ hs.block_size blocks
      have hnew : ({ result.2 with
          copies := result.2.copies + volume (if r < cfg.maximumLevel then lateCore cfg r (queueVector queue) pivots result.1 else [])
          output := { result.2.output with blocks := result.2.output.blocks ++ lateBlocks cfg r (queueVector queue) pivots result.1 } } : State n).Bounded cfg :=
        ⟨hs.records_le, hs.stars_le, hb.1, hb.2, checked⟩
      refine ⟨hnew, by omega, ?_, by omega, ?_⟩
      · split_ifs
        · simpa only [late_core_count, List.size_toArray] using ih.2.2.1
        · simp
      · change (result.2.output.blocks ++ lateBlocks cfg r (queueVector queue) pivots result.1).length ≤ _
        rw [List.length_append, he, late_blocks_count]
        have hcount := hp.trans (ht.trans hvol)
        have hh := ih.2.2.2.2
        have hdiff : cfg.maximumLevel + 1 - fuel = (cfg.maximumLevel + 1 - (fuel + 1)) + 1 := by omega
        rw [hdiff, Nat.mul_add, Nat.add_mul]
        omega

/-- This applies before either geometric guard: its statement has no successful
copy/block check and thus includes the locally aborted materializations. -/
theorem LevelBoundary.geometry_space {cfg : Config} {hn : 0 < n} {handler : Code.Handler n}
    {stored : Implicit.Representation n} {rank : Vector ℕ n} {fuel r : ℕ}
    {queue : List (Finset (Fin n))} {state : State n}
    (h : LevelBoundary cfg hn handler stored rank fuel r queue state)
    (targets : List (Target n queue.toArray.size)) (ht : targets.length ≤ 2 * cfg.copyCap)
    (result : Core.BatchAPI.SparseReply n × State n)
    (returned : Returned handler (batch cfg r stored (queueVector queue) targets state) result)
    (pivots : List (Pivot n queue.toArray.size))
    (chosen : Returned handler (pivotLoop cfg r (queueVector queue) result.1 targets 0) pivots) :
    storedCells stored + stateCells result.2 + geometryCells cfg r (queueVector queue) pivots result.1 +
      3 * n + 8 * targets.length + selectorCells n cfg ≤
        controllerCells n cfg stored (2 * (cfg.maximumLevel + 1) * cfg.copyCap) := by
  have hi := h.invariant
  have hs := Returned.ensures _ _ _ returned _ (batch_bounded _ _ _ _ _ _ hi.1)
  have he := Returned.ensures _ _ _ returned _ (batch_blocks_unchanged _ _ _ _ _ _)
  have hr := Returned.ensures _ _ _ returned _ (batch_reply_length _ _ _ _ _ _)
  have hp := Returned.ensures _ _ _ chosen _ (pivot_loop_count _ _ _ _ _ _)
  have hid := Returned.ensures _ _ _ chosen _ (pivot_loop_identifiers _ _ _ _ _ _)
  have hh : result.2.output.blocks.length ≤ 2 * (cfg.maximumLevel + 1) * cfg.copyCap := by
    rw [he]
    exact hi.2.2.2.2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.sub_le _ _)))
  exact controller_geometry cfg r stored (queueVector queue) targets pivots result.1 result.2 _
    hs hh (by simpa only [List.size_toArray] using hi.2.2.1)
    (by rw [queue_volume]; exact hi.2.1) ht hp hid hr

end StreamingReachability.Hopset.Measured
