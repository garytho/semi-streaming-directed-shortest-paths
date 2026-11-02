module

public import StreamingSSSP.Hopset.GuardSemantics

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def applyStep (state : State n) (step : Step n) : State n where
  output := {
    explicit := state.output.explicit ++ step.output.explicit
    blocks := state.output.blocks ++ step.output.blocks }
  copies := state.copies + volume step.children
  records := state.records + step.records

def Accepted (cfg : Config) (r : ℕ) (state : State n) (step : Step n) : Prop :=
  state.records + step.records ≤ cfg.recordCap ∧
    (r < cfg.earlyLevel ∨
      (∀ B ∈ step.output.blocks, B.card ≤ cfg.blockSize) ∧
        volume (state.output.blocks ++ step.output.blocks) ≤ cfg.blockCap) ∧
    state.copies + volume step.children ≤ cfg.copyCap

theorem accepted_records (cfg : Config) (r : ℕ) (state : State n) (step : Step n)
    (h : Accepted cfg r state step) : (applyStep state step).records ≤ cfg.recordCap := h.1

theorem levels_succ (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (state : State n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hstate : state.records ≤ cfg.recordCap)
    (f : Option (Output n) → ℝ) :
    (Code.evaluate (Backend.guardedHandler input) (levels cfg hn stored rank (fuel + 1) r queue state)).expect f =
      (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect (fun step =>
        if Accepted cfg r state step then
          (Code.evaluate (Backend.guardedHandler input)
            (levels cfg hn stored rank fuel (r + 1) step.children (applyStep state step))).expect f
        else f none) := by
  let sets := queue.toArray.toVector
  by_cases he : r < cfg.earlyLevel
  · simp only [levels, he, ↓reduceIte]
    rw [Code.expect_bind, expect_guarded_batch cfg r stored input hn hs hp hsize sets
      (earlyTargets cfg r rank sets) state hstate]
    simp only [levelLaw, he, ↓reduceIte, queryLaw, Law.expect_map]
    dsimp only [sets]
    let targets := earlyTargets cfg r rank sets
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    by_cases hrecords : state.records + recordCharge stored.blocks reply ≤ cfg.recordCap
    · have hrecords' := hrecords
      dsimp only [reply, targets, sets] at hrecords'
      simp only [hrecords', ↓reduceIte]
      rw [Code.expect_bind, expect_pivotLoop]
      apply congrArg (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
      funext xs
      let pivots := pivotsFromOwners cfg r sets reply targets 0 xs
      by_cases hcopies : state.copies +
          volume (earlyFringes cfg r sets pivots reply ++ earlyCore cfg r sets pivots reply) ≤ cfg.copyCap
      · dsimp only [pivots, reply, targets, sets] at hcopies
        simp only [assemble, Accepted, he, hrecords', hcopies, ↓reduceIte, true_or, true_and,
          applyStep, List.append_nil]
      · dsimp only [pivots, reply, targets, sets] at hcopies
        simp only [assemble, Accepted, he, hrecords', hcopies, ↓reduceIte, true_or, true_and,
          Code.evaluate, Law.expect_pure]
    · have hrecords' := hrecords
      dsimp only [reply, targets, sets] at hrecords'
      simp only [hrecords', ↓reduceIte, assemble, Accepted, he, false_and, Law.expect_const]
  · simp only [levels, he, ↓reduceIte]
    rw [Code.expect_bind, expect_lateTargetLoop]
    simp only [levelLaw, he, ↓reduceIte, Law.expect_bind]
    apply congrArg (Law.family queue.toArray.size (lateDraw cfg hn r sets)).expect
    funext P
    rw [Code.expect_bind, expect_guarded_batch cfg r stored input hn hs hp hsize sets
      (pivotTargets P) state hstate]
    simp only [queryLaw, Law.expect_map]
    dsimp only [sets]
    let targets := pivotTargets P
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    by_cases hrecords : state.records + recordCharge stored.blocks reply ≤ cfg.recordCap
    · have hrecords' := hrecords
      dsimp only [reply, targets, sets] at hrecords'
      simp only [hrecords', ↓reduceIte]
      rw [Code.expect_bind, expect_pivotLoop]
      apply congrArg (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
      funext xs
      let pivots := pivotsFromOwners cfg r sets reply targets 0 xs
      let blocks := lateBlocks cfg r sets pivots reply
      let children := if r < cfg.maximumLevel then lateCore cfg r sets pivots reply else []
      by_cases hblocks : (∀ B ∈ blocks, B.card ≤ cfg.blockSize) ∧
          volume (state.output.blocks ++ blocks) ≤ cfg.blockCap
      · have hblocks' := hblocks
        dsimp only [blocks, pivots, reply, targets, sets] at hblocks'
        have hblocksEq := propext (iff_true_intro hblocks')
        by_cases hcopies : state.copies + volume children ≤ cfg.copyCap
        · dsimp only [children, pivots, reply, targets, sets] at hcopies
          simp only [assemble, Accepted, he, hrecords', hblocksEq, hcopies, ↓reduceIte,
            false_or, true_and, and_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, applyStep]
        · dsimp only [children, pivots, reply, targets, sets] at hcopies
          simp only [assemble, Accepted, he, hrecords', hblocksEq, hcopies, ↓reduceIte,
            false_or, true_and, and_false, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
            Code.evaluate, Law.expect_pure]
      · have hblocks' := hblocks
        dsimp only [blocks, pivots, reply, targets, sets] at hblocks'
        simp only [assemble, Accepted, he, hrecords', hblocks', ↓reduceIte, false_or, true_and,
          false_and, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Code.evaluate, Law.expect_pure]
    · have hrecords' := hrecords
      dsimp only [reply, targets, sets] at hrecords'
      simp only [hrecords', ↓reduceIte, assemble, Accepted, he, false_and, Law.expect_const]

end

end StreamingSSSP.Hopset.Batched
