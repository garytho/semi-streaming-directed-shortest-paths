module

public import StreamingSSSP.Hopset.LevelSemantics
public import StreamingSSSP.Hopset.ProgramSoundness

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def levelsLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → State n → Law (Option (Output n))
  | 0, _, _, state => Law.pure (some state.output)
  | fuel + 1, r, queue, state =>
      (levelLaw cfg hn stored input rank r queue.toArray.toVector).bind fun step =>
        if Accepted cfg r state step then
          levelsLaw cfg hn stored input rank fuel (r + 1) step.children (applyStep state step)
        else Law.pure none

theorem levels_equiv (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (state : State n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hstate : state.records ≤ cfg.recordCap)
    (f : Option (Output n) → ℝ) :
    (Code.evaluate (Backend.guardedHandler input) (levels cfg hn stored rank fuel r queue state)).expect f =
      (levelsLaw cfg hn stored input rank fuel r queue state).expect f := by
  induction fuel generalizing r queue state with
  | zero => simp only [levels, levelsLaw, Code.evaluate, Law.expect_pure]
  | succ fuel ih =>
      rw [levels_succ cfg hn stored input rank fuel r queue state hs hp hsize hstate f,
        levelsLaw, Law.expect_bind]
      apply congrArg (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
      funext step
      by_cases ha : Accepted cfg r state step
      · simp only [ha, ↓reduceIte]
        exact ih (r + 1) step.children (applyStep state step) (accepted_records cfg r state step ha)
      · simp only [ha, ↓reduceIte, Law.expect_pure]

def trialLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) : Law (Option (Output n)) :=
  if n ≤ cfg.copyCap then
    (Law.family n (fun _ =>
      Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).bind fun xs =>
      let rank := Vector.ofFn xs
      let sets : Vector (Finset (Fin n)) 1 := Vector.replicate 1 Finset.univ
      let targets := globalTargets cfg rank
      let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg 0 stored.blocks sets targets) cfg.blockSize) input).records
      if recordCharge stored.blocks reply ≤ cfg.recordCap then
        levelsLaw cfg hn stored input rank (cfg.maximumLevel + 1) 0 [Finset.univ]
          ⟨{ explicit := emittedStars cfg targets reply }, n, recordCharge stored.blocks reply⟩
      else Law.pure none
  else Law.pure none

theorem fixedGuess_equiv (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (f : Option (Output n) → ℝ) :
    (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).expect f =
      (trialLaw cfg hn stored input).expect f := by
  by_cases hc : n ≤ cfg.copyCap
  · simp only [fixedGuess, trialLaw, hc, ↓reduceIte, Code.ranks]
    rw [Code.expect_bind, Code.expect_rankVector, Law.expect_bind]
    apply congrArg (Law.family n (fun _ =>
      Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).expect
    funext xs
    simp only
    rw [Code.expect_bind, expect_guarded_batch cfg 0 stored input hn hs hp hsize
      (Vector.replicate 1 Finset.univ) (globalTargets cfg (Vector.ofFn xs)) ⟨{}, n, 0⟩ (by simp)]
    simp only [zero_add, List.nil_append]
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg 0 stored.blocks (Vector.replicate 1 Finset.univ)
        (globalTargets cfg (Vector.ofFn xs))) cfg.blockSize) input).records
    by_cases hr : recordCharge stored.blocks reply ≤ cfg.recordCap
    · have hr' := hr
      dsimp only [reply] at hr'
      simp only [hr', ↓reduceIte]
      exact levels_equiv cfg hn stored input (Vector.ofFn xs) _ _ _ _ hs hp hsize hr f
    · dsimp only [reply] at hr
      simp only [hr, ↓reduceIte, Law.expect_pure]
  · simp only [fixedGuess, trialLaw, hc, ↓reduceIte, Code.evaluate, Law.expect_pure]

theorem fixedGuess_viewed_equiv {E : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input.filterMap view, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (f : Option (Output n) → ℝ) :
    (Code.evaluate (Backend.guardedViewedHandler view input) (fixedGuess cfg hn stored)).expect f =
      (trialLaw cfg hn stored (input.filterMap view)).expect f := by
  rw [Backend.guardedViewedHandler_eq]
  exact fixedGuess_equiv cfg hn stored _ hs hp hsize f

end

end StreamingSSSP.Hopset.Batched
