module

public import StreamingReachability.Hopset.PathProcess

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

/-- A bad next queue only lowers the next potential; it is never conditioned on. -/
theorem pathStep_count (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (r : ℕ)
    (he : r < cfg.earlyLevel) (hb : 1 ≤ Parameters.ballSize n r)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts)
    (hcut : 48 * Parameters.ballSize n r * (Ranks.rate ps r).value / cfg.groups ≤ 1)
    (state : Option (State cfg stored input r)) :
    (pathStep cfg ps hnum stored input r state).expect (liftCount State.rawCount) ≤
      2 * liftCount (State.primeCount hnum) state +
        2 * (Ranks.rate ps r).value * liftCount (State.primeRelated hnum) state := by
  cases state with
  | none => simp [pathStep, liftCount]
  | some st =>
      by_cases hg : Batched.AllGood cfg stored input r st.queue
      · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_map]
        have hm := Law.expect_mono (currentDraw cfg ps r st.known st.queue.toArray.size) (fun sample =>
          (show liftCount State.rawCount (some (st.update hnum he sample)) ≤
            ((advanceAll cfg r hnum he
              (Batched.currentChoices cfg st.queue.toArray.toVector sample.1 sample.2)
              (splitAll cfg r hnum st.paths) (splitAll_short cfg r hnum st.paths)).length : ℝ)
            from by
              change ((st.update hnum he sample).rawCount : ℝ) ≤ ((st.update hnum he sample).paths.length : ℝ)
              exact_mod_cast (st.update hnum he sample).rawCount_le))
        have hmean := expected_advanceAll_count cfg ps r st.known hnum he (splitAll cfg r hnum st.paths)
          (splitAll_short cfg r hnum st.paths) (Parameters.ballSize n r) hgrid
          (fun i v => (st.ambient_balls hg hb i v).1) (fun i v => (st.ambient_balls hg hb i v).2) hcut
        apply hm.trans
        simpa only [liftCount, State.primeCount, State.primeRelated, hg, ↓reduceIte] using hmean
      · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_pure, liftCount,
          State.primeCount, State.primeRelated, Nat.cast_zero, mul_zero, add_zero, le_refl]

theorem pathStep_related (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (r : ℕ)
    (he : r < cfg.earlyLevel) (hr : r < ps.length)
    (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hb : 1 ≤ Parameters.ballSize n r) (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts)
    (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hbudget : 96 * (Parameters.ballSize n r : ℝ) ^ 2 * (Ranks.rate ps r).value ^ 2 ≤ cfg.groups)
    (state : Option (State cfg stored input r)) :
    (pathStep cfg ps hnum stored input r state).expect (liftCount State.rawRelated) ≤
      (18 / (Ranks.rate ps r).value) * liftCount (State.primeCount hnum) state := by
  cases state with
  | none => simp [pathStep, liftCount]
  | some st =>
      by_cases hg : Batched.AllGood cfg stored input r st.queue
      · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_map]
        have hm := Law.expect_mono (currentDraw cfg ps r st.known st.queue.toArray.size) (fun sample =>
          (show liftCount State.rawRelated (some (st.update hnum he sample)) ≤
            (related cfg (r + 1) (fun v => RankPrefix.nextKnown r (st.known v) (sample.1 v))
              (advanceAll cfg r hnum he
                (Batched.currentChoices cfg st.queue.toArray.toVector sample.1 sample.2)
                (splitAll cfg r hnum st.paths) (splitAll_short cfg r hnum st.paths)) : ℝ)
            from by
              change ((st.update hnum he sample).rawRelated : ℝ) ≤
                (related cfg (r + 1) (st.update hnum he sample).known (st.update hnum he sample).paths : ℝ)
              exact_mod_cast (st.update hnum he sample).rawRelated_le))
        have hmean := expected_advanceAll_related cfg ps r st.known hr hprefix hnum he (splitAll cfg r hnum st.paths)
          (splitAll_short cfg r hnum st.paths) (Parameters.ballSize n r) hgrid hM hp
          (fun i v => (st.ambient_balls hg hb i v).1) (fun i v => (st.ambient_balls hg hb i v).2) hbudget
        apply hm.trans
        simpa only [liftCount, State.primeCount, hg, ↓reduceIte] using hmean
      · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_pure, liftCount,
          State.primeCount, Nat.cast_zero, mul_zero, le_refl]

end

end StreamingReachability.Hopset.Following
