module

public import StreamingReachability.Hopset.Trial

@[expose] public section

namespace StreamingReachability.Hopset

variable {n : ℕ}

structure Output.Bounded (cfg : Config) (out : Output n) : Prop where
  stars_le : out.explicit.length ≤ cfg.recordCap
  blocks_le : volume out.blocks ≤ cfg.blockCap
  block_size : ∀ B ∈ out.blocks, B.card ≤ cfg.blockSize

structure State.Bounded (cfg : Config) (state : State n) : Prop where
  records_le : state.records ≤ cfg.recordCap
  stars_le : state.output.explicit.length ≤ state.records
  blocks_le : volume state.output.blocks ≤ cfg.blockCap
  block_size : ∀ B ∈ state.output.blocks, B.card ≤ cfg.blockSize
  copies_le : state.copies ≤ cfg.copyCap

theorem State.Bounded.output_bounded {cfg : Config} {state : State n}
    (h : state.Bounded cfg) : state.output.Bounded cfg :=
  ⟨h.stars_le.trans h.records_le, h.blocks_le, h.block_size⟩

theorem batch_bounded (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (state : State n) (hstate : state.Bounded cfg) :
    (batch cfg r stored sets targets state).Ensures fun result => result.2.Bounded cfg := by
  dsimp only [batch, Code.Ensures]
  intro reply
  split
  next h =>
    refine ⟨h, ?_, hstate.blocks_le, hstate.block_size, hstate.copies_le⟩
    change (state.output.explicit ++ emittedStars cfg targets reply).length ≤
      state.records + recordCharge stored.blocks reply
    simp only [List.length_append]
    exact add_le_add hstate.stars_le
      ((emittedStars_length cfg targets reply).trans
        (reply_length_le_charge stored.blocks reply))
  next h => trivial

theorem levels_bounded (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (rank : Vector ℕ n) (fuel r : ℕ) (queue : List (Finset (Fin n)))
    (state : State n) (hstate : state.Bounded cfg) :
    (levels cfg hn stored rank fuel r queue state).Ensures (Output.Bounded cfg) := by
  induction fuel generalizing r queue state with
  | zero => exact hstate.output_bounded
  | succ fuel ih =>
      dsimp only [levels]
      split
      next hr =>
        apply Code.ensures_bind _ _ _ _ (batch_bounded cfg r stored _ _ state hstate)
        intro result hresult
        apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
        intro pivots _
        split
        next hc =>
          exact ih (r + 1) _ _
            ⟨hresult.records_le, hresult.stars_le, hresult.blocks_le,
              hresult.block_size, hc⟩
        next hc => trivial
      next hr =>
        apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
        intro targets _
        apply Code.ensures_bind _ _ _ _ (batch_bounded cfg r stored _ _ state hstate)
        intro result hresult
        apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
        intro pivots _
        split
        next hb =>
          have hparts :
              (lateBlocks cfg r queue.toArray.toVector pivots result.1).all
                  (fun B => decide (B.card ≤ cfg.blockSize)) = true ∧
                decide (volume (result.2.output.blocks ++
                  lateBlocks cfg r queue.toArray.toVector pivots result.1) ≤ cfg.blockCap) = true := by
            simpa only [Bool.and_eq_true] using hb
          have hvol := of_decide_eq_true hparts.2
          have hsizes : ∀ B ∈ lateBlocks cfg r queue.toArray.toVector pivots result.1,
              B.card ≤ cfg.blockSize := by
            intro B hB
            exact of_decide_eq_true ((List.all_eq_true.mp hparts.1) B hB)
          have hcombined : ∀ B ∈ result.2.output.blocks ++
              lateBlocks cfg r queue.toArray.toVector pivots result.1,
              B.card ≤ cfg.blockSize := by
            intro B hB
            rcases List.mem_append.mp hB with hold | hnew
            · exact hresult.block_size B hold
            · exact hsizes B hnew
          by_cases hcontinue : r < cfg.maximumLevel
          · simp only [hcontinue, ↓reduceIte]
            split
            next hc =>
              apply ih
              exact ⟨hresult.records_le, hresult.stars_le, hvol, hcombined, hc⟩
            next hc => trivial
          · simp only [hcontinue, ↓reduceIte]
            split
            next hc =>
              apply ih
              exact ⟨hresult.records_le, hresult.stars_le, hvol, hcombined, hc⟩
            next hc => trivial
        next hb => trivial

theorem fixedGuess_bounded (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n) :
    (fixedGuess cfg hn stored).Ensures (Output.Bounded cfg) := by
  dsimp only [fixedGuess]
  split
  next hncap =>
    apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
    intro rank _
    apply Code.ensures_bind _ _ _ _
      (batch_bounded cfg 0 stored _ _ ⟨{}, n, 0⟩
        ⟨by change 0 ≤ cfg.recordCap; omega, by simp, by simp [volume], by simp, hncap⟩)
    intro result hresult
    exact levels_bounded cfg hn stored rank _ _ _ _ hresult
  next hncap => trivial

theorem fixedGuess_output_probability (handler : Code.Handler n) (cfg : Config)
    (hn : 0 < n) (stored : Implicit.Representation n) :
    (Code.evaluate handler (fixedGuess cfg hn stored)).prob
      (fun result => match result with | none => True | some out => out.Bounded cfg) = 1 := by
  convert Code.probability_ensures handler _ _ (fixedGuess_bounded cfg hn stored) using 1
  apply Law.prob_congr
  intro result
  cases result <;> rfl

end StreamingReachability.Hopset
