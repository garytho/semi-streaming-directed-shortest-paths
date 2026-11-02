module

public import StreamingReachability.Hopset.TraceValidity

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def AcceptedTrace (cfg : Config) : State n → List (Entry n) → Prop
  | _, [] => True
  | state, entry :: trace =>
      Accepted cfg entry.level state entry.step ∧ AcceptedTrace cfg (applyStep state entry.step) trace

def OutputSatisfies (P : Output n → Prop) : Option (Output n) → Prop
  | none => False
  | some output => P output

theorem final_caps_accepted (cfg : Config) (state : State n) (trace : List (Entry n))
    (hshape : ∀ entry ∈ trace, ∀ B ∈ entry.step.output.blocks, B.card ≤ cfg.blockSize)
    (hc : (replay state trace).copies ≤ cfg.copyCap)
    (hr : (replay state trace).records ≤ cfg.recordCap)
    (hb : volume (replay state trace).output.blocks ≤ cfg.blockCap) :
    AcceptedTrace cfg state trace := by
  induction trace generalizing state with
  | nil => trivial
  | cons entry trace ih =>
      have hrecord : (applyStep state entry.step).records ≤ cfg.recordCap := by
        have h := replay_records (applyStep state entry.step) trace
        change (replay (applyStep state entry.step) trace).records ≤ cfg.recordCap at hr
        omega
      have hcopies : (applyStep state entry.step).copies ≤ cfg.copyCap :=
        (replay_copies_mono (applyStep state entry.step) trace).trans hc
      have hblocks : volume (applyStep state entry.step).output.blocks ≤ cfg.blockCap := by
        have h := replay_blocks (applyStep state entry.step) trace
        change volume (replay (applyStep state entry.step) trace).output.blocks ≤ cfg.blockCap at hb
        omega
      refine ⟨⟨hrecord, Or.inr ⟨hshape entry (by simp), hblocks⟩, hcopies⟩, ?_⟩
      exact ih (applyStep state entry.step)
        (fun e he => hshape e (by simp [he])) hc hr hb

theorem trace_success_le (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (state : State n) (P : Output n → Prop) :
    (traceLaw cfg hn stored input rank fuel r queue).prob (fun trace =>
        trace.length = fuel ∧ AcceptedTrace cfg state trace ∧ P (replay state trace).output) ≤
      (levelsLaw cfg hn stored input rank fuel r queue state).prob (OutputSatisfies P) := by
  induction fuel generalizing r queue state with
  | zero =>
      by_cases ho : P state.output <;>
        simp [traceLaw, levelsLaw, Law.prob, AcceptedTrace, replay, OutputSatisfies, ho]
  | succ fuel ih =>
      by_cases hg : AllGood cfg stored input r queue
      · simp only [traceLaw, hg, ↓reduceIte, levelsLaw, Law.prob_bind, Law.prob_map]
        apply Law.expect_mono
        intro step
        by_cases ha : Accepted cfg r state step
        · simp only [ha, ↓reduceIte]
          simpa only [List.length_cons, Nat.add_right_cancel_iff, AcceptedTrace, ha, true_and, replay] using
            ih (r + 1) step.children (applyStep state step)
        · simp [AcceptedTrace, ha, OutputSatisfies, Law.prob]
      · calc
          _ = 0 := by simp [traceLaw, hg, Law.prob]
          _ ≤ _ := Law.prob_nonneg _ _

theorem short_probability_le_bad (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (hg : AllGood cfg stored input r queue) :
    (traceLaw cfg hn stored input rank fuel r queue).prob (fun trace => trace.length ≠ fuel) ≤
      (traceLaw cfg hn stored input rank fuel r queue).expect
        (fun trace => (traceCost (badReward cfg stored input) trace : ℝ)) := by
  unfold Law.prob
  apply Early.Sampling.expect_mono_on
  refine Early.Sampling.holds_mono (traceLaw_valid cfg hn stored input rank fuel r queue) ?_
  intro trace hvalid
  change (@ite ℝ (trace.length ≠ fuel) (Classical.propDecidable _) 1 0) ≤
    (traceCost (badReward cfg stored input) trace : ℝ)
  by_cases hc : trace.length = fuel
  · rw [ite_eq_right (by intro h; exact h hc)]
    exact Nat.cast_nonneg _
  · have hpos := hvalid.short_has_bad hg (by have := hvalid.length_le; omega)
    rw [ite_eq_left hc]
    exact_mod_cast (show 1 ≤ traceCost (badReward cfg stored input) trace by omega)

end

end StreamingReachability.Hopset.Batched
