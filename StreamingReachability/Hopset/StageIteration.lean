module

public import StreamingReachability.Hopset.HopProgress

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem stages_progress_failure (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hmin : ∀ u v, u ≠ v → ((wmin * Parameters.queryUnit n accuracy x : ℕ) : Distance) ≤
      StoredEdges.graphOfEdges input u v)
    (hmax : Exact.WeightsBounded (StoredEdges.graphOfEdges input) (wmax * Parameters.queryUnit n accuracy x))
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (trials count i : ℕ) (hi : i + count ≤ Parameters.ell n)
    (stored : Implicit.Representation n) (hs : StoredValid (StoredEdges.graphOfEdges input) x stored)
    (hprogress : HopProgress input stored (Parameters.hopBound n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) i) :
    (Builder.evaluate (Backend.guardedHandler input)
      (stages hn accuracy x ha (guesses n wmin wmax hwmin) trials count stored)).prob (fun out =>
        ¬ HopProgress input out (Parameters.hopBound n accuracy x)
          (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) (i + count)) ≤
      (count : ℝ) * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ trials := by
  let G := StoredEdges.graphOfEdges input
  let deltas := guesses n wmin wmax hwmin
  let h := Parameters.hopBound n accuracy x
  let stretch : ℝ := 1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)
  let err := (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ trials
  have herr : 0 ≤ err := by dsimp only [err]; positivity
  have hinput : Implicit.Noncontracting G G := fun u v => Graph.dist_le_edge G u v
  have hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v := by
    intro u v huv
    have hpos : 0 < wmin * Parameters.queryUnit n accuracy x :=
      Nat.mul_pos hwmin (Parameters.queryUnit_pos n accuracy x ha)
    exact (WithTop.coe_le_coe.mpr hpos).trans (hmin u v huv)
  induction count generalizing i stored with
  | zero =>
      simp only [stages, Builder.evaluate, Law.prob, Law.expect_pure, Nat.add_zero, hprogress,
        not_true_eq_false, ↓reduceIte, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
      let mu := Builder.evaluate (Backend.guardedHandler input)
        (repeatTrials hn accuracy x ha deltas stored trials stored)
      let goodStage := fun next => StageQuality stored next input h
        (wmin * Parameters.queryUnit n accuracy x) (2 * n * wmax * Parameters.queryUnit n accuracy x) stretch
      have hvalid := Builder.checked_evaluate input _
        (StoredValid G x) (repeatTrials_valid G hn accuracy x ha input hp hinput hG stored hs deltas trials stored hs)
      have hext := Builder.ensures_evaluate (Backend.guardedHandler input) _ _
        (repeatTrials_extends hn accuracy x ha deltas stored trials stored)
      have hboth : Early.Sampling.Holds mu (fun next => StoredValid G x next ∧ next.Extends stored) :=
        fun z hz => ⟨hvalid z hz, hext z hz⟩
      have hbad : mu.prob (fun next => ¬ goodStage next) ≤ err :=
        stage_quality_failure hn hn₂ accuracy x wmin wmax ha hwmin stored input hs.positive hp hs.blocks hpoly
          trials stored (.refl stored)
      rw [stages, Builder.prob_bind]
      have hmean : mu.expect (fun next =>
          (Builder.evaluate (Backend.guardedHandler input) (stages hn accuracy x ha deltas trials count next)).prob (fun out =>
            ¬ HopProgress input out h stretch (i + (count + 1)))) ≤
          mu.expect (fun next => (count : ℝ) * err + if ¬ goodStage next then 1 else 0) := by
        apply Early.Sampling.expect_mono_on
        refine Early.Sampling.holds_mono hboth ?_
        intro next hnext
        by_cases hquality : goodStage next
        · have hprogNext := calibrated_progress_step accuracy x wmin wmax ha input stored next i (by omega)
            hmin hmax hs.sound hprogress hquality
          have hf := ih (i + 1) (by omega) next hnext.1 hprogNext
          have heq : i + 1 + count = i + (count + 1) := by omega
          rw [ite_eq_right (not_not_intro hquality), add_zero]
          simpa only [heq, err, h, stretch, deltas, mul_assoc] using hf
        · rw [ite_eq_left hquality]
          exact (Law.prob_le_one _ _).trans
            (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg count : (0 : ℝ) ≤ count) herr))
      have heq : mu.expect (fun next => (count : ℝ) * err + if ¬ goodStage next then 1 else 0) =
          (count : ℝ) * err + mu.prob (fun next => ¬ goodStage next) := by
        rw [Law.expect_add, Law.expect_const, Law.expect_indicator]
      calc
        _ ≤ mu.expect (fun next => (count : ℝ) * err + if ¬ goodStage next then 1 else 0) := hmean
        _ = (count : ℝ) * err + mu.prob (fun next => ¬ goodStage next) := heq
        _ ≤ (count : ℝ) * err + err := add_le_add le_rfl hbad
        _ = _ := by dsimp only [err]; push_cast; ring

end

end StreamingReachability.Hopset
