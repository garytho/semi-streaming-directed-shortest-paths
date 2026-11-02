module

public import StreamingReachability.Hopset.FrozenTrial

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem repeatTrials_failure (handler : Code.Handler n) (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (frozen : Implicit.Representation n) (deltas : List {delta : ℕ // 0 < delta})
    (good : Implicit.Representation n → Prop)
    (hmono : ∀ {new old : Implicit.Representation n}, new.Extends old → good old → good new)
    (hstep : ∀ committed : Implicit.Representation n, committed.Extends frozen →
      (1 / 2 : ℝ) ≤
        (Builder.evaluate handler (executeGuesses hn accuracy x ha frozen deltas committed)).prob good)
    (count : ℕ) (committed : Implicit.Representation n) (hcommitted : committed.Extends frozen) :
    (Builder.evaluate handler (repeatTrials hn accuracy x ha deltas frozen count committed)).prob
      (fun out => ¬ good out) ≤ (1 / 2 : ℝ) ^ count := by
  have hclaim (count : ℕ) (committed : Implicit.Representation n) (hc : committed.Extends frozen) :
      (Builder.evaluate handler (repeatTrials hn accuracy x ha deltas frozen count committed)).prob
        (fun out => ¬ good out) ≤ if good committed then 0 else (1 / 2 : ℝ) ^ count := by
    induction count generalizing committed with
    | zero =>
        by_cases hg : good committed <;>
          simp only [repeatTrials, Builder.evaluate, Law.prob, Law.expect_pure, hg, not_true_eq_false,
            not_false_eq_true, ↓reduceIte, pow_zero, le_refl]
    | succ count ih =>
        by_cases hg : good committed
        · have hext := Builder.ensures_evaluate handler _ _
            (repeatTrials_extends hn accuracy x ha deltas frozen (count + 1) committed)
          have hgood := Early.Sampling.holds_mono hext (fun out ho => hmono ho hg)
          have hp := Following.probability_of_holds _ good hgood
          have hcomp := (Builder.evaluate handler
            (repeatTrials hn accuracy x ha deltas frozen (count + 1) committed)).prob_compl good
          rw [ite_eq_left hg]
          linarith
        · rw [ite_eq_right hg, repeatTrials, Builder.prob_bind]
          let mu := Builder.evaluate handler (executeGuesses hn accuracy x ha frozen deltas committed)
          have hext := Builder.ensures_evaluate handler _ _
            (executeGuesses_extends hn accuracy x ha frozen deltas committed)
          have hmean : mu.expect (fun next =>
              (Builder.evaluate handler (repeatTrials hn accuracy x ha deltas frozen count next)).prob (fun out => ¬ good out)) ≤
              mu.expect (fun next => if good next then 0 else (1 / 2 : ℝ) ^ count) := by
            apply Early.Sampling.expect_mono_on
            exact Early.Sampling.holds_mono hext (fun next hn => ih next (hn.trans hc))
          have hbad : mu.prob (fun next => ¬ good next) ≤ 1 / 2 := by
            have hp : (1 / 2 : ℝ) ≤ mu.prob good := hstep committed hc
            have hcomp := mu.prob_compl good
            linarith
          have heq : mu.expect (fun next => if good next then 0 else (1 / 2 : ℝ) ^ count) =
              (1 / 2 : ℝ) ^ count * mu.prob (fun next => ¬ good next) := by
            have hf : (fun next => if good next then (0 : ℝ) else (1 / 2 : ℝ) ^ count) =
                fun next => if ¬ good next then (1 / 2 : ℝ) ^ count else 0 := by
              funext next
              by_cases hg : good next <;> simp only [hg, not_true_eq_false, not_false_eq_true, ↓reduceIte]
            rw [hf, Law.expect_ite_const]
          calc
            _ ≤ mu.expect (fun next => if good next then 0 else (1 / 2 : ℝ) ^ count) := hmean
            _ = (1 / 2 : ℝ) ^ count * mu.prob (fun next => ¬ good next) := heq
            _ ≤ (1 / 2 : ℝ) ^ count * (1 / 2) := mul_le_mul_of_nonneg_left hbad (by positivity)
            _ = _ := (pow_succ _ _).symm
  exact (hclaim count committed hcommitted).trans (by split_ifs <;> first | positivity | exact le_rfl)

theorem repeatTrials_shortens_failure (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (frozen : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path frozen (StoredEdges.graphOfEdges input) s t)
    (hlength : Q.length ≤ 2 * Parameters.hopBound n accuracy x)
    (hlower : wmin * Parameters.queryUnit n accuracy x ≤ Q.micro)
    (hupper : Q.micro ≤ 2 * n * wmax * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ frozen.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ frozen.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (count : ℕ) (committed : Implicit.Representation n) (hcommitted : committed.Extends frozen) :
    (Builder.evaluate (Backend.guardedHandler input)
      (repeatTrials hn accuracy x ha (guesses n wmin wmax hwmin) frozen count committed)).prob (fun out =>
        ¬ ShortRoute (out.graph (StoredEdges.graphOfEdges input)) s t (Parameters.hopBound n accuracy x)
          ((1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) * Q.micro)) ≤ (1 / 2 : ℝ) ^ count := by
  apply repeatTrials_failure (Backend.guardedHandler input) hn accuracy x ha frozen _ _ _ _ count committed hcommitted
  · intro new old he hg
    exact hg.extends _ he
  · intro committed hc
    exact executeGuesses_shortens hn hn₂ accuracy x wmin wmax ha hwmin frozen input Q hlength hlower hupper
      hs hp hsize hpoly committed hc

end

end StreamingReachability.Hopset
