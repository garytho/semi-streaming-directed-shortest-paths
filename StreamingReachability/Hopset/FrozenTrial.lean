module

public import StreamingReachability.Hopset.BuilderFacts

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

theorem executeGuesses_hit (handler : Code.Handler n) (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (frozen : Implicit.Representation n) (deltas : List {delta : ℕ // 0 < delta})
    (delta : {delta : ℕ // 0 < delta}) (hdelta : delta ∈ deltas)
    (good : Implicit.Representation n → Prop)
    (hmono : ∀ {new old : Implicit.Representation n}, new.Extends old → good old → good new)
    (bound : ℝ)
    (htrial : bound ≤
      (Code.evaluate handler (fixedGuess
        (Parameters.configuration n accuracy x delta.val (volume frozen.blocks) ha delta.property) hn frozen)).prob
          (OutputSatisfies (fun out => good (commit frozen out))))
    (committed : Implicit.Representation n) (hcommitted : committed.Extends frozen) :
    bound ≤ (Builder.evaluate handler (executeGuesses hn accuracy x ha frozen deltas committed)).prob good := by
  induction deltas generalizing committed with
  | nil => simp only [List.not_mem_nil] at hdelta
  | cons first deltas ih =>
      let cfg := Parameters.configuration n accuracy x first.val (volume frozen.blocks) ha first.property
      let mu := Code.evaluate handler (fixedGuess cfg hn frozen)
      rw [executeGuesses, Builder.evaluate, Law.prob_bind]
      rcases List.mem_cons.mp hdelta with hfirst | hrest
      · subst first
        calc
          _ ≤ mu.prob (OutputSatisfies (fun out => good (commit frozen out))) := htrial
          _ ≤ _ := by
            unfold Law.prob
            apply Law.expect_mono
            intro result
            by_cases hg : OutputSatisfies (fun out => good (commit frozen out)) result
            · cases result with
              | none => exact False.elim hg
              | some out =>
                  have hcurrent : good (commit committed out) := hmono (commit_extends_commit hcommitted out) hg
                  have hfuture := Builder.ensures_evaluate handler _ _
                    (executeGuesses_extends hn accuracy x ha frozen deltas (commit committed out))
                  have hgood := Early.Sampling.holds_mono hfuture (fun result hr => hmono hr hcurrent)
                  have he := Following.probability_of_holds _ good hgood
                  rw [ite_eq_left hg]
                  exact he.ge
            · rw [ite_eq_right hg]
              exact Law.prob_nonneg _ _
      · calc
          _ = mu.expect (fun _ => bound) := (Law.expect_const _ _).symm
          _ ≤ _ := by
            apply Law.expect_mono
            intro result
            apply ih hrest
            cases result with
            | none => exact hcommitted
            | some out => exact (commit_extends committed out).trans hcommitted

theorem executeGuesses_shortens (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (frozen : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path frozen (StoredEdges.graphOfEdges input) s t)
    (hlength : Q.length ≤ 2 * Parameters.hopBound n accuracy x)
    (hlower : wmin * Parameters.queryUnit n accuracy x ≤ Q.micro)
    (hupper : Q.micro ≤ 2 * n * wmax * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ frozen.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ frozen.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (committed : Implicit.Representation n) (hcommitted : committed.Extends frozen) :
    (1 / 2 : ℝ) ≤
      (Builder.evaluate (Backend.guardedHandler input)
        (executeGuesses hn accuracy x ha frozen (guesses n wmin wmax hwmin) committed)).prob (fun out =>
          ShortRoute (out.graph (StoredEdges.graphOfEdges input)) s t (Parameters.hopBound n accuracy x)
            ((1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) * Q.micro)) := by
  obtain ⟨delta, hdelta, hlo, hhi⟩ := guesses_cover_scaled n wmin wmax (Parameters.queryUnit n accuracy x)
    Q.micro hwmin (Parameters.queryUnit_pos n accuracy x ha) hlower hupper
  apply executeGuesses_hit (Backend.guardedHandler input) hn accuracy x ha frozen _ delta hdelta _ _ (1 / 2)
    (fixedGuess_relative hn hn₂ accuracy x delta.val ha delta.property frozen input Q hlength hlo hhi hs hp hsize hpoly)
    committed hcommitted
  intro new old he hg
  exact hg.extends _ he

end

end StreamingReachability.Hopset
