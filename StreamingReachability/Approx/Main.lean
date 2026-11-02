module

public import StreamingReachability.Approx.ExtractionCorrectness
public import StreamingReachability.Hopset.SmallCase

@[expose] public section

namespace StreamingReachability.Approx

open scoped Classical
open Hopset

noncomputable section

variable {n : ℕ}

theorem solve_admissible_accurate (hn : 0 < n) (accuracy x confidence : ℕ)
    (ha : 0 < accuracy) (source : Fin n) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hblock : Parameters.blockAdmissible n accuracy x) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Program.evaluate input (solve hn accuracy x confidence ha source)).prob (Accurate input source accuracy) := by
  let bounds := scan input
  let unit := Parameters.queryUnit n accuracy x
  have hb : bounds.Valid input := scan_valid input hp
  have hmin : 0 < bounds.minWeight := hb.minWeight_pos
  have hscan : scanViewed some input = bounds := by rw [scanViewed_eq, List.filterMap_some]
  let mu := Hopset.Builder.evaluate (Backend.guardedViewedHandler (microView unit) input)
    (Hopset.construct hn accuracy x confidence bounds.minWeight bounds.maximum ha hmin (emptyRepresentation n))
  let good := fun stored : Implicit.Representation n =>
    StoredValid (StoredEdges.graphOfEdges (input.filterMap (microView unit))) x stored ∧
      IsImplicitHopset (input.filterMap (microView unit)) stored (Parameters.hopBound n accuracy x)
        (1 + 1 / (5 * (accuracy : ℝ)))
  have hbuild : 1 - 1 / (n : ℝ) ^ confidence ≤ mu.prob good :=
    scaled_construct_admissible hn accuracy x confidence bounds.minWeight bounds.maximum ha hmin input hp
      hb.minWeight_le hb.upper hblock
  have houtput : mu.prob good ≤ mu.expect (fun stored =>
      (Program.evaluate input
        (extractGuesses accuracy x source stored (guesses n bounds.minWeight bounds.maximum hmin) (Vector.replicate n ⊤))).prob
          (Accurate input source accuracy)) := by
    change mu.expect (fun stored => @ite ℝ (good stored) (Classical.propDecidable _) 1 0) ≤ _
    apply mu.expect_mono
    intro stored
    by_cases hg : good stored
    · have hcorrect := extraction_correct hn accuracy x bounds.minWeight bounds.maximum ha hmin input stored source
        hp hg.1.positive hg.1.blocks hb.minWeight_le hb.upper hg.2
      have he := Hopset.Following.probability_of_holds _ (Accurate input source accuracy) hcorrect
      rw [ite_eq_left hg]
      exact he.ge
    · rw [ite_eq_right hg]
      exact Law.prob_nonneg _ _
  simp only [Program.evaluate, solve, Program.evaluateViewed, hscan, hmin, ↓reduceDIte, Law.prob_bind]
  exact hbuild.trans houtput

theorem solve_accurate (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x confidence : ℕ)
    (ha : 0 < accuracy) (source : Fin n) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Program.evaluate input (solve hn accuracy x confidence ha source)).prob (Accurate input source accuracy) :=
  solve_admissible_accurate hn accuracy x confidence ha source input hp (Or.inl ⟨hn₂, hpoly⟩)

theorem solve_cube_accurate (hn : 0 < n) (accuracy confidence : ℕ)
    (ha : 0 < accuracy) (source : Fin n) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Program.evaluate input (solve hn accuracy (Parameters.blockSize n) confidence ha source)).prob
        (Accurate input source accuracy) :=
  solve_admissible_accurate hn accuracy _ confidence ha source input hp (Parameters.cube_block_admissible n accuracy hn)

theorem solve_viewed_accurate {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x confidence : ℕ) (ha : 0 < accuracy) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view, 0 < e.weight)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Program.evaluateViewed view input (solve hn accuracy x confidence ha source)).prob
        (Accurate (input.filterMap view) source accuracy) := by
  rw [Program.evaluateViewed_eq]
  exact solve_accurate hn hn₂ accuracy x confidence ha source _ hp hpoly

theorem solve_cube_viewed_accurate {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (hn : 0 < n) (accuracy confidence : ℕ) (ha : 0 < accuracy) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view, 0 < e.weight) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Program.evaluateViewed view input (solve hn accuracy (Parameters.blockSize n) confidence ha source)).prob
        (Accurate (input.filterMap view) source accuracy) := by
  rw [Program.evaluateViewed_eq]
  exact solve_cube_accurate hn accuracy confidence ha source _ hp

end

end StreamingReachability.Approx
