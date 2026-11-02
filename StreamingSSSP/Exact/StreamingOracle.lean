module

public import StreamingSSSP.Exact.StreamingLevelView

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open DescriptorProgram

noncomputable section

variable {n : ℕ}

def safeAccuracy (denominator : ℕ) : ℕ := max 1 denominator

theorem safeAccuracy_pos (denominator : ℕ) : 0 < safeAccuracy denominator :=
  lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem sourcePositive (source : Fin n) : 0 < n :=
  lt_of_le_of_lt (Nat.zero_le source.val) source.isLt

def requestHandler (originalSource : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n)) :
    (request : Request n) → Law request.Reply
  | .base descriptor source denominator _ =>
      (Approx.Program.evaluateAuxiliary (baseView descriptor) input
        (baseAuxiliary descriptor originalSource (n ^ exponent))
        (Approx.solve (sourcePositive source) (safeAccuracy denominator) (Parameters.blockSize n) confidence
          (safeAccuracy_pos denominator) source)).map integerLabels
  | .level descriptor denominator _ =>
      (Approx.Program.evaluateAuxiliary (levelView descriptor) input
        (levelAuxiliary descriptor originalSource (n ^ exponent))
        (Approx.solve (Nat.succ_pos n) (safeAccuracy denominator) (Parameters.blockSize (n + 1)) confidence
          (safeAccuracy_pos denominator) (Fin.last n))).map integerLevelAnswer
  | .parents source weightBound distances =>
      Law.pure (Vector.ofFn (ParentPass.run source weightBound distances.get input))

def RequestAccurate (originalSource : Fin n) (exponent : ℕ) (input : List (StoredEdges.Edge n)) :
    (request : Request n) → request.Reply → Prop
  | .base descriptor source denominator _, reply =>
      IntegerApprox (descriptor.graph (preprocess (StoredEdges.graphOfEdges input) originalSource (n ^ exponent)))
        source denominator reply.get
  | .level descriptor denominator _, reply =>
      IntegerApprox (descriptor.graph (preprocess (StoredEdges.graphOfEdges input) originalSource (n ^ exponent)))
        none denominator reply.at
  | .parents source weightBound distances, reply =>
      reply = Vector.ofFn (ParentPass.run source weightBound distances.get input)

theorem requestHandler_accurate (originalSource : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (request : Request n) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (requestHandler originalSource exponent confidence input request).prob
        (RequestAccurate originalSource exponent input request) := by
  cases request with
  | base descriptor source denominator clock =>
      let edges := input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor originalSource (n ^ exponent)
      let mu := Approx.Program.evaluateAuxiliary (baseView descriptor) input
        (baseAuxiliary descriptor originalSource (n ^ exponent))
        (Approx.solve (sourcePositive source) (safeAccuracy denominator) (Parameters.blockSize n) confidence
          (safeAccuracy_pos denominator) source)
      have hgood : 1 - 1 / (n : ℝ) ^ confidence ≤ mu.prob (Approx.Accurate edges source (safeAccuracy denominator)) :=
        Approx.solve_auxiliary_accurate _ _ _ _ _ _ _ _ (base_input_positive descriptor originalSource (n ^ exponent) input)
      change 1 - 1 / (n : ℝ) ^ confidence ≤ (mu.map integerLabels).prob
        (fun reply : Labels n => IntegerApprox
          (descriptor.graph (preprocess (StoredEdges.graphOfEdges input) originalSource (n ^ exponent)))
          source denominator reply.get)
      rw [Law.prob_map]
      apply hgood.trans
      apply Law.prob_mono
      intro answer ha
      have h := integerLabels_accurate edges source denominator answer ha
      rw [show StoredEdges.graphOfEdges edges =
        descriptor.graph (preprocess (StoredEdges.graphOfEdges input) originalSource (n ^ exponent))
        from base_graph descriptor originalSource (n ^ exponent) input] at h
      exact h
  | level descriptor denominator clock =>
      let edges := input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor originalSource (n ^ exponent)
      let mu := Approx.Program.evaluateAuxiliary (levelView descriptor) input
        (levelAuxiliary descriptor originalSource (n ^ exponent))
        (Approx.solve (Nat.succ_pos n) (safeAccuracy denominator) (Parameters.blockSize (n + 1)) confidence
          (safeAccuracy_pos denominator) (Fin.last n))
      have hgood : 1 - 1 / ((n + 1 : ℕ) : ℝ) ^ confidence ≤
          mu.prob (Approx.Accurate edges (Fin.last n) (safeAccuracy denominator)) :=
        Approx.solve_auxiliary_accurate _ _ _ _ _ _ _ _ (level_input_positive descriptor originalSource (n ^ exponent) input)
      have hn : (0 : ℝ) < n := by exact_mod_cast sourcePositive originalSource
      have hp : (n : ℝ) ^ confidence ≤ ((n + 1 : ℕ) : ℝ) ^ confidence := by gcongr; omega
      have herror : 1 / ((n + 1 : ℕ) : ℝ) ^ confidence ≤ 1 / (n : ℝ) ^ confidence :=
        div_le_div_of_nonneg_left (by norm_num) (pow_pos hn confidence) hp
      change 1 - 1 / (n : ℝ) ^ confidence ≤ (mu.map integerLevelAnswer).prob
        (fun reply : LevelAnswer n => IntegerApprox
          (descriptor.graph (preprocess (StoredEdges.graphOfEdges input) originalSource (n ^ exponent)))
          none denominator reply.at)
      rw [Law.prob_map]
      apply (le_trans (by linarith) hgood).trans
      apply Law.prob_mono
      intro answer ha
      exact integerLevel_accurate edges _ denominator answer
        (level_graph descriptor originalSource (n ^ exponent) input) ha
  | parents source weightBound distances =>
      change 1 - 1 / (n : ℝ) ^ confidence ≤
        (Law.pure (Vector.ofFn (ParentPass.run source weightBound distances.get input))).prob
          (fun reply => reply = Vector.ofFn (ParentPass.run source weightBound distances.get input))
      simp only [Law.prob, Law.expect_pure, ↓reduceIte]
      have h : (0 : ℝ) ≤ 1 / (n : ℝ) ^ confidence := by positivity
      linarith

end

end StreamingSSSP.Exact.Implementation
