module

public import StreamingReachability.Hopset.Confidence

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

def IsImplicitHopset (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n)
    (hops : ℕ) (stretch : ℝ) : Prop :=
  stored.Sound (StoredEdges.graphOfEdges input) ∧
    ∀ s t (d : ℕ), (StoredEdges.graphOfEdges input).dist s t = (d : Distance) →
      ∃ e : ℕ, (stored.graph (StoredEdges.graphOfEdges input)).hopDist hops s t = (e : Distance) ∧
        d ≤ e ∧ (e : ℝ) ≤ stretch * d

theorem construct_progress_failure (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hmin : ∀ u v, u ≠ v → ((wmin * Parameters.queryUnit n accuracy x : ℕ) : Distance) ≤
      StoredEdges.graphOfEdges input u v)
    (hmax : Exact.WeightsBounded (StoredEdges.graphOfEdges input) (wmax * Parameters.queryUnit n accuracy x))
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (initial : Implicit.Representation n) (hs : StoredValid (StoredEdges.graphOfEdges input) x initial) :
    (Builder.evaluate (Backend.guardedHandler input)
      (construct hn accuracy x confidence wmin wmax ha hwmin initial)).prob (fun out =>
        ¬ HopProgress input out (Parameters.hopBound n accuracy x)
          (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) (Parameters.ell n)) ≤ 1 / (n : ℝ) ^ confidence := by
  have hprogress := hopProgress_zero input initial (Parameters.hopBound n accuracy x)
    (Parameters.hopBound_pos n accuracy x) (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) hs.sound
  have h := stages_progress_failure hn hn₂ accuracy x wmin wmax ha hwmin input hp hmin hmax hpoly
    ((confidence + 16) * Parameters.ell n) (Parameters.ell n) 0 (by omega) initial hs hprogress
  simp only [Nat.zero_add] at h
  exact h.trans (Parameters.confidence_failure_budget n confidence hn)

theorem construct_implicit_hopset (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hmin : ∀ u v, u ≠ v → ((wmin * Parameters.queryUnit n accuracy x : ℕ) : Distance) ≤
      StoredEdges.graphOfEdges input u v)
    (hmax : Exact.WeightsBounded (StoredEdges.graphOfEdges input) (wmax * Parameters.queryUnit n accuracy x))
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (initial : Implicit.Representation n) (hs : StoredValid (StoredEdges.graphOfEdges input) x initial) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Builder.evaluate (Backend.guardedHandler input)
        (construct hn accuracy x confidence wmin wmax ha hwmin initial)).prob (fun out =>
          StoredValid (StoredEdges.graphOfEdges input) x out ∧
            IsImplicitHopset input out (Parameters.hopBound n accuracy x) (1 + 1 / (5 * (accuracy : ℝ)))) := by
  let mu := Builder.evaluate (Backend.guardedHandler input)
    (construct hn accuracy x confidence wmin wmax ha hwmin initial)
  let progress := fun out => HopProgress input out (Parameters.hopBound n accuracy x)
    (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) (Parameters.ell n)
  have hbad : mu.prob (fun out => ¬ progress out) ≤ 1 / (n : ℝ) ^ confidence :=
    construct_progress_failure hn hn₂ accuracy x confidence wmin wmax ha hwmin input hp hmin hmax hpoly initial hs
  have hcomp := mu.prob_compl progress
  have hpos : 0 < wmin * Parameters.queryUnit n accuracy x :=
    Nat.mul_pos hwmin (Parameters.queryUnit_pos n accuracy x ha)
  have hG : ∀ u v, u ≠ v → (1 : Distance) ≤ StoredEdges.graphOfEdges input u v :=
    fun u v huv => (WithTop.coe_le_coe.mpr hpos).trans (hmin u v huv)
  have hinput : Implicit.Noncontracting (StoredEdges.graphOfEdges input) (StoredEdges.graphOfEdges input) :=
    fun u v => Graph.dist_le_edge _ u v
  have hvalid : Early.Sampling.Holds mu (StoredValid (StoredEdges.graphOfEdges input) x) :=
    Builder.checked_evaluate input _
      (StoredValid (StoredEdges.graphOfEdges input) x)
      (stages_valid _ hn accuracy x ha input hp hinput hG _ _ _ initial hs)
  have hm : mu.prob progress ≤ mu.prob (fun out =>
      StoredValid (StoredEdges.graphOfEdges input) x out ∧
        IsImplicitHopset input out (Parameters.hopBound n accuracy x) (1 + 1 / (5 * (accuracy : ℝ)))) := by
    apply Batched.prob_mono_supported
    refine Early.Sampling.holds_mono hvalid ?_
    intro out ho hp
    exact ⟨ho, ho.sound, hopProgress_final hn accuracy x ha input out ho.sound hp⟩
  change 1 - 1 / (n : ℝ) ^ confidence ≤ mu.prob _
  linarith

end

end StreamingReachability.Hopset
