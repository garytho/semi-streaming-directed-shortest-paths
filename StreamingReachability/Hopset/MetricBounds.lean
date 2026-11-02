module

public import StreamingReachability.Hopset.StoppedBounds

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical

noncomputable section

variable {n : ℕ}

abbrev Metric (n : ℕ) (cfg : Config) :=
  ℕ → Finset (Fin n) → (Fin n → ℕ) → Choice n cfg → ℕ

def metricCharge (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (metric : Metric n cfg) (ranks : Fin n → ℕ)
    (r : ℕ) (S : Finset (Fin n)) (step : Branching.Step (Finset (Fin n)) (Choice n cfg)) : ℕ :=
  if BallsGood cfg stored input r S then metric r S ranks step.value else 0

def metricPotential (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (metric : Metric n cfg)
    (fuel r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ) : ℝ :=
  Branching.potential (stoppedKernel cfg hn stored input ranks)
    (metricCharge cfg stored input metric ranks) fuel r S

theorem metricPotential_nonneg (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (metric : Metric n cfg)
    (fuel r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ) :
    0 ≤ metricPotential cfg hn stored input metric fuel r S ranks :=
  Branching.potential_nonneg _ _ _ _ _

theorem metricPotential_succ (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (metric : Metric n cfg)
    (fuel r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ) :
    metricPotential cfg hn stored input metric (fuel + 1) r S ranks =
      if BallsGood cfg stored input r S then
        (kernel cfg hn stored input ranks r S).expect (fun step =>
          (metric r S ranks step.value : ℝ) +
            (step.children.map fun T =>
              metricPotential cfg hn stored input metric fuel (r + 1) T ranks).sum)
      else 0 := by
  by_cases hg : BallsGood cfg stored input r S
  · simp only [metricPotential, Branching.potential, stoppedKernel, metricCharge, hg, ↓reduceIte]
  · simp [metricPotential, Branching.potential, stoppedKernel, metricCharge, hg]

theorem metricPotential_outside (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (metric : Metric n cfg) (v : Fin n)
    (houtside : ∀ r S ranks choice, v ∉ S → metric r S ranks choice = 0)
    (fuel r : ℕ) (S : Finset (Fin n)) (hv : v ∉ S) (ranks : Fin n → ℕ) :
    metricPotential cfg hn stored input metric fuel r S ranks = 0 := by
  induction fuel generalizing r S with
  | zero => rfl
  | succ fuel ih =>
      rw [metricPotential_succ]
      by_cases hg : BallsGood cfg stored input r S
      · simp only [hg, ↓reduceIte, kernel, Law.expect_map]
        have he (choice : Choice n cfg) :
            (metric r S ranks choice : ℝ) +
              ((children cfg stored input r S choice).map fun T =>
                metricPotential cfg hn stored input metric fuel (r + 1) T ranks).sum = 0 := by
          rw [houtside r S ranks choice hv, Nat.cast_zero, zero_add]
          apply List.sum_eq_zero
          intro a ha
          obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
          apply ih (r + 1) T
          intro hvT
          exact hv (children_subset cfg stored input r S choice T hT hvT)
        simp only [he, Law.expect_const]
      · simp [hg]

theorem stopped_metric_moment (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (growth : ℝ) (hgrowth : 0 ≤ growth)
    (hprefix : ∀ r < cfg.earlyLevel, r < ps.length ∧
      ((ps.take r).map Rate.value).sum ≤ 1 / 2 ∧
        8 * (Parameters.ballSize n r : ℝ) * (Ranks.rate ps r).value / cfg.groups ≤ growth)
    (metric : Metric n cfg) (v : Fin n) (Q : ℝ) (hQ : 0 ≤ Q)
    (houtside : ∀ r S ranks choice, v ∉ S → metric r S ranks choice = 0)
    (hlocal : ∀ r S history, CopyHistory.compatible history S → CopyHistory.past history r →
      BallsGood cfg stored input r S → v ∈ S →
        (Law.family n (fun _ => Ranks.firstHit ps)).expect
            (Law.masked (CopyHistory.event history) (fun ranks =>
              (kernel cfg hn stored input ranks r S).expect
                (fun step => (metric r S ranks step.value : ℝ)))) ≤
          CopyHistory.mass ps history * Q)
    (fuel r : ℕ) (S : Finset (Fin n)) (history : List (CopyHistory.Observation n))
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r) :
    futureMoment ps history
        (fun T ranks => metricPotential cfg hn stored input metric fuel r T ranks) S ≤
      CopyHistory.mass ps history * Q * copyBudget growth fuel * if v ∈ S then 1 else 0 := by
  induction fuel generalizing r S history with
  | zero =>
      have hz := CopyHistory.moment ps history (fun _ => 0)
      simp only [Law.expect_const, mul_zero] at hz
      simpa only [futureMoment, metricPotential, Branching.potential, copyBudget,
        Nat.cast_zero, zero_mul, mul_zero] using hz.le
  | succ fuel ih =>
      let B := Q * copyBudget growth fuel
      have hB : 0 ≤ B := mul_nonneg hQ (copyBudget_nonneg growth hgrowth fuel)
      have hfuture : ∀ hist T, CopyHistory.compatible hist T →
          CopyHistory.past hist (r + 1) →
            futureMoment ps hist
                (fun T ranks => metricPotential cfg hn stored input metric fuel (r + 1) T ranks) T ≤
              CopyHistory.mass ps hist * B * if v ∈ T then 1 else 0 := by
        intro hist T hcomp hpast
        simpa only [B, mul_assoc] using ih (r + 1) T hist hcomp hpast
      have hm : 0 ≤ CopyHistory.mass ps history := CopyHistory.mass_nonneg ps history
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte, mul_one]
        by_cases hballs : BallsGood cfg stored input r S
        · have hkernel := kernel_future_bound ps history cfg hn stored input hnum r S v
            (Parameters.ballSize n r) B growth hB hgrowth hc hp (hprefix r)
            (hballs v hv).1 (hballs v hv).2
            (fun T ranks => metricPotential cfg hn stored input metric fuel (r + 1) T ranks) hfuture
          have hfn :
              (fun ranks : Fin n → ℕ => metricPotential cfg hn stored input metric (fuel + 1) r S ranks) =
                fun ranks =>
                  (kernel cfg hn stored input ranks r S).expect (fun step => (metric r S ranks step.value : ℝ)) +
                  (kernel cfg hn stored input ranks r S).expect (fun step =>
                    (step.children.map fun T =>
                      metricPotential cfg hn stored input metric fuel (r + 1) T ranks).sum) := by
            funext ranks
            rw [metricPotential_succ]
            simp only [hballs, ↓reduceIte, Law.expect_add]
          dsimp only [futureMoment]
          rw [hfn, Law.expect_mask_add]
          calc
            _ ≤ CopyHistory.mass ps history * Q +
                CopyHistory.mass ps history * B * (1 + growth) :=
              add_le_add (hlocal r S history hc hp hballs hv) hkernel
            _ = (CopyHistory.mass ps history * Q) *
                (1 + copyBudget growth fuel * (1 + growth)) := by dsimp [B]; ring
            _ ≤ CopyHistory.mass ps history * Q * copyBudget growth (fuel + 1) :=
              mul_le_mul_of_nonneg_left (cumulative_growth_step growth hgrowth fuel) (mul_nonneg hm hQ)
        · have hfn :
              (fun ranks : Fin n → ℕ => metricPotential cfg hn stored input metric (fuel + 1) r S ranks) =
                fun _ => 0 := by
            funext ranks
            rw [metricPotential_succ]
            simp only [hballs, ↓reduceIte]
          dsimp only [futureMoment]
          rw [hfn]
          have hz := CopyHistory.moment ps history (fun _ => 0)
          simp only [Law.expect_const, mul_zero] at hz
          rw [hz]
          exact mul_nonneg (mul_nonneg hm hQ) (copyBudget_nonneg growth hgrowth _)
      · simp only [hv, ↓reduceIte, mul_zero]
        have hfn :
            (fun ranks : Fin n → ℕ => metricPotential cfg hn stored input metric (fuel + 1) r S ranks) =
              fun _ => 0 := by
          funext ranks
          exact metricPotential_outside cfg hn stored input metric v houtside _ r S hv ranks
        dsimp only [futureMoment]
        rw [hfn]
        have hz := CopyHistory.moment ps history (fun _ => 0)
        simp only [Law.expect_const, mul_zero] at hz
        exact hz.le

theorem expected_calibrated_metric (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (metric : Metric n (Parameters.configuration n accuracy x delta blockVolume ha hd))
    (v : Fin n) (Q : ℝ) (hQ : 0 ≤ Q)
    (houtside : ∀ r S ranks choice, v ∉ S → metric r S ranks choice = 0)
    (hlocal : ∀ r S history, CopyHistory.compatible history S → CopyHistory.past history r →
      BallsGood (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input r S → v ∈ S →
        (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
            (Law.masked (CopyHistory.event history) (fun ranks =>
              (kernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks r S).expect
                (fun step => (metric r S ranks step.value : ℝ)))) ≤
          CopyHistory.mass (earlyRates n hn x) history * Q) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => metricPotential (Parameters.configuration n accuracy x delta blockVolume ha hd) hn
          stored input metric (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) ≤
      Q * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let fuel := Parameters.maximumLevel n + 1
  have h := stopped_metric_moment cfg hn stored input
    (Parameters.initialNumerator_pos n accuracy x ha) ps (growthBound n) (growthBound_nonneg n)
    (calibrated_prefix_budget n hn accuracy x delta blockVolume ha hd) metric v Q hQ
    houtside hlocal fuel 0 Finset.univ []
    (by simp [CopyHistory.compatible]) (by simp [CopyHistory.past])
  let f := fun T ranks => metricPotential cfg hn stored input metric fuel 0 T ranks
  have hmass : CopyHistory.mass (n := n) ps [] = 1 := by
    simp [CopyHistory.mass, CopyHistory.allowed, Law.prob]
  have hmask : Law.masked (CopyHistory.event []) (f Finset.univ) = f Finset.univ := by
    funext ranks
    simp [Law.masked, CopyHistory.event, CopyHistory.allowed]
  change futureMoment ps [] f Finset.univ ≤ _ at h
  dsimp only [futureMoment] at h
  rw [hmask, hmass, one_mul] at h
  simp only [Finset.mem_univ, ↓reduceIte, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (copyBudget_le_twice n fuel
      (by have := Parameters.maximumLevel_le_logarithm n; dsimp [fuel]; omega)) hQ)

end

end StreamingReachability.Hopset.Reference
