module

public import StreamingReachability.Hopset.Stopped
public import StreamingReachability.Hopset.Growth

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def copyBudget (growth : ℝ) (fuel : ℕ) : ℝ := (fuel : ℝ) * (1 + growth) ^ fuel

theorem copyBudget_nonneg (growth : ℝ) (hg : 0 ≤ growth) (fuel : ℕ) :
    0 ≤ copyBudget growth fuel := by
  unfold copyBudget
  positivity

theorem stopped_copy_moment (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (ps : List Rate) (growth : ℝ) (hgrowth : 0 ≤ growth)
    (hprefix : ∀ r < cfg.earlyLevel, r < ps.length ∧
      ((ps.take r).map Rate.value).sum ≤ 1 / 2 ∧
        8 * (Parameters.ballSize n r : ℝ) * (Ranks.rate ps r).value / cfg.groups ≤ growth)
    (v : Fin n) (fuel r : ℕ) (S : Finset (Fin n))
    (history : List (CopyHistory.Observation n))
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r) :
    futureMoment ps history
        (fun T ranks => copyPotential cfg hn stored input v fuel r T ranks) S ≤
      CopyHistory.mass ps history * copyBudget growth fuel * if v ∈ S then 1 else 0 := by
  induction fuel generalizing r S history with
  | zero =>
      have hz := CopyHistory.moment ps history (fun _ => 0)
      simp only [Law.expect_const, mul_zero] at hz
      simpa only [futureMoment, copyPotential_zero, copyBudget, Nat.cast_zero, zero_mul, mul_zero]
        using hz.le
  | succ fuel ih =>
      let B := copyBudget growth fuel
      have hB : 0 ≤ B := copyBudget_nonneg growth hgrowth fuel
      have hfuture : ∀ hist T, CopyHistory.compatible hist T →
          CopyHistory.past hist (r + 1) →
            futureMoment ps hist
                (fun T ranks => copyPotential cfg hn stored input v fuel (r + 1) T ranks) T ≤
              CopyHistory.mass ps hist * B * if v ∈ T then 1 else 0 := by
        intro hist T hcomp hpast
        exact ih (r + 1) T hist hcomp hpast
      have hm : 0 ≤ CopyHistory.mass ps history := CopyHistory.mass_nonneg ps history
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte, mul_one]
        by_cases hballs : BallsGood cfg stored input r S
        · have hkernel := kernel_future_bound ps history cfg hn stored input hnum r S v
            (Parameters.ballSize n r) B growth hB hgrowth hc hp (hprefix r)
            (hballs v hv).1 (hballs v hv).2
            (fun T ranks => copyPotential cfg hn stored input v fuel (r + 1) T ranks) hfuture
          have hfn :
              (fun ranks : Fin n → ℕ => copyPotential cfg hn stored input v (fuel + 1) r S ranks) =
                fun ranks => (1 : ℝ) +
                  (kernel cfg hn stored input ranks r S).expect (fun step =>
                    (step.children.map fun T =>
                      copyPotential cfg hn stored input v fuel (r + 1) T ranks).sum) := by
            funext ranks
            rw [copyPotential_succ]
            simp only [hballs, hv, ↓reduceIte]
          dsimp only [futureMoment]
          rw [hfn, Law.expect_mask_add]
          have hconstant := CopyHistory.moment ps history (fun _ => 1)
          simp only [Law.expect_const, mul_one] at hconstant
          rw [hconstant]
          calc
            _ ≤ CopyHistory.mass ps history + CopyHistory.mass ps history * B * (1 + growth) :=
              add_le_add le_rfl hkernel
            _ = CopyHistory.mass ps history * (1 + B * (1 + growth)) := by ring
            _ ≤ CopyHistory.mass ps history * copyBudget growth (fuel + 1) :=
              mul_le_mul_of_nonneg_left (cumulative_growth_step growth hgrowth fuel) hm
        · have hfn :
              (fun ranks : Fin n → ℕ => copyPotential cfg hn stored input v (fuel + 1) r S ranks) =
                fun _ => 0 := by
            funext ranks
            rw [copyPotential_succ]
            simp only [hballs, ↓reduceIte]
          dsimp only [futureMoment]
          rw [hfn]
          have hz := CopyHistory.moment ps history (fun _ => 0)
          simp only [Law.expect_const, mul_zero] at hz
          rw [hz]
          exact mul_nonneg hm (copyBudget_nonneg growth hgrowth _)
      · simp only [hv, ↓reduceIte, mul_zero]
        have hfn :
            (fun ranks : Fin n → ℕ => copyPotential cfg hn stored input v (fuel + 1) r S ranks) =
              fun _ => 0 := by
          funext ranks
          exact copyPotential_outside cfg hn stored input v _ r S hv ranks
        dsimp only [futureMoment]
        rw [hfn]
        have hz := CopyHistory.moment ps history (fun _ => 0)
        simp only [Law.expect_const, mul_zero] at hz
        exact hz.le

def growthBound (n : ℕ) : ℝ := 2 / (100 * Parameters.ell n)

theorem growthBound_nonneg (n : ℕ) : 0 ≤ growthBound n := by
  unfold growthBound
  positivity

theorem copyBudget_le_twice (n fuel : ℕ) (hf : fuel ≤ Parameters.ell n + 1) :
    copyBudget (growthBound n) fuel ≤ 2 * fuel := by
  have he : (0 : ℝ) < Parameters.ell n := by exact_mod_cast Parameters.ell_pos n
  have he1 : (1 : ℝ) ≤ Parameters.ell n := by exact_mod_cast Parameters.ell_pos n
  have hfR : (fuel : ℝ) ≤ Parameters.ell n + 1 := by exact_mod_cast hf
  have hsmall : (fuel : ℝ) * growthBound n ≤ 1 / 2 := by
    unfold growthBound
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have h := power_le_two (growthBound n) (growthBound_nonneg n) fuel hsmall
  exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg fuel)).trans_eq (mul_comm _ _)

def earlyRates (n : ℕ) (hn : 0 < n) (x : ℕ) : List Rate :=
  PivotProfile.rates n hn (Parameters.k n) (Parameters.ell n) (Parameters.threshold n x)

theorem calibrated_prefix_budget (n : ℕ) (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) :
    ∀ r < (Parameters.configuration n accuracy x delta blockVolume ha hd).earlyLevel,
      r < (earlyRates n hn x).length ∧
        (((earlyRates n hn x).take r).map Rate.value).sum ≤ 1 / 2 ∧
          8 * (Parameters.ballSize n r : ℝ) * (Ranks.rate (earlyRates n hn x) r).value /
            (Parameters.configuration n accuracy x delta blockVolume ha hd).groups ≤ growthBound n := by
  intro r hr
  have hr' : r < Parameters.threshold n x := hr
  refine ⟨?_, ?_, ?_⟩
  · simpa only [earlyRates, PivotProfile.length_rates] using hr'
  · exact Parameters.early_prefix_half n hn x r hr'
  · change 8 * (Parameters.ballSize n r : ℝ) *
      (Ranks.rate (earlyRates n hn x) r).value / Parameters.groups n ≤ growthBound n
    rw [earlyRates, PivotProfile.lookup n hn (Parameters.k n) (Parameters.ell n)
      (Parameters.threshold n x) r hr']
    exact Parameters.copy_growth_budget n hn r

theorem calibrated_copy_moment (n : ℕ) (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (fuel r : ℕ) (S : Finset (Fin n))
    (history : List (CopyHistory.Observation n))
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r) :
    futureMoment (earlyRates n hn x) history
        (fun T ranks => copyPotential
          (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input v fuel r T ranks) S ≤
      CopyHistory.mass (earlyRates n hn x) history * copyBudget (growthBound n) fuel *
        if v ∈ S then 1 else 0 := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  exact stopped_copy_moment cfg hn stored input hnum (earlyRates n hn x) (growthBound n)
    (growthBound_nonneg n) (calibrated_prefix_budget n hn accuracy x delta blockVolume ha hd)
    v fuel r S history hc hp

theorem expected_stopped_copies_per_vertex (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (v : Fin n) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => copyPotential
          (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input v
          (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) ≤
      2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let fuel := Parameters.maximumLevel n + 1
  let f := fun T ranks => copyPotential cfg hn stored input v fuel 0 T ranks
  have h := calibrated_copy_moment n hn accuracy x delta blockVolume ha hd stored input v
    fuel 0 Finset.univ [] (by simp [CopyHistory.compatible]) (by simp [CopyHistory.past])
  have hmass : CopyHistory.mass (n := n) ps [] = 1 := by
    simp [CopyHistory.mass, CopyHistory.allowed, Law.prob]
  have hmask : Law.masked (CopyHistory.event []) (f Finset.univ) = f Finset.univ := by
    funext ranks
    simp [Law.masked, CopyHistory.event, CopyHistory.allowed]
  change futureMoment ps [] f Finset.univ ≤ _ at h
  dsimp only [futureMoment] at h
  rw [hmask, hmass, one_mul] at h
  simp only [Finset.mem_univ, ↓reduceIte, mul_one] at h
  exact h.trans (copyBudget_le_twice n fuel
    (by have := Parameters.maximumLevel_le_logarithm n; dsimp [fuel]; omega))

def volumeCharge (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n))
    (step : Branching.Step (Finset (Fin n)) (Choice n cfg)) : ℕ :=
  ∑ v : Fin n, copyCharge cfg stored input v r S step

theorem volumeCharge_eq (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n))
    (step : Branching.Step (Finset (Fin n)) (Choice n cfg)) :
    volumeCharge cfg stored input r S step =
      if BallsGood cfg stored input r S then S.card else 0 := by
  by_cases hg : BallsGood cfg stored input r S
  · simp only [volumeCharge, copyCharge, hg, true_and, ↓reduceIte]
    rw [Finset.sum_boole]
    have hs : (Finset.univ.filter fun v => v ∈ S) = S := by ext v; simp
    simp [hs]
  · simp only [volumeCharge, copyCharge, hg, false_and, ↓reduceIte, Finset.sum_const_zero]

theorem expected_stopped_copy_volume (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    ((Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).bind fun ranks =>
        Branching.runCost
          (stoppedKernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks)
          (volumeCharge (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input)
          (Parameters.maximumLevel n + 1) 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤
      2 * n * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let fuel := Parameters.maximumLevel n + 1
  change ((Law.family n (fun _ => Ranks.firstHit ps)).bind fun ranks =>
    Branching.runCost (stoppedKernel cfg hn stored input ranks) (volumeCharge cfg stored input)
      fuel 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤ _
  rw [Law.expect_bind]
  simp_rw [Branching.expected_breadth_first_cost]
  simp only [List.map_singleton, List.sum_singleton]
  have hpotential (ranks : Fin n → ℕ) :
      Branching.potential (stoppedKernel cfg hn stored input ranks) (volumeCharge cfg stored input)
          fuel 0 Finset.univ =
        ∑ v : Fin n, copyPotential cfg hn stored input v fuel 0 Finset.univ ranks :=
    Branching.potential_sum _ Finset.univ (fun v => copyCharge cfg stored input v) fuel 0 Finset.univ
  simp_rw [hpotential]
  rw [Law.expect_finset_sum]
  calc
    _ ≤ ∑ _v : Fin n, 2 * (fuel : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      exact expected_stopped_copies_per_vertex n hn accuracy x delta blockVolume ha hd stored input v
    _ = _ := by simp [fuel]; ring

end

end StreamingReachability.Hopset.Reference
