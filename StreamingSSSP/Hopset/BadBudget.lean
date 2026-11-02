module

public import StreamingSSSP.Hopset.BallBirth

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

theorem root_balls_good (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (S : Finset (Fin n)) :
    BallsGood cfg stored input 0 S := by
  have hcard (A : Finset (Fin n)) : A.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ A)
  intro v hv
  constructor <;> exact (hcard _).trans (by simp [Parameters.ballSize]; omega)

def badMetric (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) : Metric n cfg :=
  fun r S _ranks choice => if v ∈ S ∧ BadBirth cfg stored input r S choice then 1 else 0

def badVisitBudget (n : ℕ) : ℝ := 2 * (n : ℝ) ^ 2 * Real.exp (-25 * Parameters.ell n)

theorem badVisitBudget_nonneg (n : ℕ) : 0 ≤ badVisitBudget n := by
  unfold badVisitBudget
  positivity

theorem badMetric_outside (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) (choice : Choice n cfg) (hv : v ∉ S) :
    badMetric cfg stored input v r S ranks choice = 0 := by simp [badMetric, hv]

theorem expected_stopped_bad_per_vertex (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (v : Fin n) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => metricPotential (Parameters.configuration n accuracy x delta blockVolume ha hd) hn
          stored input (badMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
          (Parameters.maximumLevel n + 1) 0 Finset.univ ranks) ≤
      badVisitBudget n * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  apply expected_calibrated_metric n hn accuracy x delta blockVolume ha hd stored input _ v
    (badVisitBudget n) (badVisitBudget_nonneg n) (badMetric_outside _ _ _ v)
  intro r S history hc hp hg hv
  rw [CopyHistory.moment]
  apply mul_le_mul_of_nonneg_left _ (CopyHistory.mass_nonneg _ _)
  change (CopyHistory.law ps history).expect (fun ranks =>
    (kernel cfg hn stored input ranks r S).expect
      (fun step => (badMetric cfg stored input v r S ranks step.value : ℝ))) ≤ badVisitBudget n
  have he (ranks : Fin n → ℕ) :
      (kernel cfg hn stored input ranks r S).expect
          (fun step => (badMetric cfg stored input v r S ranks step.value : ℝ)) =
        (kernel cfg hn stored input ranks r S).prob
          (fun step => BadBirth cfg stored input r S step.value) := by
    have hfn :
        (fun step : Branching.Step (Finset (Fin n)) (Choice n cfg) =>
          (badMetric cfg stored input v r S ranks step.value : ℝ)) =
          fun step => if BadBirth cfg stored input r S step.value then (1 : ℝ) else 0 := by
      funext step
      by_cases hb : BadBirth cfg stored input r S step.value <;> simp [badMetric, hv, hb]
    rw [hfn, Law.expect_indicator]
  simp_rw [he]
  rw [← Law.prob_bind]
  apply (calibrated_bad_birth_probability n hn accuracy x delta blockVolume ha hd stored input
    r S history hc hp hg).trans
  have hcard : (S.card : ℝ) ≤ n := by
    exact_mod_cast (show S.card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S))
  unfold badVisitBudget
  gcongr

theorem expected_stopped_bad_weight (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    ((Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).bind fun ranks =>
        Branching.runCost
          (stoppedKernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks)
          (fun r S step => ∑ v : Fin n,
            metricCharge (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input
              (badMetric (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input v)
              ranks r S step)
          (Parameters.maximumLevel n + 1) 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤
      4 * (n : ℝ) ^ 3 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) *
        Real.exp (-25 * Parameters.ell n) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let fuel := Parameters.maximumLevel n + 1
  change ((Law.family n (fun _ => Ranks.firstHit ps)).bind fun ranks =>
    Branching.runCost (stoppedKernel cfg hn stored input ranks)
      (fun r S step => ∑ v : Fin n,
        metricCharge cfg stored input (badMetric cfg stored input v) ranks r S step)
      fuel 0 [Finset.univ]).expect (fun count => (count : ℝ)) ≤ _
  rw [Law.expect_bind]
  simp_rw [Branching.expected_breadth_first_cost]
  simp only [List.map_singleton, List.sum_singleton]
  have hpotential (ranks : Fin n → ℕ) :
      Branching.potential (stoppedKernel cfg hn stored input ranks)
          (fun r S step => ∑ v : Fin n,
            metricCharge cfg stored input (badMetric cfg stored input v) ranks r S step)
          fuel 0 Finset.univ =
        ∑ v : Fin n, metricPotential cfg hn stored input (badMetric cfg stored input v)
          fuel 0 Finset.univ ranks :=
    Branching.potential_sum _ Finset.univ
      (fun v => metricCharge cfg stored input (badMetric cfg stored input v) ranks) fuel 0 Finset.univ
  simp_rw [hpotential]
  rw [Law.expect_finset_sum]
  calc
    _ ≤ ∑ _v : Fin n, badVisitBudget n * (2 * fuel) := by
      apply Finset.sum_le_sum
      intro v _
      exact expected_stopped_bad_per_vertex n hn accuracy x delta blockVolume ha hd stored input v
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, badVisitBudget, fuel]
      ring

theorem exp_negative_logarithm_bound (n : ℕ) (hn : 0 < n) :
    Real.exp (-25 * Parameters.ell n) ≤ 1 / (n : ℝ) ^ 25 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpower : (n : ℝ) ≤ Real.exp (Parameters.ell n : ℝ) := by
    calc
      (n : ℝ) ≤ (2 : ℝ) ^ Parameters.ell n := by
        exact_mod_cast (Parameters.lt_two_pow_ell n).le
      _ ≤ (Real.exp 1) ^ Parameters.ell n :=
        pow_le_pow_left₀ (by norm_num) htwo _
      _ = Real.exp (Parameters.ell n : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
  have he : Real.exp (25 * (Parameters.ell n : ℝ)) =
      (Real.exp (Parameters.ell n : ℝ)) ^ 25 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [show -25 * (Parameters.ell n : ℝ) = -(25 * (Parameters.ell n : ℝ)) by ring,
    Real.exp_neg, he]
  simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hnR 25)
    (pow_le_pow_left₀ hnR.le hpower 25)

theorem bad_weight_negligible (n : ℕ) (hn : 2 ≤ n) :
    4 * (n : ℝ) ^ 3 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) *
        Real.exp (-25 * Parameters.ell n) ≤ 1 / (n : ℝ) ^ 10 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlevels : Parameters.maximumLevel n + 1 ≤ 2 * n := by
    have h := Parameters.firstCross_le (100 * Parameters.k n * Parameters.ell n)
      (Parameters.k n) n n
    change Parameters.maximumLevel n ≤ n at h
    omega
  have h11 : (8 : ℝ) ≤ (n : ℝ) ^ 11 := by
    calc
      8 ≤ (2 : ℝ) ^ 11 := by norm_num
      _ ≤ (n : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hn2R _
  calc
    _ ≤ 4 * (n : ℝ) ^ 3 * (2 * n) * (1 / (n : ℝ) ^ 25) := by
      gcongr
      · exact_mod_cast hlevels
      · exact exp_negative_logarithm_bound n (by omega)
    _ = 8 / (n : ℝ) ^ 21 := by field_simp; ring
    _ ≤ 1 / (n : ℝ) ^ 10 := by
      apply (div_le_div_iff₀ (pow_pos hnR _) (pow_pos hnR _)).mpr
      calc
        8 * (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 11 * (n : ℝ) ^ 10 :=
          mul_le_mul_of_nonneg_right h11 (pow_nonneg hnR.le _)
        _ = 1 * (n : ℝ) ^ 21 := by ring

end

end StreamingSSSP.Hopset.Reference
