module

public import StreamingReachability.Hopset.PathRoot

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

theorem piece_zero_envelope (C b ell z : ℝ) (hC : 1 ≤ C) (hb : 1 ≤ b) (he : 1 ≤ ell)
    (hz : z ≤ 4 * C) : z ≤ pieceEnvelope C b ell 0 := by
  have hbell : 1 ≤ b * ell := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr he)]
  have hprod := mul_nonneg (show 0 ≤ C by linarith) (sub_nonneg.mpr hbell)
  simp only [pieceEnvelope, pow_zero, mul_one]
  nlinarith

theorem piece_one_envelope (C b ell z₀ z₁ : ℝ) (hC : 1 ≤ C) (hb : 1 ≤ b) (he : 1 ≤ ell)
    (hz₀ : z₀ ≤ 4 * C) (hz₁ : z₁ ≤ (2 + 800 * b ^ 2 * ell) * z₀ + 300 * C * b) :
    z₁ ≤ pieceEnvelope C b ell 1 := by
  have hbb : b ≤ b ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ b by linarith)]
  have hbell : b ^ 2 ≤ b ^ 2 * ell := by nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr he)]
  have hC0 : 0 ≤ C := by linarith
  have hc₁ := mul_nonneg hC0 (show 0 ≤ b ^ 2 * ell - 1 by linarith)
  have hc₂ := mul_nonneg hC0 (show 0 ≤ b ^ 2 * ell - b by linarith)
  have hm := mul_le_mul_of_nonneg_left hz₀ (show 0 ≤ 2 + 800 * b ^ 2 * ell by positivity)
  simp only [pieceEnvelope, pow_one]
  nlinarith

variable {n : ℕ}

theorem calibrated_mean_recurrence (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (root : State (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input 0)
    (hroot : weight delta root.paths ≤ 3 * Parameters.queryUnit n accuracy x)
    (r : ℕ) (hr : r + 2 ≤ Parameters.threshold n x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let ps := Reference.earlyRates n hn x
    let z := meanZ cfg ps (Parameters.initialNumerator_pos n accuracy x ha) stored input root
    z (r + 2) ≤ 2 * z (r + 1) + 36 * (Parameters.split n : ℝ) ^ 2 * z r +
      3 * Parameters.pathScale n accuracy * (100 * (Parameters.split n : ℝ)) ^ (r + 2) +
      2400 * (Parameters.split n : ℝ) ^ 2 * Parameters.ell n * Parameters.pathScale n accuracy *
        (100 * (Parameters.split n : ℝ)) ^ (r + 1) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := Reference.earlyRates n hn x
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let z := meanZ cfg ps hnum stored input root
  let C := Parameters.pathScale n accuracy
  let b : ℝ := Parameters.split n
  let ell : ℝ := Parameters.ell n
  let W := 3 * Parameters.queryUnit n accuracy x
  change z (r + 2) ≤ 2 * z (r + 1) + 36 * b ^ 2 * z r +
    3 * C * (100 * b) ^ (r + 2) + 2400 * b ^ 2 * ell * C * (100 * b) ^ (r + 1)
  have hstep := meanZ_recurrence cfg ps hnum stored input root W r hroot
    (calibrated_early_numerics n hn accuracy x delta blockVolume ha hd r (by omega))
    (calibrated_early_numerics n hn accuracy x delta blockVolume ha hd (r + 1) (by omega))
    (calibrated_rate_step n hn x r (by omega))
  have hk : (cfg.k : ℝ) = b ^ 2 := by
    simp only [cfg, Parameters.configuration, Config.k, b, Nat.cast_pow]
  have hell : (cfg.logarithm : ℝ) = ell := rfl
  rw [hk, hell] at hstep
  have hB₁ := Parameters.path_weight_div_scale n accuracy x delta blockVolume ha hd (r + 1) (by omega)
    (W : ℝ) (by simp only [W, Nat.cast_mul, Nat.cast_ofNat, le_refl])
  have hB₂ := Parameters.path_weight_div_scale n accuracy x delta blockVolume ha hd (r + 2) hr
    (W : ℝ) (by simp only [W, Nat.cast_mul, Nat.cast_ofNat, le_refl])
  have hmul := mul_le_mul_of_nonneg_left hB₁ (show 0 ≤ 800 * b ^ 2 * ell by positivity)
  change z (r + 2) ≤ 2 * z (r + 1) + 36 * b ^ 2 * z r +
    (W : ℝ) / Reference.distanceScale cfg (r + 2) +
    800 * b ^ 2 * ell * ((W : ℝ) / Reference.distanceScale cfg (r + 1)) at hstep
  change (W : ℝ) / Reference.distanceScale cfg (r + 2) ≤ 3 * C * (100 * b) ^ (r + 2) at hB₂
  change 800 * b ^ 2 * ell * ((W : ℝ) / Reference.distanceScale cfg (r + 1)) ≤
    800 * b ^ 2 * ell * (3 * C * (100 * b) ^ (r + 1)) at hmul
  linarith

theorem calibrated_piece_counts (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let ps := Reference.earlyRates n hn x
    let root := rootState cfg stored input Q
    ∀ r ≤ Parameters.threshold n x,
      meanZ cfg ps (Parameters.initialNumerator_pos n accuracy x ha) stored input root r ≤
        pieceEnvelope (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := Reference.earlyRates n hn x
  let root := rootState cfg stored input Q
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let z := meanZ cfg ps hnum stored input root
  let C := Parameters.pathScale n accuracy
  let b : ℝ := Parameters.split n
  let ell : ℝ := Parameters.ell n
  let W := 3 * Parameters.queryUnit n accuracy x
  have hC : 1 ≤ C := Parameters.pathScale_one_le n accuracy
  have hb : 1 ≤ b := by
    change (1 : ℝ) ≤ (Parameters.split n : ℝ)
    exact_mod_cast (show 1 ≤ Parameters.split n from Parameters.split_pos n)
  have he : 1 ≤ ell := by
    change (1 : ℝ) ≤ (Parameters.ell n : ℝ)
    exact_mod_cast (show 1 ≤ Parameters.ell n from Parameters.ell_pos n)
  have hroot : weight cfg.inputScale root.paths ≤ W := hweight
  have hB₀ := Parameters.path_weight_div_scale n accuracy x delta blockVolume ha hd 0 (Nat.zero_le _)
    (W : ℝ) (by simp only [W, Nat.cast_mul, Nat.cast_ofNat, le_refl])
  have hz₀ := root_meanZ_le cfg ps hnum stored input Q W hweight
  have hz₀' : z 0 ≤ 4 * C := by
    change (W : ℝ) / Reference.distanceScale cfg 0 ≤ 3 * C * (100 * b) ^ 0 at hB₀
    change z 0 ≤ 1 + (W : ℝ) / Reference.distanceScale cfg 0 at hz₀
    simp only [pow_zero, mul_one] at hB₀
    linarith
  change ∀ r ≤ Parameters.threshold n x, z r ≤ pieceEnvelope C b ell r
  apply second_order_piece_bound z C b ell (by linarith) hb he (Parameters.threshold n x)
  · exact piece_zero_envelope C b ell (z 0) hC hb he hz₀'
  · intro hlevel
    have hnumer := calibrated_early_numerics n hn accuracy x delta blockVolume ha hd 0 (by omega)
    have hz₁ := root_meanZ_one cfg ps hnum stored input hn Q W hweight hnumer
    have hB₁ := Parameters.path_weight_div_scale n accuracy x delta blockVolume ha hd 1 hlevel
      (W : ℝ) (by simp only [W, Nat.cast_mul, Nat.cast_ofNat, le_refl])
    have hk : (cfg.k : ℝ) = b ^ 2 := by
      simp only [cfg, Parameters.configuration, Config.k, b, Nat.cast_pow]
    have hell : (cfg.logarithm : ℝ) = ell := rfl
    rw [hk, hell] at hz₁
    have hinit : z 1 ≤ (2 + 800 * b ^ 2 * ell) * z 0 + 300 * C * b := by
      change z 1 ≤ (2 + 800 * b ^ 2 * ell) * z 0 +
        (W : ℝ) / Reference.distanceScale cfg 1 at hz₁
      change (W : ℝ) / Reference.distanceScale cfg 1 ≤ 3 * C * (100 * b) ^ 1 at hB₁
      simp only [pow_one] at hB₁
      linarith
    exact piece_one_envelope C b ell (z 0) (z 1) hC hb he hz₀' hinit
  · intro r hr
    exact calibrated_mean_recurrence hn accuracy x delta blockVolume ha hd stored input root hroot r hr

end

end StreamingReachability.Hopset.Following
