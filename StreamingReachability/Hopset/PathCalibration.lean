module

public import StreamingReachability.Hopset.ScaleSeparation
public import StreamingReachability.Hopset.StoppedBounds

@[expose] public section

namespace StreamingReachability

namespace PivotProfile

theorem rate_pos (n : ℕ) (hn : 0 < n) (k ell r : ℕ) (hk : 0 < k) (hell : 0 < ell) :
    0 < (rate n hn k ell r).value := by
  have hnum : 0 < min (100 * k ^ (r + 1) * ell) n := lt_min (by positivity) hn
  change 0 < ((min (100 * k ^ (r + 1) * ell) n : ℕ) : ℝ) / n
  exact div_pos (by exact_mod_cast hnum) (by exact_mod_cast hn)

theorem rate_succ_le (n : ℕ) (hn : 0 < n) (k ell r : ℕ) (hk : 1 ≤ k) :
    (rate n hn k ell (r + 1)).value ≤ (k : ℝ) * (rate n hn k ell r).value := by
  have hnum : min (100 * k ^ (r + 1 + 1) * ell) n ≤ k * min (100 * k ^ (r + 1) * ell) n := by
    by_cases h : 100 * k ^ (r + 1) * ell ≤ n
    · rw [Nat.min_eq_left h]
      apply (Nat.min_le_left _ _).trans
      exact le_of_eq (by rw [pow_succ]; ring)
    · rw [Nat.min_eq_right (by omega : n ≤ 100 * k ^ (r + 1) * ell)]
      exact (Nat.min_le_right _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  change ((min (100 * k ^ (r + 1 + 1) * ell) n : ℕ) : ℝ) / n ≤
    (k : ℝ) * (((min (100 * k ^ (r + 1) * ell) n : ℕ) : ℝ) / n)
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hnum

end PivotProfile

namespace Hopset.Reference

theorem near_le_search (cfg : Config) (r : ℕ) :
    Early.nearRadius cfg.k cfg.groups (distanceScale cfg r) ≤
      Early.searchRadius cfg.k cfg.groups (distanceScale cfg r) := by
  have hD : 0 ≤ distanceScale cfg r := by unfold distanceScale; positivity
  unfold Early.nearRadius Early.searchRadius
  nlinarith

theorem next_near_separated (cfg : Config) (r : ℕ) :
    Early.nearRadius cfg.k cfg.groups (distanceScale cfg (r + 1)) ≤
      Early.nextSearchBound cfg.k cfg.groups (distanceScale cfg r) :=
  (near_le_search cfg (r + 1)).trans (next_search_separated cfg r)

theorem next_near_budget (cfg : Config) (r : ℕ) :
    distanceScale cfg r + Early.nearRadius cfg.k cfg.groups (distanceScale cfg (r + 1)) ≤
      Early.searchRadius cfg.k cfg.groups (distanceScale cfg r) := by
  have hD : 0 ≤ distanceScale cfg r := by unfold distanceScale; positivity
  have hl : 0 ≤ Early.lambda cfg.k cfg.groups := by unfold Early.lambda; positivity
  have hs := next_near_separated cfg r
  unfold Early.nextSearchBound Early.searchRadius at *
  nlinarith [mul_nonneg hl hD]

theorem denominator_early (cfg : Config) (r : ℕ) (hr : r ≤ cfg.earlyLevel) :
    cfg.denominatorAt r = cfg.initialDenominator * (100 * cfg.split) ^ r := by
  simp only [Config.denominatorAt, Nat.min_eq_left hr, Nat.sub_eq_zero_of_le hr, pow_zero, mul_one]

theorem distanceScale_early (cfg : Config) (r : ℕ) (hr : r ≤ cfg.earlyLevel) :
    distanceScale cfg r =
      ((cfg.initialNumerator : ℝ) / cfg.initialDenominator) / (100 * (cfg.split : ℝ)) ^ r := by
  simp only [distanceScale, denominator_early cfg r hr, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, div_mul_eq_div_div]

end Hopset.Reference

namespace Parameters

theorem type3_related_parameter_budget (n : ℕ) (hn : 0 < n) (r : ℕ) :
    96 * (ballSize n r : ℝ) ^ 2 * (PivotProfile.rate n hn (k n) (ell n) r).value ^ 2 ≤ groups n := by
  have hp := (PivotProfile.rate n hn (k n) (ell n) r).value_nonneg
  have hsquare :
      ((ballSize n r : ℝ) * (PivotProfile.rate n hn (k n) (ell n) r).value) ^ 2 ≤
        (200 * (k n : ℝ) * ell n) ^ 2 := by
    gcongr 1
    exact ball_rate_upper n hn r
  norm_num only [groups, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

theorem center_ge_log_cube (n accuracy : ℕ) : ell n ^ 3 ≤ centerDenominator n accuracy :=
  (Nat.le_mul_of_pos_left _ (by omega : 0 < 8 * k n * groups n + 2)).trans (eta_logarithm_budget n accuracy)

noncomputable def pathScale (n accuracy : ℕ) : ℝ := (centerDenominator n accuracy : ℝ) / (ell n : ℝ) ^ 3

theorem pathScale_one_le (n accuracy : ℕ) : 1 ≤ pathScale n accuracy := by
  have he : (0 : ℝ) < ell n := by exact_mod_cast ell_pos n
  apply (le_div_iff₀ (pow_pos he 3)).mpr
  simpa only [one_mul, ← Nat.cast_pow] using (show ((ell n ^ 3 : ℕ) : ℝ) ≤ centerDenominator n accuracy by
    exact_mod_cast center_ge_log_cube n accuracy)

theorem pathScale_identity (n accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (r : ℕ) (hr : r ≤ threshold n x) :
    Hopset.Reference.distanceScale (configuration n accuracy x delta blockVolume ha hd) r *
        (pathScale n accuracy * (100 * (split n : ℝ)) ^ r) =
      queryUnit n accuracy x := by
  have he : (ell n : ℝ) ≠ 0 := by exact_mod_cast (ell_pos n).ne'
  have hc : (centerDenominator n accuracy : ℝ) ≠ 0 := by exact_mod_cast (centerDenominator_pos n accuracy).ne'
  have hs : (split n : ℝ) ≠ 0 := by exact_mod_cast (split_pos n).ne'
  rw [Hopset.Reference.distanceScale_early _ r hr]
  simp only [configuration, initialNumerator, pathScale, Nat.cast_mul, Nat.cast_pow]
  field_simp [he, hc, hs]

theorem path_weight_div_scale (n accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (r : ℕ) (hr : r ≤ threshold n x) (W : ℝ) (hW : W ≤ 3 * queryUnit n accuracy x) :
    W / Hopset.Reference.distanceScale (configuration n accuracy x delta blockVolume ha hd) r ≤
      3 * pathScale n accuracy * (100 * (split n : ℝ)) ^ r := by
  have hD := Hopset.Reference.distanceScale_pos
    (configuration n accuracy x delta blockVolume ha hd) (initialNumerator_pos n accuracy x ha) r
  apply (div_le_iff₀ hD).mpr
  have hi := pathScale_identity n accuracy x delta blockVolume ha hd r hr
  nlinarith

end Parameters

end StreamingReachability
