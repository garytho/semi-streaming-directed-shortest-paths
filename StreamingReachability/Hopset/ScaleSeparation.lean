module

public import StreamingReachability.Hopset.ReferenceFacts

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical

noncomputable section

theorem denominator_succ_early (cfg : Config) (r : ℕ) (hr : r < cfg.earlyLevel) :
    cfg.denominatorAt (r + 1) = cfg.denominatorAt r * (100 * cfg.split) := by
  have hmin : min r cfg.earlyLevel = r := Nat.min_eq_left (by omega)
  have hminnext : min (r + 1) cfg.earlyLevel = r + 1 := Nat.min_eq_left (by omega)
  have hsub : r - cfg.earlyLevel = 0 := by omega
  have hsubnext : r + 1 - cfg.earlyLevel = 0 := by omega
  simp only [Config.denominatorAt, hmin, hminnext, hsub, hsubnext, pow_zero, mul_one, pow_succ]
  ring

theorem denominator_succ_late (cfg : Config) (r : ℕ) (hr : cfg.earlyLevel ≤ r) :
    cfg.denominatorAt (r + 1) = cfg.denominatorAt r * 4 := by
  have hmin : min r cfg.earlyLevel = cfg.earlyLevel := Nat.min_eq_right hr
  have hminnext : min (r + 1) cfg.earlyLevel = cfg.earlyLevel := Nat.min_eq_right (by omega)
  have hsubnext : r + 1 - cfg.earlyLevel = (r - cfg.earlyLevel) + 1 := by omega
  simp only [Config.denominatorAt, hmin, hminnext, hsubnext, pow_succ]
  ring

theorem denominator_growth (cfg : Config) (r : ℕ) :
    4 * cfg.denominatorAt r ≤ cfg.denominatorAt (r + 1) := by
  by_cases he : r < cfg.earlyLevel
  · rw [denominator_succ_early cfg r he]
    have hs := cfg.split_pos
    nlinarith
  · rw [denominator_succ_late cfg r (by omega)]
    omega

theorem distanceScale_growth (cfg : Config) (r : ℕ) :
    4 * distanceScale cfg (r + 1) ≤ distanceScale cfg r := by
  have hd : (0 : ℝ) < cfg.denominatorAt r := by exact_mod_cast cfg.denominatorAt_pos r
  have hdnext : (0 : ℝ) < cfg.denominatorAt (r + 1) := by exact_mod_cast cfg.denominatorAt_pos (r + 1)
  have hden : 4 * (cfg.denominatorAt r : ℝ) ≤ cfg.denominatorAt (r + 1) := by
    exact_mod_cast denominator_growth cfg r
  unfold distanceScale
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hdnext hd).mpr
  have hm := mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg cfg.initialNumerator)
  nlinarith

theorem distanceScale_antitone (cfg : Config) : Antitone (distanceScale cfg) := by
  apply antitone_nat_of_succ_le
  intro r
  have h := distanceScale_growth cfg r
  have hn : 0 ≤ distanceScale cfg (r + 1) := by unfold distanceScale; positivity
  linarith

theorem distanceScale_gap (cfg : Config) {q r : ℕ} (hqr : q < r) :
    distanceScale cfg r ≤ distanceScale cfg q / 2 := by
  have hm := distanceScale_antitone cfg (Nat.succ_le_of_lt hqr)
  have hg := distanceScale_growth cfg q
  have hn : 0 ≤ distanceScale cfg q := by unfold distanceScale; positivity
  linarith

theorem next_search_separated (cfg : Config) (r : ℕ) :
    Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1)) ≤
      Early.nextSearchBound cfg.k cfg.groups (distanceScale cfg r) := by
  have hk : (1 : ℝ) ≤ cfg.k := by exact_mod_cast cfg.k_pos
  have hM : (1 : ℝ) ≤ cfg.groups := by exact_mod_cast cfg.groups_pos
  have hl : 3 ≤ Early.lambda cfg.k cfg.groups := by
    unfold Early.lambda
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hM)]
  have hD : 0 ≤ distanceScale cfg r := by unfold distanceScale; positivity
  have hstep := distanceScale_growth cfg r
  have h1 := mul_nonneg (show 0 ≤ 2 * Early.lambda cfg.k cfg.groups + 2 by linarith)
    (sub_nonneg.mpr hstep)
  have h2 := mul_nonneg (sub_nonneg.mpr hl) hD
  unfold Early.searchRadius Early.nextSearchBound
  nlinarith

theorem radii_above_next_search {n : ℕ} (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (G : Graph (Fin n)) (owners : Owners n cfg) (p : Fin n) :
    Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1)) ≤ radii cfg r G owners p := by
  apply (next_search_separated cfg r).trans
  have hD := distanceScale_pos cfg hnum r
  have hr := (Late.radius_bounds G (distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos
    hD p (owners p)).1
  unfold Early.nextSearchBound
  change _ ≤ Late.radius G (distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos p (owners p)
  nlinarith

theorem distanceScale_le_initial (cfg : Config) (r : ℕ) :
    distanceScale cfg r ≤ (cfg.initialNumerator : ℝ) / cfg.initialDenominator := by
  have hd : (0 : ℝ) < cfg.initialDenominator := by exact_mod_cast cfg.denominator_pos
  have hden : (cfg.initialDenominator : ℝ) ≤ cfg.denominatorAt r := by
    exact_mod_cast Parameters.denominatorAt_ge_initial cfg r
  unfold distanceScale
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd hden

theorem calibrated_shift_grid (n accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (r : ℕ) :
    distanceScale (Parameters.configuration n accuracy x delta blockVolume ha hd) r ≤
      (Parameters.configuration n accuracy x delta blockVolume ha hd).shifts := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  apply (distanceScale_le_initial cfg r).trans
  have hden : (0 : ℝ) < cfg.initialDenominator := by exact_mod_cast cfg.denominator_pos
  apply (div_le_iff₀ hden).mpr
  have h := Parameters.le_mul_ceilDiv (Parameters.initialNumerator n accuracy x)
    (Parameters.centerDenominator n accuracy) (Parameters.centerDenominator_pos n accuracy)
  exact_mod_cast (show cfg.initialNumerator ≤ cfg.shifts * cfg.initialDenominator by
    simpa only [cfg, Parameters.configuration, Nat.mul_comm] using h)

end

end StreamingReachability.Hopset.Reference
