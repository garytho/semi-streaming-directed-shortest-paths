module

public import StreamingSSSP.Hopset.HopCalibration

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

noncomputable def detourAt (cfg : Config) (q : ℕ) : ℝ :=
  if q + cfg.advance < cfg.earlyLevel then 3 * cfg.etaMax * distanceScale cfg (q + cfg.advance) else 0

theorem detourAt_nonneg (cfg : Config) (q : ℕ) : 0 ≤ detourAt cfg q := by
  have hD : 0 ≤ distanceScale cfg (q + cfg.advance) := by unfold distanceScale; positivity
  unfold detourAt
  split_ifs <;> positivity

end StreamingSSSP.Hopset.Reference

namespace StreamingSSSP.Parameters

open scoped Classical BigOperators
open Hopset.Following

noncomputable section

theorem center_times_split (n accuracy : ℕ) :
    (centerDenominator n accuracy : ℝ) * (split n : ℝ) =
      (100 * (split n : ℝ)) ^ advance n accuracy := by
  have hL : 1 ≤ advance n accuracy := by have h := advance_large n accuracy; omega
  simp only [centerDenominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
  rw [mul_assoc, ← pow_succ (split n : ℝ) (advance n accuracy - 1), Nat.sub_add_cancel hL]

theorem level_detour_charge (n accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta) (q : ℕ) :
    let cfg := configuration n accuracy x delta blockVolume ha hd
    pieceThreshold (pathScale n accuracy) (split n : ℝ) (ell n : ℝ) q * Hopset.Reference.detourAt cfg q *
        (centerDenominator n accuracy : ℝ) ≤
      24576 * cfg.etaMax * (ell n : ℝ) ^ 2 * queryUnit n accuracy x := by
  let cfg := configuration n accuracy x delta blockVolume ha hd
  change pieceThreshold (pathScale n accuracy) (split n : ℝ) (ell n : ℝ) q * Hopset.Reference.detourAt cfg q *
    (centerDenominator n accuracy : ℝ) ≤ _
  by_cases hq : q + cfg.advance < cfg.earlyLevel
  · have hr : q + advance n accuracy ≤ threshold n x := by
      change q + advance n accuracy < threshold n x at hq
      omega
    have hi := pathScale_identity n accuracy x delta blockVolume ha hd (q + advance n accuracy) hr
    change Hopset.Reference.distanceScale cfg (q + cfg.advance) *
      (pathScale n accuracy * (100 * (split n : ℝ)) ^ (q + cfg.advance)) =
        queryUnit n accuracy x at hi
    have hp : (100 * (split n : ℝ)) ^ cfg.advance =
        (centerDenominator n accuracy : ℝ) * (split n : ℝ) := (center_times_split n accuracy).symm
    rw [pow_add (100 * (split n : ℝ)) q cfg.advance, hp] at hi
    have he := congrArg (fun z : ℝ => 24576 * (cfg.etaMax : ℝ) * (ell n : ℝ) ^ 2 * z) hi
    simp only [Hopset.Reference.detourAt, ite_eq_left hq]
    unfold pieceThreshold
    nlinarith only [he]
  · simp only [Hopset.Reference.detourAt, ite_eq_right hq, mul_zero, zero_mul]
    positivity

theorem total_detour_budget (n accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta) :
    let cfg := configuration n accuracy x delta blockVolume ha hd
    (∑ q ∈ Finset.range (cfg.earlyLevel + 1),
      pieceThreshold (pathScale n accuracy) (split n : ℝ) (ell n : ℝ) q * Hopset.Reference.detourAt cfg q) ≤
      (queryUnit n accuracy x : ℝ) / accuracyDenominator n accuracy := by
  let cfg := configuration n accuracy x delta blockVolume ha hd
  let total := ∑ q ∈ Finset.range (cfg.earlyLevel + 1),
    pieceThreshold (pathScale n accuracy) (split n : ℝ) (ell n : ℝ) q * Hopset.Reference.detourAt cfg q
  have hc : (0 : ℝ) < centerDenominator n accuracy := by exact_mod_cast centerDenominator_pos n accuracy
  have hden : (0 : ℝ) < accuracyDenominator n accuracy := by exact_mod_cast accuracyDenominator_pos n accuracy ha
  have hunit : (0 : ℝ) ≤ queryUnit n accuracy x := Nat.cast_nonneg _
  have hr : cfg.earlyLevel ≤ ell n :=
    (Nat.min_le_left _ _).trans (maximumLevel_le_logarithm n)
  have hrange : ((cfg.earlyLevel + 1 : ℕ) : ℝ) ≤ 2 * (ell n : ℝ) := by
    exact_mod_cast (show cfg.earlyLevel + 1 ≤ 2 * ell n by have h := ell_pos n; omega)
  have hsum : total * (centerDenominator n accuracy : ℝ) ≤
      ((cfg.earlyLevel + 1 : ℕ) : ℝ) * (24576 * (cfg.etaMax : ℝ) * (ell n : ℝ) ^ 2 * queryUnit n accuracy x) := by
    have h := Finset.sum_le_sum (s := Finset.range (cfg.earlyLevel + 1))
      (fun q _ => level_detour_charge n accuracy x delta blockVolume ha hd q)
    simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    simpa only [total, cfg, mul_assoc] using h
  have hupper : total * (centerDenominator n accuracy : ℝ) ≤
      49152 * (cfg.etaMax : ℝ) * (ell n : ℝ) ^ 3 * queryUnit n accuracy x := by
    have hm := mul_le_mul_of_nonneg_right hrange
      (show 0 ≤ 24576 * (cfg.etaMax : ℝ) * (ell n : ℝ) ^ 2 * queryUnit n accuracy x by positivity)
    nlinarith only [hsum, hm]
  have heta : cfg.etaMax = 8 * k n * groups n + 2 := by
    dsimp only [cfg, configuration, Hopset.Config.etaMax, Hopset.Config.lambda, Hopset.Config.width,
      Hopset.Config.k, k]
    ring
  have hcalNat : 2 ^ 30 * cfg.etaMax * ell n ^ 3 * accuracyDenominator n accuracy ≤ centerDenominator n accuracy := by
    rw [heta]
    exact detour_parameter_budget n accuracy
  have hcal : (2 : ℝ) ^ 30 * cfg.etaMax * (ell n : ℝ) ^ 3 * accuracyDenominator n accuracy ≤
      centerDenominator n accuracy := by exact_mod_cast hcalNat
  have hsmall : 49152 * (cfg.etaMax : ℝ) * (ell n : ℝ) ^ 3 * accuracyDenominator n accuracy ≤
      centerDenominator n accuracy := by
    calc
      _ ≤ (2 : ℝ) ^ 30 * cfg.etaMax * (ell n : ℝ) ^ 3 * accuracyDenominator n accuracy := by gcongr; norm_num
      _ ≤ _ := hcal
  have hm := mul_le_mul_of_nonneg_right hupper hden.le
  have hu := mul_le_mul_of_nonneg_right hsmall hunit
  change total ≤ (queryUnit n accuracy x : ℝ) / accuracyDenominator n accuracy
  apply (le_div_iff₀ hden).mpr
  apply (mul_le_mul_iff_left₀ hc).mp
  nlinarith only [hm, hu]

theorem global_detour_budget (n accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta) (r : ℕ) :
    let cfg := configuration n accuracy x delta blockVolume ha hd
    3 * cfg.etaMax * Hopset.Reference.distanceScale cfg r ≤
      (queryUnit n accuracy x : ℝ) / accuracyDenominator n accuracy := by
  let cfg := configuration n accuracy x delta blockVolume ha hd
  have hc : (0 : ℝ) < centerDenominator n accuracy := by exact_mod_cast centerDenominator_pos n accuracy
  have hden : (0 : ℝ) < accuracyDenominator n accuracy := by exact_mod_cast accuracyDenominator_pos n accuracy ha
  have hunit : (0 : ℝ) ≤ queryUnit n accuracy x := Nat.cast_nonneg _
  have heta : cfg.etaMax = 8 * k n * groups n + 2 := by
    dsimp only [cfg, configuration, Hopset.Config.etaMax, Hopset.Config.lambda, Hopset.Config.width,
      Hopset.Config.k, k]
    ring
  have hcalNat : 2 ^ 30 * cfg.etaMax * ell n ^ 3 * accuracyDenominator n accuracy ≤ centerDenominator n accuracy := by
    rw [heta]
    exact detour_parameter_budget n accuracy
  have hcal : (2 : ℝ) ^ 30 * cfg.etaMax * (ell n : ℝ) ^ 3 * accuracyDenominator n accuracy ≤
      centerDenominator n accuracy := by exact_mod_cast hcalNat
  have hsmall : 3 * (cfg.etaMax : ℝ) * (ell n : ℝ) ^ 3 * accuracyDenominator n accuracy ≤
      centerDenominator n accuracy := by
    calc
      _ ≤ (2 : ℝ) ^ 30 * cfg.etaMax * (ell n : ℝ) ^ 3 * accuracyDenominator n accuracy := by gcongr; norm_num
      _ ≤ _ := hcal
  have hzero : Hopset.Reference.distanceScale cfg 0 * (centerDenominator n accuracy : ℝ) =
      (queryUnit n accuracy x : ℝ) * (ell n : ℝ) ^ 3 := by
    simp only [Hopset.Reference.distanceScale, Hopset.Config.denominatorAt, Nat.zero_min, Nat.zero_sub,
      pow_zero, mul_one]
    change (((queryUnit n accuracy x * ell n ^ 3 : ℕ) : ℝ) / (centerDenominator n accuracy : ℝ)) *
      (centerDenominator n accuracy : ℝ) = _
    push_cast
    exact div_mul_cancel₀ _ hc.ne'
  have hinit : 3 * (cfg.etaMax : ℝ) * Hopset.Reference.distanceScale cfg 0 ≤
      (queryUnit n accuracy x : ℝ) / accuracyDenominator n accuracy := by
    apply (le_div_iff₀ hden).mpr
    apply (mul_le_mul_iff_left₀ hc).mp
    have he := congrArg (fun z : ℝ => 3 * (cfg.etaMax : ℝ) * accuracyDenominator n accuracy * z) hzero
    have hu := mul_le_mul_of_nonneg_right hsmall hunit
    nlinarith only [he, hu]
  have hscale := Hopset.Reference.distanceScale_antitone cfg (Nat.zero_le r)
  exact (mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 3 * (cfg.etaMax : ℝ))).trans hinit

end

end StreamingSSSP.Parameters
