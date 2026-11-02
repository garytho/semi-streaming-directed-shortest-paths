module

public import StreamingSSSP.Hopset.PathCalibration

@[expose] public section

namespace StreamingSSSP.Hopset.Following

structure EarlyNumerics (n : ℕ) (cfg : Config) (ps : List Rate) (r : ℕ) : Prop where
  before : r < cfg.earlyLevel
  rankIndex : r < ps.length
  prefixHalf : ((ps.take r).map Rate.value).sum ≤ 1 / 2
  balls : 1 ≤ Parameters.ballSize n r
  grid : Reference.distanceScale cfg r ≤ cfg.shifts
  groups : 2 ≤ cfg.groups
  positive : 0 < (Ranks.rate ps r).value
  cuts : 48 * Parameters.ballSize n r * (Ranks.rate ps r).value / cfg.groups ≤ 1
  related : 96 * (Parameters.ballSize n r : ℝ) ^ 2 * (Ranks.rate ps r).value ^ 2 ≤ cfg.groups
  balance : (Parameters.ballSize n r : ℝ) * (Ranks.rate ps r).value ≤ 200 * cfg.k * cfg.logarithm

theorem calibrated_early_numerics (n : ℕ) (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (r : ℕ) (hr : r < Parameters.threshold n x) :
    EarlyNumerics n (Parameters.configuration n accuracy x delta blockVolume ha hd) (Reference.earlyRates n hn x) r := by
  have hk : 0 < Parameters.k n := by have h := Parameters.k_large n; omega
  have hell := Parameters.ell_pos n
  have hlookup : Ranks.rate (Reference.earlyRates n hn x) r =
      PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r :=
    PivotProfile.lookup n hn (Parameters.k n) (Parameters.ell n) (Parameters.threshold n x) r hr
  refine ⟨hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Reference.earlyRates, PivotProfile.length_rates] using hr
  · exact Parameters.early_prefix_half n hn x r hr
  · exact Parameters.ballSize_pos n hn r (hr.le.trans (Parameters.threshold_le_maximum n x))
  · exact Reference.calibrated_shift_grid n accuracy x delta blockVolume ha hd r
  · change 2 ≤ Parameters.groups n
    have hp : 0 < 100 ^ 2 * Parameters.k n ^ 2 * Parameters.ell n ^ 2 := by positivity
    unfold Parameters.groups
    nlinarith
  · rw [hlookup]
    exact PivotProfile.rate_pos n hn (Parameters.k n) (Parameters.ell n) r hk hell
  · change 48 * (Parameters.ballSize n r : ℝ) * (Ranks.rate (Reference.earlyRates n hn x) r).value /
      Parameters.groups n ≤ 1
    rw [hlookup]
    apply (Parameters.type3_parameter_budget n hn r).trans
    have hkR : (1 : ℝ) ≤ Parameters.k n := by exact_mod_cast hk
    have heR : (1 : ℝ) ≤ Parameters.ell n := by exact_mod_cast hell
    apply (div_le_one (by positivity : (0 : ℝ) < 4 * 100 * Parameters.k n * Parameters.ell n)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (sub_nonneg.mpr heR)]
  · change 96 * (Parameters.ballSize n r : ℝ) ^ 2 *
      (Ranks.rate (Reference.earlyRates n hn x) r).value ^ 2 ≤ Parameters.groups n
    rw [hlookup]
    exact Parameters.type3_related_parameter_budget n hn r
  · change (Parameters.ballSize n r : ℝ) * (Ranks.rate (Reference.earlyRates n hn x) r).value ≤
      200 * Parameters.k n * Parameters.ell n
    rw [hlookup]
    exact Parameters.ball_rate_upper n hn r

theorem calibrated_rate_step (n : ℕ) (hn : 0 < n) (x r : ℕ)
    (hr : r + 1 < Parameters.threshold n x) :
    (Ranks.rate (Reference.earlyRates n hn x) (r + 1)).value ≤
      (Parameters.k n : ℝ) * (Ranks.rate (Reference.earlyRates n hn x) r).value := by
  rw [Reference.earlyRates,
    PivotProfile.lookup n hn (Parameters.k n) (Parameters.ell n) (Parameters.threshold n x) (r + 1) hr,
    PivotProfile.lookup n hn (Parameters.k n) (Parameters.ell n) (Parameters.threshold n x) r (by omega)]
  exact PivotProfile.rate_succ_le n hn (Parameters.k n) (Parameters.ell n) r (by
    have h := Parameters.k_large n
    omega)

end StreamingSSSP.Hopset.Following
