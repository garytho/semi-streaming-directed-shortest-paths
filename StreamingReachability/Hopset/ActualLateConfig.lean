module

public import StreamingReachability.Hopset.PathNumerics
public import StreamingReachability.Late.Numeric

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

def actualLateConfig (n : ℕ) (hn : 0 < n) (cfg : Config) : Late.Config where
  A := cfg.inputScale
  positive_rounding := cfg.inputScale_pos
  k := cfg.k
  M := cfg.groups
  N := cfg.shifts
  positive_k := cfg.k_pos
  positive_groups := cfg.groups_pos
  positive_shifts := cfg.shifts_pos
  rate := fun remaining => (PivotProfile.rate n hn cfg.k cfg.logarithm (cfg.maximumLevel - remaining)).value
  rate_nonneg := fun remaining => (PivotProfile.rate n hn cfg.k cfg.logarithm (cfg.maximumLevel - remaining)).value_nonneg
  rate_le_one := fun remaining => (PivotProfile.rate n hn cfg.k cfg.logarithm (cfg.maximumLevel - remaining)).value_le_one
  ballBound := fun remaining => Parameters.ballSize n (cfg.maximumLevel - remaining)

theorem actual_late_balance (n : ℕ) (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    ∀ remaining,
      ((actualLateConfig n hn cfg).ballBound remaining : ℝ) * (actualLateConfig n hn cfg).rate remaining ≤
        2 * 100 * (actualLateConfig n hn cfg).k * Parameters.ell n := by
  dsimp only
  intro remaining
  have h := Parameters.ball_rate_upper n hn (Parameters.maximumLevel n - remaining)
  convert h using 1 <;> norm_num [actualLateConfig, Parameters.configuration, Config.k, Parameters.k]

theorem actual_late_scale (cfg : Config) (q : ℕ) (hq : cfg.earlyLevel ≤ q) :
    Reference.distanceScale cfg (q + 1) = Reference.distanceScale cfg q / 4 := by
  simp only [Reference.distanceScale, Reference.denominator_succ_late cfg q hq, Nat.cast_mul, Nat.cast_ofNat,
    div_mul_eq_div_div]

theorem actual_late_balls {n : ℕ} (hn : 0 < n) (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (q : ℕ) (hq : q ≤ cfg.maximumLevel) (S : Finset (Fin n)) :
    (actualLateConfig n hn cfg).BallsGood stored (StoredEdges.graphOfEdges input)
        (cfg.maximumLevel - q) S (Reference.distanceScale cfg q) ↔
      Reference.BallsGood cfg stored input q S := by
  have he : cfg.maximumLevel - (cfg.maximumLevel - q) = q := by omega
  simp only [Late.Config.BallsGood, Late.Config.search, actualLateConfig, he, Reference.BallsGood]
  rfl

end

end StreamingReachability.Hopset
