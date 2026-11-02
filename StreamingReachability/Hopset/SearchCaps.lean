module

public import StreamingReachability.Hopset.NodeQueries
public import StreamingReachability.Hopset.ScaleSeparation
public import StreamingReachability.Early.Stars

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

theorem searchRadius_eta (cfg : Config) (D : ℝ) :
    Early.searchRadius cfg.k cfg.groups D = (cfg.etaMax : ℝ) * D := by
  simp only [Early.searchRadius, Early.lambda, Config.etaMax, Config.lambda, Config.width,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem bounded_search_iff (cfg : Config) (r : ℕ) (d : Distance) :
    Early.Bounded d (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) ↔
      d ≤ (cfg.searchRadius r : Distance) := by
  have h := (Late.withinFraction_iff_bounded d (cfg.etaMax * cfg.initialNumerator)
    (cfg.denominatorAt r) (cfg.denominatorAt_pos r)).symm
  simpa only [Reference.distanceScale, searchRadius_real, withinFraction,
    decide_eq_true_eq, Config.searchRadius] using h

theorem within_search_iff {V : Type*} [Fintype V] (cfg : Config) (r : ℕ) (G : Graph V) (u v : V) :
    Early.Within G u v (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) ↔
      G.dist u v ≤ (cfg.searchRadius r : Distance) :=
  bounded_search_iff cfg r (G.dist u v)

theorem bounded_integer_iff (d : Distance) (m : ℕ) :
    Early.Bounded d (m : ℝ) ↔ d ≤ (m : Distance) := by
  constructor
  · rintro ⟨a, ha, ham⟩
    rw [ha]
    exact WithTop.coe_le_coe.mpr (by exact_mod_cast ham)
  · intro hd
    exact Early.bounded_mono_distance hd ⟨m, rfl, le_rfl⟩

theorem search_cap_real (cfg : Config) (r : ℕ) :
    (cfg.searchRadius r : ℝ) ≤ Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r) := by
  have hd : (0 : ℝ) < cfg.denominatorAt r := by exact_mod_cast cfg.denominatorAt_pos r
  rw [Reference.distanceScale, searchRadius_real]
  apply (le_div_iff₀ hd).mpr
  exact_mod_cast Nat.div_mul_le_self (cfg.etaMax * cfg.initialNumerator) (cfg.denominatorAt r)

theorem nat_excess_le (a w : ℕ) (B : ℝ) (hB : 0 ≤ B) (h : (a : ℝ) ≤ w + B) :
    ((a - w : ℕ) : ℝ) ≤ B := by
  by_cases hw : w ≤ a
  · rw [Nat.cast_sub hw]
    linarith
  · have ha : a - w = 0 := by omega
    simpa only [ha, Nat.cast_zero] using hB

theorem calibrated_initial_search (n accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg 0) ≤ Parameters.queryUnit n accuracy x := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  change Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg 0) ≤ Parameters.queryUnit n accuracy x
  have hc : (0 : ℝ) < Parameters.centerDenominator n accuracy := by
    exact_mod_cast Parameters.centerDenominator_pos n accuracy
  rw [Reference.distanceScale, searchRadius_real]
  simp only [Config.denominatorAt, Nat.zero_min, Nat.zero_sub, pow_zero, mul_one]
  apply (div_le_iff₀ hc).mpr
  have h := Nat.mul_le_mul_right (Parameters.queryUnit n accuracy x) (Parameters.eta_logarithm_budget n accuracy)
  have heta : cfg.etaMax = 8 * Parameters.k n * Parameters.groups n + 2 := by
    dsimp only [cfg, Parameters.configuration, Config.etaMax, Config.lambda, Config.width, Config.k, Parameters.k]
    ring
  rw [heta]
  change (((8 * Parameters.k n * Parameters.groups n + 2) *
    (Parameters.queryUnit n accuracy x * Parameters.ell n ^ 3) : ℕ) : ℝ) ≤
      (Parameters.queryUnit n accuracy x : ℝ) * Parameters.centerDenominator n accuracy
  exact_mod_cast (show (8 * Parameters.k n * Parameters.groups n + 2) *
    (Parameters.queryUnit n accuracy x * Parameters.ell n ^ 3) ≤
      Parameters.queryUnit n accuracy x * Parameters.centerDenominator n accuracy by nlinarith)

end

end StreamingReachability.Hopset
