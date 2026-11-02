module

public import StreamingSSSP.Hopset.AsymptoticCalibration
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace StreamingSSSP.Parameters

open Filter
open scoped Topology

theorem logarithm_real_bound (n : ℕ) (hlog : 1 ≤ Real.log n) :
    (ell n : ℝ) ≤ (1 + (Real.log 2)⁻¹) * Real.log n := by
  have h := Real.log2_le_logb n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (ell n : ℝ) = (n.log2 : ℝ) + 1 := by simp [ell]
  rw [he]
  unfold Real.logb at h
  rw [div_eq_mul_inv] at h
  nlinarith

theorem polylog_subpower (degree : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ᶠ n : ℕ in atTop, ((ell n ^ degree : ℕ) : ℝ) ≤ constant * (n : ℝ) ^ epsilon := by
  let alpha : ℝ := 1 + (Real.log 2)⁻¹
  have halpha : 0 < alpha := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [alpha]
    positivity
  have ho := (isLittleO_log_rpow_rpow_atTop (degree : ℝ) he).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hbound := ho.bound (by norm_num : (0 : ℝ) < 1)
  have hlog : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨alpha ^ degree, pow_pos halpha _, ?_⟩
  filter_upwards [hbound, hlog] with n hb hn
  have hl : (Real.log n) ^ degree ≤ (n : ℝ) ^ epsilon := by
    simpa only [Function.comp_def, Real.rpow_natCast,
      Real.norm_of_nonneg (by positivity : 0 ≤ (Real.log n) ^ degree),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) epsilon), one_mul] using hb
  calc
    ((ell n ^ degree : ℕ) : ℝ) = (ell n : ℝ) ^ degree := by norm_cast
    _ ≤ (alpha * Real.log n) ^ degree := by
      gcongr
      exact logarithm_real_bound n hn
    _ = alpha ^ degree * (Real.log n) ^ degree := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

theorem height_subpower_real {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ((100 ^ maximumLevel n : ℕ) : ℝ) ≤ (n : ℝ) ^ epsilon := by
  obtain ⟨power, hpower⟩ := exists_nat_gt (1 / epsilon)
  have hp : (0 : ℝ) < power := lt_trans (by positivity : (0 : ℝ) < 1 / epsilon) hpower
  have hne : (power : ℝ) ≠ 0 := ne_of_gt hp
  have hi : (power : ℝ)⁻¹ ≤ epsilon := by
    rw [← one_div, div_le_iff₀ hp]
    have h := (div_lt_iff₀ he).mp hpower
    nlinarith
  filter_upwards [eventually_ge_atTop (2 ^ (100 ^ power)), eventually_ge_atTop 1] with n hn hnpos
  have h : (((100 ^ maximumLevel n : ℕ) : ℝ) ^ power) ≤ (n : ℝ) := by
    exact_mod_cast height_subpower power n hn
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤
    ((100 ^ maximumLevel n : ℕ) : ℝ) ^ power) h (by positivity : (0 : ℝ) ≤ (power : ℝ)⁻¹)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ hne, Real.rpow_one] at hr
  exact hr.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnpos) hi)

theorem cube_real_upper (n : ℕ) (hn : 0 < n) :
    (blockSize n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hc : (blockSize n : ℝ) ^ 3 ≤ 8 * (n : ℝ) := by
    exact_mod_cast blockSize_cube_le n hn
  have hp := Real.rpow_mul_natCast (Nat.cast_nonneg n) (1 / 3 : ℝ) 3
  rw [show (1 / 3 : ℝ) * (3 : ℕ) = 1 by norm_num, Real.rpow_one] at hp
  have hright : (2 * (n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = 8 * (n : ℝ) := by
    rw [mul_pow, ← hp]
    norm_num
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 3)).mp
  simpa only [Real.rpow_ofNat, hright] using hc

/-- The literal cube-root block size, polylogarithmic factors, and the original
recursion height give `n^(1/3+o(1))`, in its quantified eventual form. -/
theorem cube_polylog_height (coefficient degree : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ n : ℕ in atTop,
      ((coefficient * blockSize n * ell n ^ degree * 100 ^ maximumLevel n : ℕ) : ℝ) ≤
        constant * (n : ℝ) ^ (1 / 3 + epsilon) := by
  obtain ⟨C, hC, hlog⟩ := polylog_subpower degree (half_pos he)
  have hheight := height_subpower_real (half_pos he)
  refine ⟨2 * (coefficient + 1 : ℕ) * C, by positivity, ?_⟩
  filter_upwards [hlog, hheight, eventually_ge_atTop 1] with n hl hh hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := cube_real_upper n (by omega)
  have hcoeff : (coefficient : ℝ) ≤ (coefficient + 1 : ℕ) := by exact_mod_cast Nat.le_succ coefficient
  push_cast at hl hh hcoeff ⊢
  calc
    _ ≤ (coefficient + 1 : ℕ) * (2 * (n : ℝ) ^ (1 / 3 : ℝ)) *
        (C * (n : ℝ) ^ (epsilon / 2)) * (n : ℝ) ^ (epsilon / 2) := by gcongr <;> omega
    _ = (2 * (coefficient + 1 : ℕ) * C) *
        ((n : ℝ) ^ (1 / 3 : ℝ) * ((n : ℝ) ^ (epsilon / 2) * (n : ℝ) ^ (epsilon / 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos,
        show (1 / 3 : ℝ) + (epsilon / 2 + epsilon / 2) = 1 / 3 + epsilon by ring]
      push_cast
      ring

end StreamingSSSP.Parameters
