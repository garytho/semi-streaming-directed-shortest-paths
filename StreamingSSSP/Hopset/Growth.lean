module

public import StreamingSSSP.Probability

@[expose] public section

namespace StreamingSSSP

theorem power_le_geometric_budget (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (hm : m * x < 1) :
    (1 + x) ^ m ≤ 1 / (1 - m * x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hprev : (m : ℝ) * x < 1 := by
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by simp
        rw [hcast] at hm
        nlinarith
      have hden : 0 < 1 - (m : ℝ) * x := by linarith
      have hn : 0 < 1 - ((m + 1 : ℕ) : ℝ) * x := by linarith
      rw [pow_succ]
      apply (mul_le_mul_of_nonneg_right (ih hprev) (by linarith)).trans
      apply (le_div_iff₀ hn).mpr
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply (div_le_iff₀ hden).mpr
      push_cast
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ m + 1 by positivity) (sq_nonneg x)]

theorem power_le_two (x : ℝ) (hx : 0 ≤ x) (m : ℕ) (hm : m * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 2 := by
  apply (power_le_geometric_budget x hx m (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1 - (m : ℝ) * x)).mpr
  linarith

theorem cumulative_growth_step (x : ℝ) (hx : 0 ≤ x) (fuel : ℕ) :
    1 + ((fuel : ℝ) * (1 + x) ^ fuel) * (1 + x) ≤
      ((fuel + 1 : ℕ) : ℝ) * (1 + x) ^ (fuel + 1) := by
  have h : 1 ≤ (1 + x) ^ (fuel + 1) := one_le_pow₀ (by linarith)
  rw [pow_succ] at h ⊢
  push_cast
  nlinarith

theorem stage_accuracy (r ell stages : ℕ) (hr : 0 < r) (he : 0 < ell)
    (hs : stages ≤ ell) :
    (1 + 1 / (10 * (r : ℝ) * ell)) ^ stages ≤ 1 + 1 / (2 * r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heR : (0 : ℝ) < ell := by exact_mod_cast he
  have hsR : (stages : ℝ) ≤ ell := by exact_mod_cast hs
  have hbudget : (stages : ℝ) * (1 / (10 * (r : ℝ) * ell)) ≤ 1 / (10 * r) := by
    calc
      _ ≤ (ell : ℝ) * (1 / (10 * (r : ℝ) * ell)) := by gcongr
      _ = _ := by field_simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsmall : (stages : ℝ) * (1 / (10 * (r : ℝ) * ell)) < 1 := by
    have hbound : 1 / (10 * (r : ℝ)) ≤ 1 / 10 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
      linarith
    linarith
  apply (power_le_geometric_budget _ (by positivity) _ hsmall).trans
  have hden : 0 < 1 - (stages : ℝ) * (1 / (10 * (r : ℝ) * ell)) := by linarith
  apply (div_le_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_right hbudget
    (show (0 : ℝ) ≤ 1 + 1 / (2 * r) by positivity)
  have hid : (1 + 1 / (2 * (r : ℝ))) * (1 - 1 / (10 * r)) - 1 =
      (8 * r - 1) / (20 * (r : ℝ) ^ 2) := by field_simp; ring
  have hnum : 0 ≤ 8 * (r : ℝ) - 1 := by linarith
  have hnonneg : 0 ≤ (8 * (r : ℝ) - 1) / (20 * (r : ℝ) ^ 2) :=
    div_nonneg hnum (by positivity)
  nlinarith

def pieceEnvelope (C b ell : ℝ) (r : ℕ) : ℝ := 128 * C * (100 * b) ^ r * b * ell

theorem pieceEnvelope_step (C b ell : ℝ) (hC : 0 ≤ C) (hb : 1 ≤ b) (he : 1 ≤ ell)
    (r : ℕ) :
    2 * pieceEnvelope C b ell (r + 1) + 36 * b ^ 2 * pieceEnvelope C b ell r +
        3 * C * (100 * b) ^ (r + 2) +
        2400 * b ^ 2 * ell * C * (100 * b) ^ (r + 1) ≤
      pieceEnvelope C b ell (r + 2) := by
  have ha : 0 ≤ C * (100 * b) ^ r := by positivity
  have hbell : 1 ≤ b * ell := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (sub_nonneg.mpr he)]
  have h1 := mul_nonneg
    (show 0 ≤ C * (100 * b) ^ r * b ^ 2 * ell by positivity) (sub_nonneg.mpr hb)
  have h2 := mul_nonneg
    (show 0 ≤ C * (100 * b) ^ r * b ^ 2 by positivity) (sub_nonneg.mpr hbell)
  have h3 : 0 ≤ C * (100 * b) ^ r * b ^ 3 * ell := by positivity
  dsimp only [pieceEnvelope]
  simp only [pow_add, pow_one, pow_two]
  nlinarith

theorem second_order_piece_bound (z : ℕ → ℝ) (C b ell : ℝ)
    (hC : 0 ≤ C) (hb : 1 ≤ b) (he : 1 ≤ ell) (horizon : ℕ)
    (hzero : z 0 ≤ pieceEnvelope C b ell 0)
    (hone : 1 ≤ horizon → z 1 ≤ pieceEnvelope C b ell 1)
    (hstep : ∀ r, r + 2 ≤ horizon →
      z (r + 2) ≤ 2 * z (r + 1) + 36 * b ^ 2 * z r +
        3 * C * (100 * b) ^ (r + 2) +
        2400 * b ^ 2 * ell * C * (100 * b) ^ (r + 1)) :
    ∀ r ≤ horizon, z r ≤ pieceEnvelope C b ell r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hr
      cases r with
      | zero => exact hzero
      | succ r =>
          cases r with
          | zero => exact hone hr
          | succ r =>
              have hprev := ih (r + 1) (by omega) (by omega)
              have hpast := ih r (by omega) (by omega)
              apply (hstep r hr).trans
              calc
                _ ≤ 2 * pieceEnvelope C b ell (r + 1) +
                    36 * b ^ 2 * pieceEnvelope C b ell r +
                    3 * C * (100 * b) ^ (r + 2) +
                    2400 * b ^ 2 * ell * C * (100 * b) ^ (r + 1) := by gcongr
                _ ≤ _ := pieceEnvelope_step C b ell hC hb he r

end StreamingSSSP
