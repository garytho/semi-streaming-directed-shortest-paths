module

public import StreamingReachability.Approx.DecodeBounds

@[expose] public section

namespace StreamingReachability.Parameters

theorem five_accuracy_hops_le_unit (n accuracy x : ℕ) :
    5 * accuracy * hopBound n accuracy x ≤ queryUnit n accuracy x := by
  have h := Nat.mul_le_mul_left (160 * accuracy * hopBound n accuracy x) (show 1 ≤ ell n from ell_pos n)
  unfold queryUnit accuracyDenominator
  nlinarith only [h]

end StreamingReachability.Parameters

namespace StreamingReachability.Approx

noncomputable section

theorem fivefold_error (accuracy unit d cost : ℕ) (ha : 0 < accuracy)
    (hcost : (cost : ℝ) ≤ (1 + 1 / (5 * (accuracy : ℝ))) * unit * d) :
    5 * accuracy * cost ≤ (5 * accuracy + 1) * unit * d := by
  have haR : (0 : ℝ) < accuracy := by exact_mod_cast ha
  have hm := mul_le_mul_of_nonneg_right hcost (show 0 ≤ 5 * (accuracy : ℝ) by positivity)
  have heq : (1 + 1 / (5 * (accuracy : ℝ))) * unit * d * (5 * accuracy) =
      (5 * (accuracy : ℝ) + 1) * unit * d := by
    field_simp [haR.ne']
    <;> ring
  rw [heq] at hm
  have hn : cost * (5 * accuracy) ≤ (5 * accuracy + 1) * unit * d := by exact_mod_cast hm
  nlinarith only [hn]

theorem fivefold_coarse (accuracy unit d cost : ℕ) (ha : 0 < accuracy)
    (hcost : 5 * accuracy * cost ≤ (5 * accuracy + 1) * unit * d) :
    cost ≤ 2 * unit * d := by
  have hc : 5 * accuracy + 1 ≤ 2 * (5 * accuracy) := by omega
  have hm := Nat.mul_le_mul_right (unit * d) hc
  have hb : (5 * accuracy) * cost ≤ (5 * accuracy) * (2 * unit * d) := by nlinarith only [hcost, hm]
  by_contra hn
  have hlt : 2 * unit * d < cost := by omega
  have hp := Nat.mul_lt_mul_of_pos_left hlt (show 0 < 5 * accuracy by positivity)
  omega

theorem integer_decode_accuracy (accuracy unit hops scale d cost rounded : ℕ)
    (hunit : 0 < unit) (hscale : scale ≤ d)
    (hspace : 5 * accuracy * hops ≤ unit)
    (hcost : 5 * accuracy * cost ≤ (5 * accuracy + 1) * unit * d)
    (hround : scale * rounded ≤ cost + scale * hops) :
    accuracy * (scale * rounded / unit) ≤ (accuracy + 1) * d := by
  have hf := Nat.div_mul_le_self (scale * rounded) unit
  have hff := Nat.mul_le_mul_left (5 * accuracy) hf
  have hr := Nat.mul_le_mul_left (5 * accuracy) hround
  have hs := Nat.mul_le_mul_left scale hspace
  have hd := Nat.mul_le_mul_right unit hscale
  have hpos : 0 ≤ unit * d := Nat.zero_le _
  have hb : (5 * unit) * (accuracy * (scale * rounded / unit)) ≤ (5 * unit) * ((accuracy + 1) * d) := by
    nlinarith only [hff, hr, hs, hd, hcost, hpos]
  by_contra hn
  have hlt : (accuracy + 1) * d < accuracy * (scale * rounded / unit) := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hlt (show 0 < 5 * unit by positivity)
  omega

theorem rounded_radius_bound (unit hops scale d cost rounded : ℕ) (hscale : 0 < scale)
    (hbracket : d < 2 * scale) (hhops : hops ≤ unit)
    (hcost : cost ≤ 2 * unit * d) (hround : scale * rounded ≤ cost + scale * hops) :
    rounded ≤ 8 * unit := by
  have hd := Nat.mul_le_mul_left (2 * unit) hbracket.le
  have hh := Nat.mul_le_mul_left scale hhops
  have hb : scale * rounded ≤ scale * (8 * unit) := by nlinarith only [hd, hh, hcost, hround]
  by_contra hn
  have hlt : 8 * unit < rounded := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hlt hscale
  omega

end

end StreamingReachability.Approx
