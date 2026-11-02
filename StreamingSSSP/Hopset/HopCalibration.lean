module

public import StreamingSSSP.Hopset.EarlyPathProbability

@[expose] public section

namespace StreamingSSSP.Parameters

theorem threshold_split_power (n x : ℕ) (hx : 0 < x) :
    split n ^ threshold n x ≤ 2 * split n * (Nat.sqrt (ceilDiv n x) + 1) := by
  have hb : 0 < split n := split_pos n
  have hk : 0 < k n := by have h := k_large n; omega
  by_cases hz : threshold n x = 0
  · simp only [hz, pow_zero]
    nlinarith
  · let r := threshold n x
    let b := split n
    let Q := ceilDiv n x
    have hr : r - 1 < firstCross x (k n) (4 * n) (4 * n) := by
      have h := Nat.min_le_right (maximumLevel n) (firstCross x (k n) (4 * n) (4 * n))
      change r ≤ _ at h
      omega
    have hp := firstCross_small x (k n) (4 * n) (4 * n) (r - 1) hr
    have hpower : x * k n ^ r < 4 * k n * n := by
      calc
        x * k n ^ r = (x * k n ^ (r - 1)) * k n := by
          have hre : (r - 1) + 1 = r := by dsimp only [r]; omega
          conv_lhs => rw [← hre, pow_succ]
          ring
        _ < (4 * n) * k n := Nat.mul_lt_mul_of_pos_right hp hk
        _ = _ := by ring
    have heq : (b ^ r) ^ 2 = k n ^ r := by
      change (split n ^ r) ^ 2 = (split n ^ 2) ^ r
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    have hnQ : n ≤ x * Q := le_mul_ceilDiv n x hx
    have hsquare : (b ^ r) ^ 2 < 4 * b ^ 2 * Q := by
      by_contra hn
      have hlow : 4 * b ^ 2 * Q ≤ (b ^ r) ^ 2 := by omega
      have hm := Nat.mul_le_mul_left x hlow
      rw [← heq] at hpower
      have hkn : k n = b ^ 2 := rfl
      rw [hkn] at hpower
      have hupper := Nat.mul_le_mul_left (4 * b ^ 2) hnQ
      nlinarith
    have hroot := Nat.lt_succ_sqrt Q
    have hscale := Nat.mul_lt_mul_of_pos_left hroot (show 0 < 4 * b ^ 2 by dsimp only [b]; positivity)
    have hfull : (b ^ r) ^ 2 < (2 * b * (Nat.sqrt Q + 1)) ^ 2 := by nlinarith
    change b ^ r ≤ 2 * b * (Nat.sqrt Q + 1)
    by_contra hn
    have hlow : (2 * b * (Nat.sqrt Q + 1)) ^ 2 ≤ (b ^ r) ^ 2 := by
      gcongr
      omega
    omega

noncomputable section

open Hopset.Following

theorem pathScale_log_square (n accuracy : ℕ) :
    pathScale n accuracy * (ell n : ℝ) ^ 2 ≤ centerDenominator n accuracy := by
  have he : (0 : ℝ) < ell n := by exact_mod_cast ell_pos n
  have he₁ : (1 : ℝ) ≤ ell n := by exact_mod_cast (show 1 ≤ ell n from ell_pos n)
  have hc : (0 : ℝ) ≤ centerDenominator n accuracy := Nat.cast_nonneg _
  change ((centerDenominator n accuracy : ℝ) / (ell n : ℝ) ^ 3) * (ell n : ℝ) ^ 2 ≤ _
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos he 3)).mpr
  have hh : (ell n : ℝ) ^ 2 ≤ (ell n : ℝ) ^ 3 :=
    pow_le_pow_right₀ he₁ (by omega)
  exact mul_le_mul_of_nonneg_left hh hc

theorem threshold_piece_budget (n accuracy x : ℕ) (hx : 0 < x) :
    pieceThreshold (pathScale n accuracy) (split n : ℝ) (ell n : ℝ) (threshold n x) ≤
      16384 * (100 : ℝ) ^ (advance n accuracy + threshold n x) *
        (split n : ℝ) ^ (advance n accuracy + 1) * (Nat.sqrt (ceilDiv n x) + 1 : ℕ) := by
  let r := threshold n x
  let L := advance n accuracy
  let b : ℝ := split n
  let S : ℝ := ((Nat.sqrt (ceilDiv n x) + 1 : ℕ) : ℝ)
  have hb : 0 < b := by dsimp only [b]; exact_mod_cast split_pos n
  have hs : b ^ r ≤ 2 * b * S := by
    change (split n : ℝ) ^ threshold n x ≤ 2 * (split n : ℝ) * ((Nat.sqrt (ceilDiv n x) + 1 : ℕ) : ℝ)
    exact_mod_cast threshold_split_power n x hx
  have hL : 1 ≤ L := by have h := advance_large n accuracy; dsimp only [L]; omega
  have hc := pathScale_log_square n accuracy
  have hmult := mul_le_mul_of_nonneg_right hc (show 0 ≤ 8192 * (100 * b) ^ r * b by positivity)
  have hcenter : (centerDenominator n accuracy : ℝ) * b = (100 : ℝ) ^ L * b ^ L := by
    change ((100 ^ L * split n ^ (L - 1) : ℕ) : ℝ) * b = _
    push_cast
    change (100 : ℝ) ^ L * b ^ (L - 1) * b = (100 : ℝ) ^ L * b ^ L
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hL]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8192 * (100 : ℝ) ^ r * (100 : ℝ) ^ L * b ^ L by positivity)
  change pieceThreshold (pathScale n accuracy) b (ell n : ℝ) r ≤ 16384 * (100 : ℝ) ^ (L + r) * b ^ (L + 1) * S
  unfold pieceThreshold
  have hfirst :
      8192 * pathScale n accuracy * (100 * b) ^ r * b * (ell n : ℝ) ^ 2 ≤
        8192 * (100 : ℝ) ^ r * (100 : ℝ) ^ L * b ^ L * b ^ r := by
    calc
      _ ≤ (centerDenominator n accuracy : ℝ) * (8192 * (100 * b) ^ r * b) := by nlinarith
      _ = 8192 * (100 : ℝ) ^ r * ((centerDenominator n accuracy : ℝ) * b) * b ^ r := by rw [mul_pow]; ring
      _ = _ := by rw [hcenter]; ring
  rw [pow_add (100 : ℝ) L r, pow_succ b L]
  nlinarith

theorem combined_hop_budget (n accuracy x : ℕ) (hx : 0 < x) :
    (4 * ((ell n : ℝ) + 1) + 32 * (14 : ℝ) ^ (maximumLevel n - threshold n x + 1)) *
        pieceThreshold (pathScale n accuracy) (split n : ℝ) (ell n : ℝ) (threshold n x) ≤
      (hopBound n accuracy x : ℝ) := by
  let r := threshold n x
  let R := maximumLevel n
  let L := advance n accuracy
  let b : ℝ := split n
  let S : ℝ := ((Nat.sqrt (ceilDiv n x) + 1 : ℕ) : ℝ)
  let T := pieceThreshold (pathScale n accuracy) b (ell n : ℝ) r
  let U := 16384 * (100 : ℝ) ^ (L + r) * b ^ (L + 1) * S
  let V := (100 : ℝ) ^ (L + R) * b ^ (L + 3) * S
  have hr : r ≤ R := Nat.min_le_left _ _
  have hb : (1 : ℝ) ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ split n from split_pos n)
  have hs : 0 ≤ S := Nat.cast_nonneg _
  have ht : 0 ≤ T := by
    have hc : 0 ≤ pathScale n accuracy := by unfold pathScale; positivity
    dsimp only [T, pieceThreshold]
    positivity
  have hu : 0 ≤ U := by dsimp only [U]; positivity
  have hv : 0 ≤ V := by dsimp only [V]; positivity
  have hTU : T ≤ U := threshold_piece_budget n accuracy x hx
  have he : (ell n : ℝ) + 1 ≤ 2 * b ^ 2 := by
    have hlog : (ell n : ℝ) ≤ b ^ 2 := by
      dsimp only [b]
      exact_mod_cast (show ell n ≤ split n ^ 2 from logarithm_le_k n)
    have he₁ : (1 : ℝ) ≤ ell n := by exact_mod_cast (show 1 ≤ ell n from ell_pos n)
    linarith
  have h100 : (100 : ℝ) ^ (L + r) ≤ (100 : ℝ) ^ (L + R) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hbpow : b ^ (L + 1) ≤ b ^ (L + 3) := pow_le_pow_right₀ hb (by omega)
  have h14 : (14 : ℝ) ^ (R - r + 1) ≤ (100 : ℝ) ^ (R - r + 1) := by gcongr; norm_num
  have hproduct : (100 : ℝ) ^ (R - r + 1) * (100 : ℝ) ^ (L + r) =
      (100 : ℝ) ^ (L + R + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hbproduct : b ^ 2 * b ^ (L + 1) = b ^ (L + 3) := by
    rw [← pow_add]
    congr 1
    omega
  have hearly : 4 * ((ell n : ℝ) + 1) * T ≤ 131072 * V := by
    calc
      _ ≤ (8 * b ^ 2) * U := by
        apply mul_le_mul
        · linarith
        · exact hTU
        · exact ht
        · positivity
      _ = 131072 * (100 : ℝ) ^ (L + r) * b ^ (L + 3) * S := by
        dsimp only [U]
        calc
          _ = 131072 * (100 : ℝ) ^ (L + r) * (b ^ 2 * b ^ (L + 1)) * S := by ring
          _ = _ := by rw [hbproduct]
      _ ≤ 131072 * (100 : ℝ) ^ (L + R) * b ^ (L + 3) * S := by gcongr
      _ = 131072 * V := by dsimp only [V]; ring
  have hlate : 32 * (14 : ℝ) ^ (R - r + 1) * T ≤ 52428800 * V := by
    calc
      _ ≤ 32 * (100 : ℝ) ^ (R - r + 1) * U := by gcongr
      _ = 524288 * (100 : ℝ) ^ (L + R + 1) * b ^ (L + 1) * S := by
        dsimp only [U]
        calc
          _ = 524288 * ((100 : ℝ) ^ (R - r + 1) * (100 : ℝ) ^ (L + r)) * b ^ (L + 1) * S := by ring
          _ = _ := by rw [hproduct]
      _ ≤ 524288 * (100 : ℝ) ^ (L + R + 1) * b ^ (L + 3) * S := by gcongr
      _ = 52428800 * V := by dsimp only [V]; rw [pow_succ (100 : ℝ) (L + R)]; ring
  have hhop : (hopBound n accuracy x : ℝ) = 2 ^ 30 * 100 ^ 2 * V := by
    simp only [hopBound, Nat.cast_mul, Nat.cast_pow]
    change (2 : ℝ) ^ 30 * (100 : ℝ) ^ (L + R + 2) * b ^ (L + 3) * S = _
    rw [pow_add (100 : ℝ) (L + R) 2]
    dsimp only [V]
    ring
  change (4 * ((ell n : ℝ) + 1) + 32 * (14 : ℝ) ^ (R - r + 1)) * T ≤ _
  rw [hhop]
  nlinarith

end

end StreamingSSSP.Parameters
