module

public import StreamingReachability.Hopset.CubeCalibration

@[expose] public section

namespace StreamingReachability.Parameters

theorem firstCross_upper (base factor target fuel bound : ℕ)
    (h : target ≤ base * factor ^ bound) :
    firstCross base factor target fuel ≤ bound := by
  by_contra hb
  have hs := firstCross_small base factor target fuel bound (by omega)
  omega

theorem advance_upper (n accuracy coefficient : ℕ)
    (ha : accuracy ≤ coefficient * ell n) :
    advance n accuracy ≤ 40 * coefficient + 21 := by
  have hk : 2 ≤ k n := by have h := k_large n; omega
  have hconstant : 20 * coefficient ≤ k n ^ (20 * coefficient) :=
    (nat_le_two_pow _).trans (Nat.pow_le_pow_left hk _)
  have he : ell n ^ 2 ≤ k n ^ 2 := Nat.pow_le_pow_left (logarithm_le_k n) 2
  have hd : accuracyDenominator n accuracy ≤ k n ^ (20 * coefficient + 2) := by
    calc
      _ ≤ 20 * (coefficient * ell n) * ell n := by
        unfold accuracyDenominator
        gcongr
      _ = (20 * coefficient) * ell n ^ 2 := by ring
      _ ≤ k n ^ (20 * coefficient) * k n ^ 2 := Nat.mul_le_mul hconstant he
      _ = _ := (pow_add _ _ _).symm
  have ht : accuracyDenominator n accuracy ^ 2 ≤ 1 * k n ^ (40 * coefficient + 4) := by
    calc
      _ ≤ (k n ^ (20 * coefficient + 2)) ^ 2 := Nat.pow_le_pow_left hd 2
      _ = _ := by rw [← pow_mul]; congr 1 <;> ring
  have hc := firstCross_upper 1 (k n) (accuracyDenominator n accuracy ^ 2)
    (accuracyDenominator n accuracy ^ 2) (40 * coefficient + 4) ht
  unfold advance
  omega

theorem split_upper (n : ℕ) : split n ≤ 4097 * ell n := by
  have hs := Nat.sqrt_le_self (4096 * ell n)
  have he := ell_pos n
  unfold split
  omega

theorem k_upper (n : ℕ) : k n ≤ 16785409 * ell n ^ 2 := by
  have h := Nat.pow_le_pow_left (split_upper n) 2
  simpa only [k] using h.trans_eq (by ring)

theorem ceilDiv_cube (n : ℕ) (hn : 0 < n) :
    ceilDiv n (blockSize n) ≤ blockSize n ^ 2 := by
  have hx := blockSize_pos n
  have hc := blockSize_cube_ge n hn
  unfold ceilDiv
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul hx]
  have he : (blockSize n ^ 2).succ * blockSize n = blockSize n ^ 3 + blockSize n := by
    simp only [Nat.succ_eq_add_one]
    ring
  rw [he]
  omega

theorem cube_sqrt_ceilDiv (n : ℕ) (hn : 0 < n) :
    Nat.sqrt (ceilDiv n (blockSize n)) + 1 ≤ 2 * blockSize n := by
  have hs := Nat.sqrt_le_sqrt (ceilDiv_cube n hn)
  rw [Nat.sqrt_eq'] at hs
  have hx := blockSize_pos n
  omega

theorem logarithm_eventually_large (bound : ℕ) :
    ∀ n ≥ 2 ^ bound, bound ≤ ell n := by
  intro n hn
  have hp : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ bound) hn
  have hlog : bound ≤ n.log2 := (Nat.le_log2 (Nat.ne_of_gt hp)).mpr hn
  unfold ell
  omega

/-- This is the finite inequality underlying the subpolynomial height factor;
no asymptotic assumption is an input to the algorithm. -/
theorem height_subpower (power n : ℕ) (hn : 2 ^ (100 ^ power) ≤ n) :
    (100 ^ maximumLevel n) ^ power ≤ n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ (100 ^ power)) hn
  have hk : 100 ^ power ≤ k n :=
    (logarithm_eventually_large (100 ^ power) n hn).trans (logarithm_le_k n)
  calc
    _ = (100 ^ power) ^ maximumLevel n := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ k n ^ maximumLevel n := Nat.pow_le_pow_left hk _
    _ ≤ n := power_maximumLevel_le n hnpos

theorem cube_hop_upper (n accuracy coefficient : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) :
    hopBound n accuracy (blockSize n) ≤
      (2 ^ 31 * 100 ^ (40 * coefficient + 23) * 4097 ^ (40 * coefficient + 24)) *
        blockSize n * ell n ^ (40 * coefficient + 24) * 100 ^ maximumLevel n := by
  have hL := advance_upper n accuracy coefficient ha
  have hb := split_upper n
  have hs : 1 ≤ split n := split_pos n
  have h100 : 100 ^ (advance n accuracy + maximumLevel n + 2) ≤
      100 ^ (40 * coefficient + 23) * 100 ^ maximumLevel n := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hsplit : split n ^ (advance n accuracy + 3) ≤
      4097 ^ (40 * coefficient + 24) * ell n ^ (40 * coefficient + 24) := by
    calc
      _ ≤ split n ^ (40 * coefficient + 24) := Nat.pow_le_pow_right hs (by omega)
      _ ≤ (4097 * ell n) ^ (40 * coefficient + 24) := Nat.pow_le_pow_left hb _
      _ = _ := mul_pow _ _ _
  have hr := cube_sqrt_ceilDiv n hn
  unfold hopBound
  calc
    _ ≤ 2 ^ 30 * (100 ^ (40 * coefficient + 23) * 100 ^ maximumLevel n) *
        (4097 ^ (40 * coefficient + 24) * ell n ^ (40 * coefficient + 24)) *
        (2 * blockSize n) := by gcongr
    _ = _ := by rw [pow_succ]; ring

end StreamingReachability.Parameters
