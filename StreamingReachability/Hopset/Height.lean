module

public import Mathlib

@[expose] public section

namespace StreamingReachability.Parameters

def firstCross (base factor target : ℕ) : ℕ → ℕ
  | 0 => 0
  | fuel + 1 =>
      if target ≤ base then 0 else firstCross (base * factor) factor target fuel + 1

theorem firstCross_le (base factor target fuel : ℕ) :
    firstCross base factor target fuel ≤ fuel := by
  induction fuel generalizing base with
  | zero => rfl
  | succ fuel ih =>
      simp only [firstCross]
      split_ifs
      · omega
      · exact Nat.succ_le_succ (ih (base * factor))

theorem firstCross_large (base factor target fuel : ℕ)
    (h : target ≤ base * factor ^ fuel) :
    target ≤ base * factor ^ firstCross base factor target fuel := by
  induction fuel generalizing base with
  | zero => simpa [firstCross] using h
  | succ fuel ih =>
      simp only [firstCross]
      split_ifs with hs
      · simpa using hs
      · have hr : target ≤ (base * factor) * factor ^ fuel := by
          calc
            target ≤ base * factor ^ (fuel + 1) := h
            _ = (base * factor) * factor ^ fuel := by rw [pow_succ]; ring
        have hh := ih (base * factor) hr
        simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

theorem firstCross_small (base factor target fuel : ℕ) :
    ∀ j < firstCross base factor target fuel, base * factor ^ j < target := by
  induction fuel generalizing base with
  | zero => simp [firstCross]
  | succ fuel ih =>
      intro j hj
      simp only [firstCross] at hj
      split_ifs at hj with hs
      · omega
      · cases j with
        | zero => simpa using Nat.lt_of_not_ge hs
        | succ j =>
            have hj' : j < firstCross (base * factor) factor target fuel := by omega
            have hh := ih (base * factor) j hj'
            simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

theorem firstCross_unique (base factor target fuel r : ℕ)
    (h : target ≤ base * factor ^ fuel)
    (hr : target ≤ base * factor ^ r)
    (hprev : ∀ j < r, base * factor ^ j < target) :
    firstCross base factor target fuel = r := by
  have hc := firstCross_large base factor target fuel h
  rcases lt_trichotomy (firstCross base factor target fuel) r with hlt | he | hgt
  · have hh := hprev _ hlt
    omega
  · exact he
  · have hh := firstCross_small base factor target fuel r hgt
    omega

def ell (n : ℕ) : ℕ := n.log2 + 1

theorem ell_pos (n : ℕ) : 0 < ell n := by unfold ell; omega

theorem lt_two_pow_ell (n : ℕ) : n < 2 ^ ell n := Nat.lt_log2_self

theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hp : 0 < 2 ^ n := by positivity
      rw [pow_succ]
      omega

def maxLevel (n k ell : ℕ) : ℕ := firstCross (100 * k * ell) k n n

theorem maxLevel_large (n k ell : ℕ) (hk : 2 ≤ k) (he : 0 < ell) :
    n ≤ 100 * k ^ (maxLevel n k ell + 1) * ell := by
  have hbase : 1 ≤ 100 * k * ell := by nlinarith
  have hpow : 2 ^ n ≤ k ^ n := by gcongr
  have hf : n ≤ (100 * k * ell) * k ^ n :=
    (nat_le_two_pow n).trans (hpow.trans (Nat.le_mul_of_pos_left _ hbase))
  have h := firstCross_large (100 * k * ell) k n n hf
  simpa only [maxLevel, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

theorem maxLevel_small (n k ell : ℕ) {r : ℕ} (hr : r < maxLevel n k ell) :
    100 * k ^ (r + 1) * ell < n := by
  have h := firstCross_small (100 * k * ell) k n n r hr
  simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

theorem maxLevel_le_ell (n k e : ℕ) (hk : 2 ≤ k) (he : 0 < e) :
    maxLevel n k e ≤ ell n := by
  by_contra h
  have hr : ell n < maxLevel n k e := by omega
  have hs := maxLevel_small n k e hr
  have hp : 2 ^ ell n ≤ k ^ (ell n + 1) := by
    calc
      2 ^ ell n ≤ k ^ ell n := by gcongr
      _ ≤ k ^ (ell n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : k ^ (ell n + 1) ≤ 100 * k ^ (ell n + 1) * e := by
    have hcoeff : 1 ≤ 100 * e := by omega
    have hh := Nat.mul_le_mul_right (k ^ (ell n + 1)) hcoeff
    simpa only [one_mul, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh
  have hh := (lt_two_pow_ell n).trans_le (hp.trans hm)
  omega

theorem power_maxLevel_le (n k e : ℕ) (hn : 0 < n) (hk : 2 ≤ k) (he : 0 < e) :
    k ^ maxLevel n k e ≤ n := by
  by_cases hz : maxLevel n k e = 0
  · simp only [hz, pow_zero]
    omega
  · have hpos : 0 < maxLevel n k e := Nat.pos_of_ne_zero hz
    have hr : maxLevel n k e - 1 < maxLevel n k e := by omega
    have hs := maxLevel_small n k e hr
    have hc : k ≤ 100 * k * e := by nlinarith
    have hp : k ^ maxLevel n k e ≤ (100 * k * e) * k ^ (maxLevel n k e - 1) := by
      calc
        k ^ maxLevel n k e = k * k ^ (maxLevel n k e - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hpos]
          rw [pow_succ]
          ring
        _ ≤ _ := Nat.mul_le_mul_right _ hc
    have hh : (100 * k * e) * k ^ (maxLevel n k e - 1) < n := by
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] using hs
    exact (hp.trans_lt hh).le

end StreamingReachability.Parameters
