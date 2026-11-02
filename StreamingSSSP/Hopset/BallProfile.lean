module

public import StreamingSSSP.Hopset.Calibration
public import StreamingSSSP.Hopset.BallProbability

@[expose] public section

namespace StreamingSSSP.Parameters

open scoped Classical

def ballSize (n r : ℕ) : ℕ := 2 * n / k n ^ r

theorem ballSize_succ (n r : ℕ) : ballSize n r / k n = ballSize n (r + 1) := by
  simp only [ballSize, Nat.div_div_eq_div_mul, pow_succ]

theorem doubled_quotient_covers (n d : ℕ) (hd : 0 < d) (hdn : d ≤ n) :
    n ≤ (2 * n / d) * d := by
  have hr := Nat.mod_lt (2 * n) hd
  have he := Nat.div_add_mod (2 * n) d
  rw [Nat.mul_comm d] at he
  omega

theorem level_power_le (n : ℕ) (hn : 0 < n) (r : ℕ) (hr : r ≤ maximumLevel n) :
    k n ^ r ≤ n :=
  (Nat.pow_le_pow_right (by have := k_large n; omega) hr).trans
    (power_maximumLevel_le n hn)

theorem ballSize_pos (n : ℕ) (hn : 0 < n) (r : ℕ) (hr : r ≤ maximumLevel n) :
    0 < ballSize n r := by
  have hk : 0 < k n := by have := k_large n; omega
  have hd : 0 < k n ^ r := by positivity
  change 1 ≤ 2 * n / k n ^ r
  apply (Nat.le_div_iff_mul_le hd).mpr
  simpa only [one_mul] using (level_power_le n hn r hr).trans
    (show n ≤ 2 * n by omega)

theorem ball_rate_upper (n : ℕ) (hn : 0 < n) (r : ℕ) :
    (ballSize n r : ℝ) * (PivotProfile.rate n hn (k n) (ell n) r).value ≤
      200 * k n * ell n := by
  have hnat : ballSize n r * min (100 * k n ^ (r + 1) * ell n) n ≤
      200 * k n * ell n * n := by
    calc
      _ ≤ ballSize n r * (100 * k n ^ (r + 1) * ell n) :=
        Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
      _ = (ballSize n r * k n ^ r) * (100 * k n * ell n) := by rw [pow_succ]; ring
      _ ≤ (2 * n) * (100 * k n * ell n) :=
        Nat.mul_le_mul_right _ (Nat.div_mul_le_self (2 * n) (k n ^ r))
      _ = _ := by ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (ballSize n r : ℝ) *
    (((min (100 * k n ^ (r + 1) * ell n) n : ℕ) : ℝ) / n) ≤ _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnR).mpr
  exact_mod_cast hnat

theorem future_ball_rate_upper (n : ℕ) (hn : 0 < n) (r delay : ℕ) :
    (ballSize n r : ℝ) * (PivotProfile.rate n hn (k n) (ell n) (r + delay)).value ≤
      200 * (k n : ℝ) ^ (delay + 1) * ell n := by
  have hnat : ballSize n r * min (100 * k n ^ (r + delay + 1) * ell n) n ≤
      200 * k n ^ (delay + 1) * ell n * n := by
    calc
      _ ≤ ballSize n r * (100 * k n ^ (r + delay + 1) * ell n) :=
        Nat.mul_le_mul_left _ (Nat.min_le_left _ _)
      _ = (ballSize n r * k n ^ r) * (100 * k n ^ (delay + 1) * ell n) := by
        rw [show r + delay + 1 = r + (delay + 1) by omega, pow_add]
        ring
      _ ≤ (2 * n) * (100 * k n ^ (delay + 1) * ell n) :=
        Nat.mul_le_mul_right _ (Nat.div_mul_le_self (2 * n) (k n ^ r))
      _ = _ := by ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change (ballSize n r : ℝ) *
    (((min (100 * k n ^ (r + delay + 1) * ell n) n : ℕ) : ℝ) / n) ≤ _
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnR).mpr
  exact_mod_cast hnat

theorem ball_rate_lower_next (n : ℕ) (hn : 0 < n) (r : ℕ)
    (hr : r < maximumLevel n) :
    100 * (ell n : ℝ) ≤
      (PivotProfile.rate n hn (k n) (ell n) r).value * ballSize n (r + 1) := by
  have hk : 0 < k n := by have := k_large n; omega
  have hd : 0 < k n ^ (r + 1) := by positivity
  have hcover := doubled_quotient_covers n (k n ^ (r + 1)) hd
    (level_power_le n hn (r + 1) (by omega))
  have hcoverR : (n : ℝ) ≤ (ballSize n (r + 1) : ℝ) * (k n : ℝ) ^ (r + 1) := by
    exact_mod_cast hcover
  have hnum := (maxLevel_small n (k n) (ell n) hr).le
  rw [PivotProfile.rate_value n hn (k n) (ell n) r hnum, div_mul_eq_mul_div]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ hnR).mpr
  have hmul := mul_le_mul_of_nonneg_right hcoverR
    (show (0 : ℝ) ≤ 100 * ell n by positivity)
  nlinarith

theorem rate_one_after_max (n : ℕ) (hn : 0 < n) (r : ℕ) (hr : maximumLevel n ≤ r) :
    (PivotProfile.rate n hn (k n) (ell n) r).value = 1 := by
  have hk : 1 ≤ k n := by have := k_large n; omega
  have hk2 : 2 ≤ k n := by have := k_large n; omega
  have hbase := maxLevel_large n (k n) (ell n) hk2 (ell_pos n)
  have hpower : k n ^ (maximumLevel n + 1) ≤ k n ^ (r + 1) :=
    Nat.pow_le_pow_right hk (by omega)
  have hnum : n ≤ 100 * k n ^ (r + 1) * ell n :=
    hbase.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpower))
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [PivotProfile.rate, Rate.value, Nat.min_eq_right hnum, hnR]

theorem type3_parameter_budget (n : ℕ) (hn : 0 < n) (r : ℕ) :
    48 * (ballSize n r : ℝ) * (PivotProfile.rate n hn (k n) (ell n) r).value /
        groups n ≤
      1 / (4 * 100 * k n * ell n) := by
  have hk : (0 : ℝ) < k n := by exact_mod_cast (show 0 < k n by have := k_large n; omega)
  have he : (0 : ℝ) < ell n := by exact_mod_cast ell_pos n
  have hM : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  apply (div_le_div_iff₀ hM (by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_right (ball_rate_upper n hn r)
    (show (0 : ℝ) ≤ 19200 * k n * ell n by positivity)
  norm_num only [groups, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, one_mul]
  nlinarith

theorem copy_growth_budget (n : ℕ) (hn : 0 < n) (r : ℕ) :
    8 * (ballSize n r : ℝ) * (PivotProfile.rate n hn (k n) (ell n) r).value /
        groups n ≤
      2 / (100 * ell n) := by
  have hk : (1 : ℝ) ≤ k n := by
    exact_mod_cast (show 1 ≤ k n by have := k_large n; omega)
  have he : (0 : ℝ) < ell n := by exact_mod_cast ell_pos n
  have hM : (0 : ℝ) < groups n := by exact_mod_cast groups_pos n
  apply (div_le_div_iff₀ hM (by positivity)).mpr
  have hmul := mul_le_mul_of_nonneg_right (ball_rate_upper n hn r)
    (show (0 : ℝ) ≤ 800 * ell n by positivity)
  have hbase := mul_nonneg (sub_nonneg.mpr hk)
    (show (0 : ℝ) ≤ (k n : ℝ) * (ell n : ℝ) ^ 2 by positivity)
  norm_num only [groups, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

theorem crossing_large (n x : ℕ) (hx : 0 < x) :
    4 * n ≤ x * k n ^ firstCross x (k n) (4 * n) (4 * n) := by
  have hk : 2 ≤ k n := by have := k_large n; omega
  apply firstCross_large
  calc
    4 * n ≤ 2 ^ (4 * n) := nat_le_two_pow _
    _ ≤ k n ^ (4 * n) := by gcongr
    _ ≤ _ := Nat.le_mul_of_pos_left _ hx

theorem late_block_size_budget (n x r : ℕ) (hx : 0 < x)
    (hpoly : 4 * 100 * k n * ell n ≤ x)
    (hr0 : threshold n x ≤ r) (hr : r ≤ maximumLevel n) :
    2 * ballSize n r ≤ x := by
  have hk : 0 < k n := by have := k_large n; omega
  have hk2 : 2 ≤ k n := by have := k_large n; omega
  have hp : 0 < k n ^ r := by positivity
  have hball : ballSize n r * k n ^ r ≤ 2 * n := Nat.div_mul_le_self _ _
  by_cases hlast : maximumLevel n ≤ firstCross x (k n) (4 * n) (4 * n)
  · have hthreshold : threshold n x = maximumLevel n := Nat.min_eq_left hlast
    have hre : r = maximumLevel n := by omega
    have hlarge := maxLevel_large n (k n) (ell n) hk2 (ell_pos n)
    change n ≤ 100 * k n ^ (maximumLevel n + 1) * ell n at hlarge
    have hnum : 2 * n ≤ k n ^ r * (200 * k n * ell n) := by
      rw [← hre] at hlarge
      rw [pow_succ] at hlarge
      nlinarith
    have hb : ballSize n r ≤ 200 * k n * ell n := Nat.div_le_of_le_mul hnum
    nlinarith
  · have hthreshold : threshold n x = firstCross x (k n) (4 * n) (4 * n) :=
      Nat.min_eq_right (by omega)
    have hlarge := crossing_large n x hx
    have hlevel : firstCross x (k n) (4 * n) (4 * n) ≤ r := by omega
    have hnext : 4 * n ≤ x * k n ^ r :=
      hlarge.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hlevel))
    by_contra hb
    have hstrict : x * k n ^ r < (2 * ballSize n r) * k n ^ r :=
      Nat.mul_lt_mul_of_pos_right (by omega) hp
    nlinarith

theorem related_parameter_budget (n : ℕ) (hn : 0 < n) (r : ℕ) :
    2 * (ballSize n r : ℝ) * ballSize n r *
        (PivotProfile.rate n hn (k n) (ell n) r).value ^ 2 ≤
      (k n : ℝ) * groups n := by
  have hk : (1 : ℝ) ≤ k n := by
    exact_mod_cast (show 1 ≤ k n by have := k_large n; omega)
  have hp := (PivotProfile.rate n hn (k n) (ell n) r).value_nonneg
  have hsquare :
      ((ballSize n r : ℝ) * (PivotProfile.rate n hn (k n) (ell n) r).value) ^ 2 ≤
        (200 * (k n : ℝ) * ell n) ^ 2 := by
    gcongr 1
    exact ball_rate_upper n hn r
  have hbase : 0 ≤ ((k n : ℝ) - 1) * ((k n : ℝ) ^ 2 * (ell n : ℝ) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hk) (by positivity)
  norm_num only [groups, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  nlinarith

theorem early_prefix_half (n : ℕ) (hn : 0 < n) (x r : ℕ) (hr : r < threshold n x) :
    (((PivotProfile.rates n hn (k n) (ell n) (threshold n x)).take r).map Rate.value).sum ≤
      1 / 2 := by
  have hrmax : r < maximumLevel n := hr.trans_le (threshold_le_maximum n x)
  exact PivotProfile.prefix_half_take n hn (k n) (ell n) (threshold n x) r
    (by have := k_large n; omega) (by omega)
    (maxLevel_small n (k n) (ell n) hrmax).le

theorem early_ball_failure (n : ℕ) (hn : 0 < n) (x r : ℕ) (hr : r < threshold n x)
    (history : List (CopyHistory.Observation n)) (S : Finset (Fin n))
    (Ain Aout : Fin n → Finset (Fin n)) (Rin Rout : Fin n → Fin n → Prop)
    (hin : ∀ v ∈ S, Ain v ⊆ S) (hout : ∀ v ∈ S, Aout v ⊆ S)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r) :
    (CopyHistory.law (PivotProfile.rates n hn (k n) (ell n) (threshold n x)) history).prob
        (fun ranks => ∃ v ∈ S,
          ¬ CopyHistory.Hits (Ain v) Rin (ballSize n (r + 1)) r ranks ∨
            ¬ CopyHistory.Hits (Aout v) Rout (ballSize n (r + 1)) r ranks) ≤
      2 * (S.card : ℝ) ^ 2 * Real.exp (-25 * ell n) := by
  have hrlen : r < (PivotProfile.rates n hn (k n) (ell n) (threshold n x)).length := by
    simpa using hr
  have h := CopyHistory.two_direction_failure
    (PivotProfile.rates n hn (k n) (ell n) (threshold n x)) history S Ain Aout Rin Rout
    (ballSize n (r + 1)) r hin hout hrlen hc hp (early_prefix_half n hn x r hr)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [PivotProfile.lookup n hn (k n) (ell n) (threshold n x) r hr]
  have hlower := ball_rate_lower_next n hn r (hr.trans_le (threshold_le_maximum n x))
  nlinarith

end StreamingSSSP.Parameters
