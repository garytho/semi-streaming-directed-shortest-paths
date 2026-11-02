module

public import StreamingSSSP.Hopset.RecordBudget

@[expose] public section

namespace StreamingSSSP.Parameters

open scoped Classical

theorem levels_plus_one_le (n : ℕ) : maximumLevel n + 1 ≤ 2 * ell n := by
  have h := maximumLevel_le_logarithm n
  have he := ell_pos n
  omega

theorem copy_mean_slack (n : ℕ) :
    1024 * (2 * (n : ℝ) * ((maximumLevel n + 1 : ℕ) : ℝ)) ≤
      ((2 ^ 30 * n * ell n ^ 4 : ℕ) : ℝ) := by
  have hp : ell n ≤ ell n ^ 4 := by
    simpa using Nat.pow_le_pow_right (ell_pos n) (by norm_num : 1 ≤ 4)
  have h : 1024 * (2 * n * (maximumLevel n + 1)) ≤ 2 ^ 30 * n * ell n ^ 4 := by
    calc
      _ ≤ 1024 * (2 * n * (2 * ell n)) := by gcongr; exact levels_plus_one_le n
      _ = 4096 * n * ell n := by ring
      _ ≤ 4096 * n * ell n ^ 4 := by gcongr
      _ ≤ _ := by gcongr <;> norm_num
  exact_mod_cast h

theorem block_mean_slack (n : ℕ) :
    1024 * ((400 * (k n : ℝ) * ell n) * (2 * ((maximumLevel n + 1 : ℕ) : ℝ)) * n) ≤
      ((2 ^ 30 * n * k n * ell n ^ 4 : ℕ) : ℝ) := by
  have hp : ell n ^ 2 ≤ ell n ^ 4 :=
    Nat.pow_le_pow_right (ell_pos n) (by norm_num)
  have h : 1024 * ((400 * k n * ell n) * (2 * (maximumLevel n + 1)) * n) ≤
      2 ^ 30 * n * k n * ell n ^ 4 := by
    calc
      _ ≤ 1024 * ((400 * k n * ell n) * (2 * (2 * ell n)) * n) := by
        gcongr
        exact levels_plus_one_le n
      _ = 1638400 * n * k n * ell n ^ 2 := by ring
      _ ≤ 1638400 * n * k n * ell n ^ 4 := by gcongr
      _ ≤ _ := by gcongr <;> norm_num
  exact_mod_cast h

theorem record_mean_slack (n accuracy blockVolume : ℕ) :
    1024 * (400 * (k n : ℝ) ^ advance n accuracy * ell n * (n + blockVolume) +
      StreamingSSSP.Hopset.Reference.recordVisitBudget n accuracy *
        (2 * ((maximumLevel n + 1 : ℕ) : ℝ)) * (n + blockVolume)) ≤
      ((2 ^ 30 * k n ^ (advance n accuracy + 2) * ell n ^ 4 * (n + blockVolume) : ℕ) : ℝ) := by
  have hk : 1 ≤ k n := by have := k_large n; omega
  have hpow₀ : k n ^ advance n accuracy ≤ k n ^ (advance n accuracy + 2) :=
    Nat.pow_le_pow_right hk (by omega)
  have hpow₁ : k n ^ (advance n accuracy + 1) ≤ k n ^ (advance n accuracy + 2) :=
    Nat.pow_le_pow_right hk (by omega)
  have he₁ : ell n ≤ ell n ^ 4 := by
    simpa using Nat.pow_le_pow_right (ell_pos n) (by norm_num : 1 ≤ 4)
  have he₂ : ell n ^ 2 ≤ ell n ^ 4 :=
    Nat.pow_le_pow_right (ell_pos n) (by norm_num)
  let H := k n ^ (advance n accuracy + 2) * ell n ^ 4 * (n + blockVolume)
  have hg : 400 * k n ^ advance n accuracy * ell n * (n + blockVolume) ≤ 400 * H := by
    dsimp only [H]
    calc
      _ ≤ 400 * k n ^ (advance n accuracy + 2) * ell n ^ 4 * (n + blockVolume) := by gcongr
      _ = _ := by ring
  have ht : (1000 * k n ^ (advance n accuracy + 1) * ell n) *
      (2 * (maximumLevel n + 1)) * (n + blockVolume) ≤ 4000 * H := by
    calc
      _ ≤ (1000 * k n ^ (advance n accuracy + 1) * ell n) *
          (2 * (2 * ell n)) * (n + blockVolume) := by
        gcongr
        exact levels_plus_one_le n
      _ = 4000 * k n ^ (advance n accuracy + 1) * ell n ^ 2 * (n + blockVolume) := by ring
      _ ≤ 4000 * k n ^ (advance n accuracy + 2) * ell n ^ 4 * (n + blockVolume) := by gcongr
      _ = _ := by dsimp [H]; ring
  have h : 1024 * (400 * k n ^ advance n accuracy * ell n * (n + blockVolume) +
      (1000 * k n ^ (advance n accuracy + 1) * ell n) *
        (2 * (maximumLevel n + 1)) * (n + blockVolume)) ≤
      2 ^ 30 * k n ^ (advance n accuracy + 2) * ell n ^ 4 * (n + blockVolume) := by
    calc
      _ ≤ 1024 * (400 * H + 4000 * H) := Nat.mul_le_mul_left _ (Nat.add_le_add hg ht)
      _ = 4505600 * H := by ring
      _ ≤ 2 ^ 30 * H := Nat.mul_le_mul_right _ (by norm_num)
      _ = _ := by dsimp [H]; ring
  unfold StreamingSSSP.Hopset.Reference.recordVisitBudget
  exact_mod_cast h

theorem inverse_tenth_small (n : ℕ) (hn : 2 ≤ n) : 1 / (n : ℝ) ^ 10 ≤ 1 / 1024 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1024 : ℝ) ≤ (n : ℝ) ^ 10 := by
    calc
      1024 = (2 : ℝ) ^ 10 := by norm_num
      _ ≤ (n : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hnR _
  exact one_div_le_one_div_of_le (by norm_num) hp

end StreamingSSSP.Parameters
