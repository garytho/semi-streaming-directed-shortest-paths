module

public import StreamingReachability.Hopset.HopCalibration
public import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

@[expose] public section

namespace StreamingReachability.Parameters

def blockSize (n : ℕ) : ℕ := Nat.nthRoot 3 (n - 1) + 1

theorem blockSize_pos (n : ℕ) : 0 < blockSize n := by unfold blockSize; omega

theorem blockSize_cube_ge (n : ℕ) (hn : 0 < n) : n ≤ blockSize n ^ 3 := by
  have h := Nat.lt_pow_nthRoot_add_one (by decide : (3 : ℕ) ≠ 0) (n - 1)
  change n ≤ (Nat.nthRoot 3 (n - 1) + 1) ^ 3
  omega

theorem blockSize_minimal (n : ℕ) (hn : 0 < n) : (blockSize n - 1) ^ 3 < n := by
  have h := Nat.pow_nthRoot_le (n := 3) (a := n - 1) (Or.inl (by decide : (3 : ℕ) ≠ 0))
  have he : blockSize n - 1 = Nat.nthRoot 3 (n - 1) := by unfold blockSize; omega
  rw [he]
  omega

theorem blockSize_le_n (n : ℕ) (hn : 0 < n) : blockSize n ≤ n := by
  have h := Nat.pow_nthRoot_le (n := 3) (a := n - 1) (Or.inl (by decide : (3 : ℕ) ≠ 0))
  have hr := Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) (Nat.nthRoot 3 (n - 1))
  unfold blockSize
  omega

theorem hopBound_split_lower (n accuracy x : ℕ) :
    2 ^ 30 * k n ^ 10 ≤ hopBound n accuracy x := by
  have hb : 1 ≤ split n := split_pos n
  have hL := advance_large n accuracy
  have hp : k n ^ 10 ≤ split n ^ (advance n accuracy + 3) := by
    change (split n ^ 2) ^ 10 ≤ _
    rw [← pow_mul]
    exact pow_le_pow_right₀ hb (by omega)
  have h100 : 0 < 100 ^ (advance n accuracy + maximumLevel n + 2) := by positivity
  have hs : 0 < Nat.sqrt (ceilDiv n x) + 1 := by omega
  calc
    _ ≤ 2 ^ 30 * split n ^ (advance n accuracy + 3) := Nat.mul_le_mul_left _ hp
    _ ≤ (2 ^ 30 * 100 ^ (advance n accuracy + maximumLevel n + 2)) *
        split n ^ (advance n accuracy + 3) :=
      Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h100)
    _ ≤ _ := Nat.le_mul_of_pos_right _ hs

theorem cube_small_case_hops (n accuracy : ℕ) (hn : 0 < n)
    (hsmall : ¬ 4 * 100 * k n * ell n ≤ blockSize n) :
    n ≤ hopBound n accuracy (blockSize n) := by
  have hk : 1 ≤ k n := by have h := k_large n; omega
  change ¬ 400 * k n * ell n ≤ blockSize n at hsmall
  have hx : blockSize n ≤ 400 * k n * ell n := by omega
  have ht : 400 * k n * ell n ≤ 400 * k n ^ 2 := by
    have h := Nat.mul_le_mul_left (400 * k n) (logarithm_le_k n)
    nlinarith only [h]
  calc
    _ ≤ blockSize n ^ 3 := blockSize_cube_ge n hn
    _ ≤ (400 * k n ^ 2) ^ 3 := by gcongr; exact hx.trans ht
    _ = 64000000 * k n ^ 6 := by ring
    _ ≤ 2 ^ 30 * k n ^ 10 := by
      apply Nat.mul_le_mul
      · norm_num
      · exact pow_le_pow_right₀ hk (by omega)
    _ ≤ _ := hopBound_split_lower n accuracy (blockSize n)

theorem blockSize_cube_le (n : ℕ) (hn : 0 < n) : blockSize n ^ 3 ≤ 8 * n := by
  let r := Nat.nthRoot 3 (n - 1)
  have hr : r ^ 3 ≤ n - 1 := Nat.pow_nthRoot_le (Or.inl (by decide : (3 : ℕ) ≠ 0))
  change (r + 1) ^ 3 ≤ 8 * n
  by_cases hz : r = 0
  · rw [hz]
    norm_num
    omega
  · have hle : r + 1 ≤ 2 * r := by omega
    have hp : (r + 1) ^ 3 ≤ (2 * r) ^ 3 := by gcongr
    have hrn : r ^ 3 < n := by omega
    nlinarith only [hp, hrn]

theorem blockSize_workspace_eventual (n : ℕ) (hn : 513 ≤ n) : 2 * blockSize n * blockSize n ≤ n := by
  have hnpos : 0 < n := by omega
  let r := blockSize n - 1
  have hrCube : r ^ 3 < n := blockSize_minimal n hnpos
  have hge : 8 ≤ r := by
    by_contra h
    have hx : blockSize n ≤ 8 := by dsimp only [r] at h; omega
    have hp : blockSize n ^ 3 ≤ (8 : ℕ) ^ 3 := by gcongr
    have hlow := blockSize_cube_ge n hnpos
    norm_num at hp
    omega
  have hx : blockSize n ≤ 2 * r := by
    have hpos := blockSize_pos n
    dsimp only [r]
    omega
  have hsquare : blockSize n ^ 2 ≤ (2 * r) ^ 2 := by gcongr
  have hmul := Nat.mul_le_mul_right (r ^ 2) hge
  nlinarith only [hsquare, hmul, hrCube]

def blockAdmissible (n accuracy x : ℕ) : Prop :=
  (2 ≤ n ∧ 4 * 100 * k n * ell n ≤ x) ∨ n ≤ hopBound n accuracy x + 1

theorem cube_block_admissible (n accuracy : ℕ) (hn : 0 < n) :
    blockAdmissible n accuracy (blockSize n) := by
  by_cases hn₂ : 2 ≤ n
  · by_cases hx : 4 * 100 * k n * ell n ≤ blockSize n
    · exact Or.inl ⟨hn₂, hx⟩
    · exact Or.inr ((cube_small_case_hops n accuracy hn hx).trans (Nat.le_succ _))
  · exact Or.inr (by omega)

end StreamingReachability.Parameters
