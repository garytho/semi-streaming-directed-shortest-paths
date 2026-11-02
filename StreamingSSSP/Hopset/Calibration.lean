module

public import StreamingSSSP.Hopset.Height
public import StreamingSSSP.Hopset.Trial

@[expose] public section

namespace StreamingSSSP.Parameters

def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem le_mul_ceilDiv (a b : ℕ) (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  have hr := Nat.mod_lt (a + b - 1) hb
  have hd := Nat.div_add_mod (a + b - 1) b
  dsimp only [ceilDiv]
  omega

theorem ceilDiv_pos (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    0 < ceilDiv a b := by
  have h := le_mul_ceilDiv a b hb
  by_contra hn
  have hz : ceilDiv a b = 0 := by omega
  rw [hz, mul_zero] at h
  omega

def split (n : ℕ) : ℕ := Nat.sqrt (4096 * ell n) + 1
def k (n : ℕ) : ℕ := split n ^ 2
def groups (n : ℕ) : ℕ := 384 * 100 ^ 2 * k n ^ 2 * ell n ^ 2
def maximumLevel (n : ℕ) : ℕ := maxLevel n (k n) (ell n)
def threshold (n x : ℕ) : ℕ :=
  min (maximumLevel n) (firstCross x (k n) (4 * n) (4 * n))
def accuracyDenominator (n accuracy : ℕ) : ℕ := 20 * accuracy * ell n
def advance (n accuracy : ℕ) : ℕ :=
  17 + firstCross 1 (k n) (accuracyDenominator n accuracy ^ 2)
    (accuracyDenominator n accuracy ^ 2)
def centerDenominator (n accuracy : ℕ) : ℕ :=
  100 ^ advance n accuracy * split n ^ (advance n accuracy - 1)
def hopBound (n accuracy x : ℕ) : ℕ :=
  2 ^ 30 * 100 ^ (advance n accuracy + maximumLevel n + 2) *
    split n ^ (advance n accuracy + 3) * (Nat.sqrt (ceilDiv n x) + 1)
def queryUnit (n accuracy x : ℕ) : ℕ :=
  8 * hopBound n accuracy x * accuracyDenominator n accuracy
def initialNumerator (n accuracy x : ℕ) : ℕ := queryUnit n accuracy x * ell n ^ 3

theorem split_pos (n : ℕ) : 0 < split n := by unfold split; omega

theorem logarithm_le_k (n : ℕ) : ell n ≤ k n := by
  have hs := Nat.lt_succ_sqrt (4096 * ell n)
  have he := ell_pos n
  dsimp only [k, split]
  rw [pow_two]
  simpa only [Nat.succ_eq_add_one] using
    (show ell n ≤ (Nat.sqrt (4096 * ell n)).succ *
      (Nat.sqrt (4096 * ell n)).succ by omega)

theorem k_large (n : ℕ) : 4096 < k n := by
  have hs := Nat.lt_succ_sqrt (4096 * ell n)
  have he := ell_pos n
  dsimp only [k, split]
  rw [pow_two]
  simpa only [Nat.succ_eq_add_one] using
    (show 4096 < (Nat.sqrt (4096 * ell n)).succ *
      (Nat.sqrt (4096 * ell n)).succ by omega)

theorem groups_pos (n : ℕ) : 0 < groups n := by
  have hk : 0 < k n := by have := k_large n; omega
  have he := ell_pos n
  dsimp [groups]
  positivity

theorem advance_large (n accuracy : ℕ) : 17 ≤ advance n accuracy := by
  unfold advance
  omega

theorem centerDenominator_pos (n accuracy : ℕ) : 0 < centerDenominator n accuracy := by
  have hs := split_pos n
  dsimp [centerDenominator]
  positivity

theorem accuracyDenominator_pos (n accuracy : ℕ) (ha : 0 < accuracy) :
    0 < accuracyDenominator n accuracy := by
  have he := ell_pos n
  dsimp [accuracyDenominator]
  positivity

theorem hopBound_pos (n accuracy x : ℕ) : 0 < hopBound n accuracy x := by
  have hs := split_pos n
  dsimp [hopBound]
  positivity

theorem queryUnit_pos (n accuracy x : ℕ) (ha : 0 < accuracy) :
    0 < queryUnit n accuracy x := by
  have hh := hopBound_pos n accuracy x
  have hd := accuracyDenominator_pos n accuracy ha
  dsimp [queryUnit]
  positivity

theorem initialNumerator_pos (n accuracy x : ℕ) (ha : 0 < accuracy) :
    0 < initialNumerator n accuracy x := by
  have hq := queryUnit_pos n accuracy x ha
  have he := ell_pos n
  dsimp [initialNumerator]
  positivity

def configuration (n accuracy x delta storedBlockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) : Hopset.Config where
  split := split n
  split_pos := split_pos n
  groups := groups n
  groups_pos := groups_pos n
  shifts := ceilDiv (initialNumerator n accuracy x) (centerDenominator n accuracy)
  shifts_pos := ceilDiv_pos _ _ (initialNumerator_pos n accuracy x ha)
    (centerDenominator_pos n accuracy)
  logarithm := ell n
  maximumLevel := maximumLevel n
  earlyLevel := threshold n x
  advance := advance n accuracy
  initialNumerator := initialNumerator n accuracy x
  initialDenominator := centerDenominator n accuracy
  denominator_pos := centerDenominator_pos n accuracy
  inputScale := delta
  inputScale_pos := hd
  globalRadius := 8 * queryUnit n accuracy x
  blockSize := x
  copyCap := 2 ^ 30 * n * ell n ^ 4
  blockCap := 2 ^ 30 * n * k n * ell n ^ 4
  recordCap := 2 ^ 30 * k n ^ (advance n accuracy + 2) * ell n ^ 4 *
    (n + storedBlockVolume)

theorem maximumLevel_le_logarithm (n : ℕ) : maximumLevel n ≤ ell n :=
  maxLevel_le_ell n (k n) (ell n) (by have := k_large n; omega) (ell_pos n)

theorem power_maximumLevel_le (n : ℕ) (hn : 0 < n) :
    k n ^ maximumLevel n ≤ n :=
  power_maxLevel_le n (k n) (ell n) hn (by have := k_large n; omega) (ell_pos n)

theorem threshold_le_maximum (n x : ℕ) : threshold n x ≤ maximumLevel n :=
  Nat.min_le_left _ _

theorem eta_polynomial_budget (n : ℕ) :
    (8 * k n * groups n + 2) * ell n ^ 3 ≤ 30720002 * split n ^ 16 := by
  have hs : 1 ≤ split n := split_pos n
  have he : ell n ≤ split n ^ 2 := logarithm_le_k n
  have hpow : split n ^ 6 ≤ split n ^ 16 := Nat.pow_le_pow_right hs (by omega)
  calc
    _ = 30720000 * split n ^ 6 * ell n ^ 5 + 2 * ell n ^ 3 := by
      dsimp only [groups, k]
      ring
    _ ≤ 30720000 * split n ^ 6 * (split n ^ 2) ^ 5 +
        2 * (split n ^ 2) ^ 3 := by gcongr
    _ = 30720000 * split n ^ 16 + 2 * split n ^ 6 := by ring
    _ ≤ 30720002 * split n ^ 16 := by nlinarith

theorem eta_logarithm_budget (n accuracy : ℕ) :
    (8 * k n * groups n + 2) * ell n ^ 3 ≤ centerDenominator n accuracy := by
  have hs : 1 ≤ split n := split_pos n
  have hL := advance_large n accuracy
  calc
    _ ≤ 30720002 * split n ^ 16 := eta_polynomial_budget n
    _ ≤ 100 ^ 17 * split n ^ 16 := by gcongr <;> norm_num
    _ ≤ centerDenominator n accuracy := by
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega : 1 ≤ 100) hL)
        (Nat.pow_le_pow_right hs (by omega))

theorem denominatorAt_ge_initial (cfg : Hopset.Config) (r : ℕ) :
    cfg.initialDenominator ≤ cfg.denominatorAt r := by
  have hs : 1 ≤ (100 * cfg.split) ^ min r cfg.earlyLevel := by
    change 0 < (100 * cfg.split) ^ min r cfg.earlyLevel
    have h := cfg.split_pos
    positivity
  have hl : 1 ≤ 4 ^ (r - cfg.earlyLevel) := by
    change 0 < 4 ^ (r - cfg.earlyLevel)
    positivity
  exact (Nat.le_mul_of_pos_right _ hs).trans (Nat.le_mul_of_pos_right _ hl)

theorem searchRadius_le_queryUnit (n accuracy x delta storedBlockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (r : ℕ) :
    (configuration n accuracy x delta storedBlockVolume ha hd).searchRadius r ≤
      queryUnit n accuracy x := by
  let cfg := configuration n accuracy x delta storedBlockVolume ha hd
  have hi : cfg.etaMax * initialNumerator n accuracy x ≤
      centerDenominator n accuracy * queryUnit n accuracy x := by
    change (2 * (4 * k n * groups n) + 2) * (queryUnit n accuracy x * ell n ^ 3) ≤ _
    calc
      _ = ((8 * k n * groups n + 2) * ell n ^ 3) * queryUnit n accuracy x := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (eta_logarithm_budget n accuracy)
  have hc : cfg.etaMax * cfg.initialNumerator ≤
      cfg.denominatorAt r * queryUnit n accuracy x :=
    hi.trans (Nat.mul_le_mul_right _ (denominatorAt_ge_initial cfg r))
  exact Nat.div_le_of_le_mul hc

theorem initial_copies_fit (n accuracy x delta storedBlockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) :
    n ≤ (configuration n accuracy x delta storedBlockVolume ha hd).copyCap := by
  have he : 1 ≤ ell n ^ 4 := by
    change 0 < ell n ^ 4
    have := ell_pos n
    positivity
  change n ≤ 2 ^ 30 * n * ell n ^ 4
  calc
    n ≤ 2 ^ 30 * n := Nat.le_mul_of_pos_left _ (by norm_num)
    _ ≤ _ := Nat.le_mul_of_pos_right _ he

theorem advance_accuracy_power (n accuracy : ℕ) :
    accuracyDenominator n accuracy ≤ split n ^ (advance n accuracy - 17) := by
  let t := accuracyDenominator n accuracy ^ 2
  have hk : 2 ≤ k n := by have := k_large n; omega
  have hfuel : t ≤ 1 * k n ^ t := by
    calc
      t ≤ 2 ^ t := nat_le_two_pow t
      _ ≤ k n ^ t := by gcongr
      _ = _ := by simp
  have hcross := firstCross_large 1 (k n) t t hfuel
  have hpower : accuracyDenominator n accuracy ^ 2 ≤ k n ^ (advance n accuracy - 17) := by
    simpa only [advance, Nat.add_sub_cancel_left, one_mul] using hcross
  have heq : k n ^ (advance n accuracy - 17) =
      (split n ^ (advance n accuracy - 17)) ^ 2 := by
    dsimp only [k]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [heq] at hpower
  have hsquare (a b : ℕ) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by nlinarith
  exact hsquare _ _ hpower

theorem centerDenominator_factor (n accuracy : ℕ) :
    centerDenominator n accuracy =
      100 ^ 17 * split n ^ 16 *
        (100 ^ (advance n accuracy - 17) * split n ^ (advance n accuracy - 17)) := by
  have hL := advance_large n accuracy
  have ha : 100 ^ advance n accuracy =
      100 ^ 17 * 100 ^ (advance n accuracy - 17) := by
    rw [← pow_add]
    congr 1
    omega
  have hb : split n ^ (advance n accuracy - 1) =
      split n ^ 16 * split n ^ (advance n accuracy - 17) := by
    rw [← pow_add]
    congr 1
    omega
  dsimp only [centerDenominator]
  rw [ha, hb]
  ring

theorem detour_parameter_budget (n accuracy : ℕ) :
    2 ^ 30 * (8 * k n * groups n + 2) * ell n ^ 3 *
        accuracyDenominator n accuracy ≤ centerDenominator n accuracy := by
  have hcoef : 2 ^ 30 * 30720002 ≤ 100 ^ 17 := by norm_num
  have hp : 1 ≤ 100 ^ (advance n accuracy - 17) := by
    change 0 < 100 ^ (advance n accuracy - 17)
    positivity
  calc
    _ = 2 ^ 30 * ((8 * k n * groups n + 2) * ell n ^ 3) *
        accuracyDenominator n accuracy := by ring
    _ ≤ 2 ^ 30 * (30720002 * split n ^ 16) * accuracyDenominator n accuracy :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (eta_polynomial_budget n))
    _ ≤ 2 ^ 30 * (30720002 * split n ^ 16) * split n ^ (advance n accuracy - 17) :=
      Nat.mul_le_mul_left _ (advance_accuracy_power n accuracy)
    _ = (2 ^ 30 * 30720002) * split n ^ 16 * split n ^ (advance n accuracy - 17) := by ring
    _ ≤ 100 ^ 17 * split n ^ 16 * split n ^ (advance n accuracy - 17) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcoef)
    _ ≤ (100 ^ 17 * split n ^ 16 * split n ^ (advance n accuracy - 17)) *
        100 ^ (advance n accuracy - 17) := Nat.le_mul_of_pos_right _ hp
    _ = centerDenominator n accuracy := by rw [centerDenominator_factor]; ring

end StreamingSSSP.Parameters
