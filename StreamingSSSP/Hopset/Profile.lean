module

public import StreamingSSSP.Hopset.Rank

@[expose] public section

namespace StreamingSSSP.PivotProfile

open scoped Classical

def rate (n : ℕ) (hn : 0 < n) (k ell r : ℕ) : Rate :=
  ⟨min (100 * k ^ (r + 1) * ell) n, n, hn, Nat.min_le_right _ _⟩

def rates (n : ℕ) (hn : 0 < n) (k ell cutoff : ℕ) : List Rate :=
  (List.range cutoff).map (rate n hn k ell)

@[simp] theorem length_rates (n : ℕ) (hn : 0 < n) (k ell cutoff : ℕ) :
    (rates n hn k ell cutoff).length = cutoff := by simp [rates]

theorem rate_value (n : ℕ) (hn : 0 < n) (k ell r : ℕ)
    (h : 100 * k ^ (r + 1) * ell ≤ n) :
    (rate n hn k ell r).value = (100 : ℝ) * (k : ℝ) ^ (r + 1) * ell / n := by
  simp only [rate, Rate.value, Nat.min_eq_left h, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem lookup (n : ℕ) (hn : 0 < n) (k ell cutoff r : ℕ) (hr : r < cutoff) :
    Ranks.rate (rates n hn k ell cutoff) r = rate n hn k ell r := by
  simp [Ranks.rate, rates, hr]

theorem take_rates (n : ℕ) (hn : 0 < n) (k ell cutoff r : ℕ) (hr : r ≤ cutoff) :
    (rates n hn k ell cutoff).take r = rates n hn k ell r := by
  simp only [rates, ← List.map_take, List.take_range, Nat.min_eq_left hr]

theorem powers_sum (k : ℝ) (r : ℕ) :
    (k - 1) * ((List.range r).map fun j => k ^ (j + 1)).sum = k ^ (r + 1) - k := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton, List.sum_append,
        List.sum_singleton]
      rw [pow_succ k (r + 1)]
      nlinarith

private theorem sum_scale (xs : List ℕ) (f : ℕ → ℝ) (c : ℝ) :
    (xs.map fun j => c * f j).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem prefix_sum_formula (n : ℕ) (hn : 0 < n) (k ell r : ℕ) (hk : 1 ≤ k)
    (hr : 100 * k ^ (r + 1) * ell ≤ n) :
    ((rates n hn k ell r).map Rate.value).sum =
      ((100 : ℝ) * ell / n) * ((List.range r).map fun j => (k : ℝ) ^ (j + 1)).sum := by
  have he : (rates n hn k ell r).map Rate.value =
      (List.range r).map fun j => ((100 : ℝ) * ell / n) * (k : ℝ) ^ (j + 1) := by
    rw [rates, List.map_map]
    apply List.map_congr_left
    intro j hj
    have hjr : j < r := List.mem_range.mp hj
    have hp : k ^ (j + 1) ≤ k ^ (r + 1) :=
      Nat.pow_le_pow_right hk (by omega)
    have hnum : 100 * k ^ (j + 1) * ell ≤ n := by
      exact (Nat.mul_le_mul_right ell (Nat.mul_le_mul_left 100 hp)).trans hr
    dsimp only [Function.comp_apply]
    rw [rate_value n hn k ell j hnum]
    ring
  rw [he, sum_scale]

theorem prefix_half (n : ℕ) (hn : 0 < n) (k ell r : ℕ) (hk : 3 ≤ k)
    (hr : 100 * k ^ (r + 1) * ell ≤ n) :
    ((rates n hn k ell r).map Rate.value).sum ≤ 1 / 2 := by
  let S := ((rates n hn k ell r).map Rate.value).sum
  let c : ℝ := (100 : ℝ) * ell / n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hS0 : 0 ≤ S := Ranks.rates_sum_nonneg _
  have hS := prefix_sum_formula n hn k ell r (by omega) hr
  have he : ((k : ℝ) - 1) * S = c * ((k : ℝ) ^ (r + 1) - k) := by
    dsimp only [S, c]
    rw [hS]
    calc
      _ = ((100 : ℝ) * ell / n) *
          (((k : ℝ) - 1) * ((List.range r).map fun j => (k : ℝ) ^ (j + 1)).sum) := by ring
      _ = _ := by rw [powers_sum]
  have hnump : (100 : ℝ) * (k : ℝ) ^ (r + 1) * ell / n ≤ 1 := by
    apply (div_le_one hn').mpr
    exact_mod_cast hr
  have hprod : ((k : ℝ) - 1) * S ≤ 1 := by
    rw [he]
    calc
      c * ((k : ℝ) ^ (r + 1) - k) ≤ c * (k : ℝ) ^ (r + 1) := by
        have h := mul_nonneg hc (show (0 : ℝ) ≤ k by positivity)
        nlinarith
      _ = (100 : ℝ) * (k : ℝ) ^ (r + 1) * ell / n := by dsimp [c]; ring
      _ ≤ 1 := hnump
  have hh := mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 3 by linarith) hS0
  change S ≤ 1 / 2
  nlinarith

theorem prefix_half_take (n : ℕ) (hn : 0 < n) (k ell cutoff r : ℕ)
    (hk : 3 ≤ k) (hrc : r ≤ cutoff) (hr : 100 * k ^ (r + 1) * ell ≤ n) :
    (((rates n hn k ell cutoff).take r).map Rate.value).sum ≤ 1 / 2 := by
  rw [take_rates n hn k ell cutoff r hrc]
  exact prefix_half n hn k ell r hk hr

end StreamingSSSP.PivotProfile
