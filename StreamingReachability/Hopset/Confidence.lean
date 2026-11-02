module

public import StreamingReachability.Hopset.StageIteration

@[expose] public section

namespace StreamingReachability.Parameters

theorem ell_le_n (n : ℕ) (hn : 0 < n) : ell n ≤ n := by
  have hp (k : ℕ) : k + 1 ≤ 2 ^ k := by
    induction k with
    | zero => decide
    | succ k ih =>
        rw [pow_succ]
        have hpos : 0 < 2 ^ k := by positivity
        omega
  exact (hp n.log2).trans (Nat.log2_self_le hn.ne')

theorem confidence_power_budget (n confidence : ℕ) (hn : 0 < n) :
    n ^ confidence * ell n * n ^ 2 ≤ 2 ^ ((confidence + 16) * ell n) := by
  have hn₁ : 1 ≤ n := hn
  have htwo : n ≤ 2 ^ ell n := (lt_two_pow_ell n).le
  calc
    _ ≤ n ^ confidence * n * n ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (ell_le_n n hn))
    _ = n ^ (confidence + 3) := by rw [pow_add n confidence 3]; ring
    _ ≤ n ^ (confidence + 16) := pow_le_pow_right₀ hn₁ (by omega)
    _ ≤ (2 ^ ell n) ^ (confidence + 16) := by gcongr
    _ = _ := by rw [← pow_mul]; congr 1; ring

theorem confidence_failure_budget (n confidence : ℕ) (hn : 0 < n) :
    (ell n : ℝ) * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ ((confidence + 16) * ell n) ≤ 1 / (n : ℝ) ^ confidence := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : (n : ℝ) ^ confidence * (ell n : ℝ) * (n : ℝ) ^ 2 ≤
      (2 : ℝ) ^ ((confidence + 16) * ell n) := by exact_mod_cast confidence_power_budget n confidence hn
  have heq : (ell n : ℝ) * (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ ((confidence + 16) * ell n) =
      ((ell n : ℝ) * (n : ℝ) ^ 2) / (2 : ℝ) ^ ((confidence + 16) * ell n) := by
    rw [div_pow, one_pow]
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (pow_pos hnR confidence)).mpr
  nlinarith only [hb]

end StreamingReachability.Parameters
