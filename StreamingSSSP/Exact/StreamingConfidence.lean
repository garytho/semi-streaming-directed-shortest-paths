module

public import StreamingSSSP.Exact.StreamingRisk

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical

theorem exponent_le_two_pow (exponent : ℕ) : exponent + 4 ≤ 2 ^ (exponent + 2) := by
  induction exponent with
  | zero => decide
  | succ exponent ih =>
      have hp : 0 < 2 ^ (exponent + 2) := by positivity
      rw [show exponent + 1 + 2 = (exponent + 2) + 1 by omega, pow_succ]
      omega

theorem callCap_power (n exponent : ℕ) (hn : 2 ≤ n) : callCap n exponent ≤ n ^ (2 * exponent + 30) := by
  have he : n.log2 + 1 ≤ n := Parameters.ell_le_n n (by omega)
  have hx := exponent_le_two_pow exponent
  have hprod : 1 ≤ (exponent + 4) ^ 2 * n ^ 2 := by
    have hp : 0 < (exponent + 4) ^ 2 * n ^ 2 := by positivity
    omega
  calc
    callCap n exponent ≤ 2308 * (exponent + 4) ^ 2 * n ^ 2 + 1 := by
      unfold callCap
      gcongr
    _ ≤ 2309 * (exponent + 4) ^ 2 * n ^ 2 := by nlinarith
    _ ≤ 4096 * (2 ^ (exponent + 2)) ^ 2 * n ^ 2 := by gcongr; norm_num
    _ = 2 ^ (2 * exponent + 16) * n ^ 2 := by
      have hp : (2 : ℕ) ^ (2 * exponent + 16) = 4096 * (2 ^ (exponent + 2)) ^ 2 := by
        rw [show 2 * exponent + 16 = (exponent + 2) * 2 + 12 by omega, pow_add, pow_mul]
        rw [show (2 : ℕ) ^ 12 = 4096 by decide]
        ring
      rw [hp]
    _ ≤ n ^ (2 * exponent + 16) * n ^ 2 := by gcongr
    _ = n ^ (2 * exponent + 18) := by
      simpa only [Nat.add_assoc] using (pow_add n (2 * exponent + 16) 2).symm
    _ ≤ n ^ (2 * exponent + 30) := pow_le_pow_right₀ (by omega) (by omega)

def oracleConfidence (exponent confidence : ℕ) : ℕ :=
  confidence + (2 * exponent + 30)

theorem exact_failure_budget (n exponent confidence : ℕ) (hn : 2 ≤ n) :
    (1 / (n : ℝ) ^ oracleConfidence exponent confidence) * (callCap n exponent : ℝ) ≤
      1 / (n : ℝ) ^ confidence := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : (callCap n exponent : ℝ) ≤ (n : ℝ) ^ (2 * exponent + 30) := by
    exact_mod_cast callCap_power n exponent hn
  have hd : (0 : ℝ) < (n : ℝ) ^ confidence := pow_pos hp confidence
  have he : (0 : ℝ) < (n : ℝ) ^ (2 * exponent + 30) := pow_pos hp _
  unfold oracleConfidence
  rw [pow_add, one_div_mul_eq_div]
  apply (div_le_div_iff₀ (mul_pos hd he) hd).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hb hd.le]

end StreamingSSSP.Exact.Implementation
