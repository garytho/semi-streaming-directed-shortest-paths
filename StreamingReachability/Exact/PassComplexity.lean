module

public import StreamingReachability.Exact.UniformBudget
public import StreamingReachability.Hopset.Asymptotics

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Exact.Implementation.Measured

open Filter
open scoped Topology
open Hopset.Measured

def passLimit (n exponent confidence : ℕ) : ℕ :=
  callCap n exponent * (uniformBudget n (20000000 * (exponent + 4)) (2000 * (exponent + 4))
    (oracleConfidence exponent confidence)).passes

theorem callCap_logarithmic (n exponent : ℕ) :
    callCap n exponent ≤ (2308 * (exponent + 4) ^ 2 + 1) * Parameters.ell n ^ 2 := by
  have he : 1 ≤ Parameters.ell n ^ 2 := by change 0 < _; have h := Parameters.ell_pos n; positivity
  unfold callCap Parameters.ell at *
  nlinarith

theorem metered_call_polynomial (n calls coefficient weightExponent confidence callCoefficient : ℕ)
    (hc : calls ≤ callCoefficient * Parameters.ell n ^ 2) :
    calls * (Parameters.blockSize n * 100 ^ Parameters.maximumLevel n *
      Hopset.Measured.envelope n coefficient weightExponent confidence ^ 10) ≤
      (callCoefficient * envelopeBase coefficient weightExponent confidence ^ 100) *
        Parameters.blockSize n * Parameters.ell n ^ (10 * envelopeDegree coefficient + 2) *
          100 ^ Parameters.maximumLevel n := by
  calc
    _ ≤ (callCoefficient * Parameters.ell n ^ 2) *
        (Parameters.blockSize n * 100 ^ Parameters.maximumLevel n *
          Hopset.Measured.envelope n coefficient weightExponent confidence ^ 10) := Nat.mul_le_mul_right _ hc
    _ = _ := by
      unfold Hopset.Measured.envelope
      rw [mul_pow, ← pow_mul, ← pow_mul, pow_add]
      ring

theorem passLimit_two_cubes (n exponent confidence : ℕ) (hn : 0 < n) :
    let coefficient := 20000000 * (exponent + 4)
    let weightExponent := 2000 * (exponent + 4)
    let conf := oracleConfidence exponent confidence
    let constant := (2308 * (exponent + 4) ^ 2 + 1) * envelopeBase coefficient weightExponent conf ^ 100
    let degree := 10 * envelopeDegree coefficient + 2
    passLimit n exponent confidence ≤
      2 * (constant * Parameters.blockSize n * Parameters.ell n ^ degree * 100 ^ Parameters.maximumLevel n) +
        constant * Parameters.blockSize (n + 1) * Parameters.ell (n + 1) ^ degree *
          100 ^ Parameters.maximumLevel (n + 1) := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let K := callCap n exponent
  let P := Parameters.blockSize n * 100 ^ Parameters.maximumLevel n *
    Hopset.Measured.envelope n C A conf ^ 10
  let Q := Parameters.blockSize (n + 1) * 100 ^ Parameters.maximumLevel (n + 1) *
    Hopset.Measured.envelope (n + 1) C A conf ^ 10
  have hP : 1 ≤ P := by
    change 0 < P
    dsimp only [P]
    have hx := Parameters.blockSize_pos n
    have hE : 0 < Hopset.Measured.envelope n C A conf :=
      lt_of_lt_of_le (by norm_num : 0 < 1024) (envelope_large n C A conf)
    positivity
  have hK := callCap_logarithmic n exponent
  have hKnext : K ≤ (2308 * (exponent + 4) ^ 2 + 1) * Parameters.ell (n + 1) ^ 2 :=
    hK.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (ell_mono (by omega)) 2))
  have hp := metered_call_polynomial n K C A conf _ hK
  have hq := metered_call_polynomial (n + 1) K C A conf _ hKnext
  change K * (P + Q + 1) ≤ _
  calc
    _ ≤ K * (2 * P + Q) := Nat.mul_le_mul_left K (by omega)
    _ = 2 * (K * P) + K * Q := by ring
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left 2 hp) hq

theorem passLimit_subpower (exponent confidence : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ constant : ℝ, 0 < constant ∧ ∀ᶠ n : ℕ in atTop,
      (passLimit n exponent confidence : ℝ) ≤ constant * (n : ℝ) ^ (1 / 3 + epsilon) := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let constant := (2308 * (exponent + 4) ^ 2 + 1) * envelopeBase C A conf ^ 100
  let degree := 10 * envelopeDegree C + 2
  let F := fun n => constant * Parameters.blockSize n * Parameters.ell n ^ degree * 100 ^ Parameters.maximumLevel n
  obtain ⟨M, hM, hbound⟩ := Parameters.cube_polylog_height constant degree he
  have hnext : ∀ᶠ n : ℕ in atTop, (F (n + 1) : ℝ) ≤ M * ((n + 1 : ℕ) : ℝ) ^ (1 / 3 + epsilon) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
    exact eventually_atTop.mpr ⟨N, fun n hn => hN (n + 1) (by omega)⟩
  refine ⟨M * (2 + (2 : ℝ) ^ (1 / 3 + epsilon)), by positivity, ?_⟩
  filter_upwards [hbound, hnext, eventually_ge_atTop 1] with n hb hbn hn
  have hfin : (passLimit n exponent confidence : ℝ) ≤ 2 * (F n : ℝ) + (F (n + 1) : ℝ) := by
    exact_mod_cast passLimit_two_cubes n exponent confidence (by omega)
  have hplus : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hr := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ)) hplus
    (by linarith : (0 : ℝ) ≤ 1 / 3 + epsilon)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)] at hr
  calc
    _ ≤ 2 * (F n : ℝ) + (F (n + 1) : ℝ) := hfin
    _ ≤ 2 * (M * (n : ℝ) ^ (1 / 3 + epsilon)) +
        M * ((2 : ℝ) ^ (1 / 3 + epsilon) * (n : ℝ) ^ (1 / 3 + epsilon)) :=
      add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num))
        (hbn.trans (mul_le_mul_of_nonneg_left hr hM.le))
    _ = _ := by ring

/-- All executions, not just the successful accuracy event, satisfy the
claimed pass exponent for the actual original-stream exact algorithm. -/
theorem exact_streaming_passes (exponent confidence : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ constant : ℝ, 0 < constant ∧ ∃ threshold : ℕ,
      ∀ n ≥ threshold, ∀ source : Fin n, ∀ input : List (StoredEdges.Edge n),
        (∀ e ∈ input, e.weight ≤ n ^ exponent) →
        Early.Sampling.Holds (evaluate source exponent confidence input)
          (fun out => (out.passes : ℝ) ≤ constant * (n : ℝ) ^ (1 / 3 + epsilon)) := by
  obtain ⟨C, hC, hbound⟩ := passLimit_subpower exponent confidence he
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  refine ⟨C, hC, N, ?_⟩
  intro n hn source input hw
  refine Early.Sampling.holds_mono (evaluate_resources source exponent confidence input hw) ?_
  intro out ho
  have hp : (out.passes : ℝ) ≤ (passLimit n exponent confidence : ℝ) := by exact_mod_cast ho.1
  exact hp.trans (hN n hn)

end StreamingReachability.Exact.Implementation.Measured
