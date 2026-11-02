module

public import StreamingReachability.Hopset.WordCapacity
public import StreamingReachability.Core.DriverWordBounds

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Hopset.Measured

open Parameters

variable {n : ℕ}

theorem unit_polynomial (n accuracy coefficient exponent confidence : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) :
    queryUnit n accuracy (blockSize n) ≤ n ^ 2 * envelope n coefficient exponent confidence := by
  have hunit := envelope_unit n accuracy coefficient exponent confidence hn ha
  have hheight : 100 ^ maximumLevel n ≤ n :=
    (Nat.pow_le_pow_left (by have h := k_large n; omega : 100 ≤ k n) _).trans (power_maximumLevel_le n hn)
  exact hunit.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul (blockSize_le_n n hn) hheight)).trans_eq (by ring))

theorem coarse_weight_polynomial (n exponent : ℕ) (hn : 0 < n) :
    40 * n * ((2 * n) ^ exponent + 1) ≤ (2 * n) ^ (exponent + 10) := by
  let b := 2 * n
  have hb : 2 ≤ b := by dsimp only [b]; omega
  have hp : 1 ≤ b ^ exponent := by change 0 < _; positivity
  have h40 : 40 ≤ b ^ 6 := by
    have h := Nat.pow_le_pow_left hb 6
    norm_num at h
    omega
  calc
    _ ≤ 40 * n * (2 * b ^ exponent) :=
      Nat.mul_le_mul_left _ (by change b ^ exponent + 1 ≤ 2 * b ^ exponent; omega)
    _ = 40 * b * b ^ exponent := by dsimp only [b]; ring
    _ ≤ b ^ 6 * b * b ^ exponent := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right b h40)
    _ = b ^ (exponent + 7) := by rw [pow_add]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem scale_polynomial (input : List (StoredEdges.Edge n)) (hn : 0 < n) (exponent : ℕ)
    (hp : ∀ e ∈ input, 0 < e.weight) (hw : ∀ e ∈ input, e.weight ≤ (2 * n) ^ exponent) :
    guessScale n (Approx.scan input).minWeight (Approx.scan input).maximum ≤ (2 * n) ^ (exponent + 10) := by
  have h5 : 5 * n * ((2 * n) ^ exponent + 1) ≤ 40 * n * ((2 * n) ^ exponent + 1) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (n * ((2 * n) ^ exponent + 1)) (by decide : 5 ≤ 40)
  exact (Approx.Measured.scan_guess_scale hn input hp _ hw).trans (h5.trans (coarse_weight_polynomial n exponent hn))

theorem physical_weight_polynomial (n accuracy coefficient exponent confidence wmin wmax : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) (hw : wmax ≤ (2 * n) ^ exponent)
    (hs : guessScale n wmin wmax ≤ (2 * n) ^ (exponent + 10)) :
    physicalWeight n accuracy (blockSize n) wmin wmax ≤
      (2 * n) ^ (exponent + 20) * envelope n coefficient exponent confidence := by
  have hU := unit_polynomial n accuracy coefficient exponent confidence hn ha
  have hp : (2 * n) ^ exponent ≤ (2 * n) ^ (exponent + 10) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h9 : 9 * n ^ 2 ≤ (2 * n) ^ 10 := by
    have hpow : 9 ≤ (2 * n) ^ 8 :=
      le_trans (by norm_num : 9 ≤ 2 ^ 8) (Nat.pow_le_pow_left (by omega : 2 ≤ 2 * n) 8)
    have hsq : n ^ 2 ≤ (2 * n) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    exact (Nat.mul_le_mul hpow hsq).trans_eq (by rw [← pow_add])
  unfold physicalWeight
  calc
    _ ≤ (n ^ 2 * envelope n coefficient exponent confidence) *
        ((2 * n) ^ (exponent + 10) + 8 * (2 * n) ^ (exponent + 10)) :=
      Nat.mul_le_mul hU (Nat.add_le_add (hw.trans hp) (Nat.mul_le_mul_left 8 hs))
    _ = (9 * n ^ 2) * (2 * n) ^ (exponent + 10) * envelope n coefficient exponent confidence := by ring
    _ ≤ (2 * n) ^ 10 * (2 * n) ^ (exponent + 10) * envelope n coefficient exponent confidence :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h9)
    _ = _ := by rw [← pow_add, show 10 + (exponent + 10) = exponent + 20 by omega]

end StreamingReachability.Hopset.Measured

namespace StreamingReachability.Approx.Measured

open scoped Classical
open Hopset.Measured

variable {n : ℕ} {E : Type*}

structure NumericCall (coefficient exponent confidence : ℕ) (call : Hopset.Measured.Call n) : Prop where
  workspace : call.request.workspace ≤ n
  allowance : call.allowance ≤ n * envelope n coefficient exponent confidence ^ 4
  catalog : Core.Live.catalogCells call.request.catalog call.request.explicit ≤ n * envelope n coefficient exponent confidence ^ 6
  radius : call.request.radius ≤ 8 * n ^ 2 * envelope n coefficient exponent confidence
  scale : call.request.catalog.scale ≤ (2 * n) ^ (exponent + 10)
  weights : ∀ e ∈ call.request.explicit, e.weight ≤
    (2 * n) ^ (exponent + 20) * envelope n coefficient exponent confidence

theorem solve_numeric (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy coefficient exponent confidence : ℕ)
    (ha : 0 < accuracy) (haccuracy : accuracy ≤ coefficient * Parameters.ell n) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight)
    (hw : ∀ e ∈ input.filterMap view ++ auxiliary, e.weight ≤ (2 * n) ^ exponent) :
    Early.Sampling.Holds
      (evaluate view input auxiliary (solve hn accuracy (Parameters.blockSize n) confidence ha source))
      (fun out => ∀ call ∈ out.calls, NumericCall coefficient exponent confidence call) := by
  let bounds := scanAuxiliary view input auxiliary
  let H := Hopset.Measured.envelope n coefficient exponent confidence
  let U := Parameters.queryUnit n accuracy (Parameters.blockSize n)
  have hv : bounds.Valid (input.filterMap view ++ auxiliary) := by
    dsimp only [bounds]
    rw [scanAuxiliary_eq]
    exact scan_valid _ hp
  have hmax : bounds.maximum ≤ (2 * n) ^ exponent := by
    dsimp only [bounds]
    rw [scanAuxiliary_eq]
    exact scan_maximum _ _ hw
  have ht := envelope_trials n bounds.minWeight bounds.maximum coefficient exponent confidence hv.minWeight_pos hmax
  have hr := envelope_record_limit n accuracy _ coefficient exponent confidence haccuracy ht
  have hc := envelope_catalog n accuracy _ coefficient exponent confidence hn haccuracy ht
  have hU := unit_polynomial n accuracy coefficient exponent confidence hn haccuracy
  have hscale : guessScale n bounds.minWeight bounds.maximum ≤ (2 * n) ^ (exponent + 10) := by
    dsimp only [bounds]
    rw [scanAuxiliary_eq]
    exact scale_polynomial _ hn exponent hp hw
  have hweight := physical_weight_polynomial n accuracy coefficient exponent confidence bounds.minWeight bounds.maximum
    hn haccuracy hmax hscale
  have hs := solve_resources view input auxiliary hn accuracy (Parameters.blockSize n) confidence ha source hp
  refine Early.Sampling.holds_mono hs ?_
  intro out ho call hcall
  have hq := ho.calls_valid call hcall
  refine ⟨by rw [hq.workspace]; exact Parameters.blockSize_le_n n hn, hq.allowance_le.trans hr, hq.catalog_le.trans hc,
    ?_, hq.scale_le.trans hscale, ?_⟩
  · simpa only [Nat.mul_assoc] using hq.radius_le.trans (Nat.mul_le_mul_left 8 hU)
  · intro e he
    exact (hq.explicit_weights e he).trans hweight

end StreamingReachability.Approx.Measured
