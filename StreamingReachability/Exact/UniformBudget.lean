module

public import StreamingReachability.Exact.MeasuredBudget

@[expose] public section

set_option maxRecDepth 8192

namespace StreamingReachability.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram StoredEdges
open Parameters Hopset.Measured

variable {n : ℕ}

theorem ell_mono {n m : ℕ} (h : n ≤ m) : ell n ≤ ell m := by
  have hm := Nat.log_mono_right (b := 2) h
  simp only [← Nat.log2_eq_log_two] at hm
  unfold ell
  omega

def uniformBudget (n coefficient exponent confidence : ℕ) : Budget :=
  let E := Hopset.Measured.envelope n coefficient exponent confidence
  let F := Hopset.Measured.envelope (n + 1) coefficient exponent confidence
  ⟨Parameters.blockSize n * 100 ^ maximumLevel n * E ^ 10 +
      Parameters.blockSize (n + 1) * 100 ^ maximumLevel (n + 1) * F ^ 10 + 1,
    E ^ 3 + F ^ 3, n * E ^ 5 + (n + 1) * F ^ 5⟩

theorem solveBudget_uniform (input : List (Edge n)) (accuracy coefficient exponent confidence : ℕ)
    (hn : 0 < n) (ha : accuracy ≤ coefficient * ell n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hw : ∀ e ∈ input, e.weight ≤ (2 * n) ^ exponent) :
    let E := Hopset.Measured.envelope n coefficient exponent confidence
    let budget := solveBudget n accuracy confidence (Approx.scan input)
    budget.passes ≤ Parameters.blockSize n * 100 ^ maximumLevel n * E ^ 10 ∧
      budget.calls ≤ E ^ 3 ∧ budget.draws ≤ n * E ^ 5 := by
  let bounds := Approx.scan input
  let E := Hopset.Measured.envelope n coefficient exponent confidence
  have hv := Approx.scan_valid input hp
  have hmin : 0 < bounds.minWeight := hv.minWeight_pos
  have hmax : bounds.maximum ≤ (2 * n) ^ exponent := Approx.Measured.scan_maximum input _ hw
  have hpasses := envelope_solve_passes n accuracy bounds.minWeight bounds.maximum coefficient exponent confidence hn ha hmin hmax
  have hcalls := envelope_solve_calls n bounds.minWeight bounds.maximum coefficient exponent confidence hmin hmax
  have htrials := envelope_trials n bounds.minWeight bounds.maximum coefficient exponent confidence hmin hmax
  have hdraws := envelope_draws n accuracy (Parameters.blockSize n) coefficient exponent confidence
  refine ⟨hpasses, hcalls, ?_⟩
  exact (Nat.mul_le_mul htrials hdraws).trans_eq (by ring)

theorem requestBudget_uniform (source : Fin n) (exponent confidence coefficient weightExponent : ℕ)
    (input : List (Edge n)) (request : Request n) (hC : 0 < coefficient)
    (h : request.rawBounds (EdgeTransducer.preprocessingEdges input source (n ^ exponent))
      (coefficient * ell n) ((2 * n) ^ weightExponent)) :
    let budget := requestBudget source exponent confidence input request
    let limit := uniformBudget n coefficient weightExponent confidence
    budget.passes ≤ limit.passes ∧ budget.calls ≤ limit.calls ∧ budget.draws ≤ limit.draws := by
  cases request with
  | base descriptor querySource denominator clock =>
      have hden : safeAccuracy denominator ≤ coefficient * ell n :=
        max_le (by have he := ell_pos n; nlinarith) h.1
      have hw : ∀ e ∈ input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor source (n ^ exponent),
          e.weight ≤ (2 * n) ^ weightExponent := by
        rw [base_input_eq]
        exact h.2
      have hb := solveBudget_uniform _ (safeAccuracy denominator) coefficient weightExponent confidence
        (sourcePositive querySource) hden (base_input_positive descriptor source (n ^ exponent) input) hw
      simp only [requestBudget, Approx.scanAuxiliary_eq]
      exact ⟨hb.1.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 1)),
        hb.2.1.trans (Nat.le_add_right _ _), hb.2.2.trans (Nat.le_add_right _ _)⟩
  | level descriptor denominator clock =>
      have he : ell n ≤ ell (n + 1) := ell_mono (by omega)
      have hden : safeAccuracy denominator ≤ coefficient * ell (n + 1) :=
        max_le (by have hp := ell_pos (n + 1); nlinarith)
          (h.1.trans (Nat.mul_le_mul_left coefficient he))
      have hw : ∀ e ∈ input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor source (n ^ exponent),
          e.weight ≤ (2 * (n + 1)) ^ weightExponent := by
        rw [level_input_eq]
        intro e he
        exact (h.2 e he).trans (Nat.pow_le_pow_left (by omega) weightExponent)
      have hb := solveBudget_uniform _ (safeAccuracy denominator) coefficient weightExponent confidence
        (Nat.succ_pos n) hden (level_input_positive descriptor source (n ^ exponent) input) hw
      simp only [requestBudget, Approx.scanAuxiliary_eq]
      exact ⟨hb.1.trans ((Nat.le_add_left _ _).trans (Nat.le_add_right _ 1)),
        hb.2.1.trans (Nat.le_add_left _ _), hb.2.2.trans (Nat.le_add_left _ _)⟩
  | parents =>
      simp only [requestBudget, uniformBudget]
      exact ⟨by omega, Nat.zero_le _, Nat.zero_le _⟩

theorem _root_.StreamingReachability.Exact.Implementation.Run.raw_bounds
    {source : Fin n} {exponent : ℕ} {cache final : Cache n} {result : Result n}
    {trace : List (Answered n)} (input : List (Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) cache result final trace)
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    ∀ entry ∈ trace, entry.request.rawBounds
      (EdgeTransducer.preprocessingEdges input source (n ^ exponent))
      (20000000 * (exponent + 4) * ell n) ((2 * n) ^ (2000 * (exponent + 4))) := by
  let G := graphOfEdges input
  have hb := exact_raw_query_bounds (interpretReply G final.baseOracle final.levelOracle (parentReplyOfEdges input))
    source exponent input hw
  intro entry he
  apply hb entry.request
  unfold requests
  rw [h.replay_trace G (fun request => [request])]
  exact List.mem_flatMap.mpr ⟨entry, he, by simp⟩

theorem evaluate_resources (source : Fin n) (exponent confidence : ℕ) (input : List (Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    let limit := uniformBudget n (20000000 * (exponent + 4)) (2000 * (exponent + 4))
      (oracleConfidence exponent confidence)
    Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => out.passes ≤ callCap n exponent * limit.passes ∧
        out.calls.length ≤ callCap n exponent * limit.calls ∧
        out.draws.length ≤ callCap n exponent * limit.draws ∧
        out.result.trace.length ≤ callCap n exponent) := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let limit := uniformBudget n C A conf
  let budget := requestBudget source exponent conf input
  have hr := execute_run (handler source exponent conf input) (parentReplyOfEdges input)
    (handler_parents source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have hb := execute_budget (handler source exponent conf input) budget
    (handler_budget source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have hboth : Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) {}
        out.result.result out.result.cache out.result.trace ∧
          WorkFits (traceBudget budget out.result.trace) out) :=
    fun atom hatom => ⟨hr atom hatom, hb atom hatom⟩
  change Early.Sampling.Holds (evaluate source exponent confidence input)
    (fun out => out.passes ≤ callCap n exponent * limit.passes ∧
      out.calls.length ≤ callCap n exponent * limit.calls ∧
      out.draws.length ≤ callCap n exponent * limit.draws ∧
      out.result.trace.length ≤ callCap n exponent)
  refine Early.Sampling.holds_mono hboth ?_
  intro out ho
  have hrun := ho.1
  have hfits := ho.2
  have hraw := hrun.raw_bounds input hw
  have hlength := hrun.exact_length (graphOfEdges input)
  have hlimits := trace_budget_bound budget out.result.trace limit (fun entry he =>
    requestBudget_uniform source exponent conf C A input entry.request (by dsimp only [C]; positivity) (hraw entry he))
  exact ⟨hfits.passes_le.trans (hlimits.1.trans (Nat.mul_le_mul_right _ hlength)),
    hfits.calls_le.trans (hlimits.2.1.trans (Nat.mul_le_mul_right _ hlength)),
    hfits.draws_le.trans (hlimits.2.2.trans (Nat.mul_le_mul_right _ hlength)), hlength⟩

end StreamingReachability.Exact.Implementation.Measured
