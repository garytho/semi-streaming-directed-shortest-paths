module

public import StreamingReachability.Exact.MeasuredOrigins
public import StreamingReachability.Streaming.AuxiliaryPrefixes

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram StoredEdges
open Hopset.Measured

variable {n : ℕ}

structure PrimitiveSpace (coefficient exponent confidence : ℕ) (call : Hopset.Measured.Call n) : Prop where
  catalog : Core.Live.catalogCells call.request.catalog call.request.explicit ≤
    n * Hopset.Measured.envelope n coefficient exponent confidence ^ 6
  prefixes : ∀ hn : 0 < n, ∀ input : List (Edge n), (∀ e ∈ input, 0 < e.weight) →
    513 ≤ n → ∀ point : Core.Live.MemoryPoint hn call.request.catalog call.request.explicit input
      call.allowance call.request.workspace,
      point.cells ≤ n * Hopset.Measured.envelope n coefficient exponent confidence ^ 7

def Call.SpaceBound (coefficient exponent confidence : ℕ) : Call n → Prop
  | .base call => PrimitiveSpace coefficient exponent confidence call
  | .level call => PrimitiveSpace coefficient exponent confidence call

theorem approx_primitive_space {E : Type*} (view : E → Option (Edge n)) (input : List E) (auxiliary : List (Edge n))
    (hn : 0 < n) (accuracy coefficient exponent confidence : ℕ) (ha : 0 < accuracy)
    (haccuracy : accuracy ≤ coefficient * Parameters.ell n) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight)
    (hw : ∀ e ∈ input.filterMap view ++ auxiliary, e.weight ≤ (2 * n) ^ exponent) :
    Early.Sampling.Holds
      (Approx.Measured.evaluate view input auxiliary (Approx.solve hn accuracy (Parameters.blockSize n) confidence ha source))
      (fun out => ∀ call ∈ out.calls, PrimitiveSpace coefficient exponent confidence call) := by
  let bounds := Approx.scanAuxiliary view input auxiliary
  have hv : bounds.Valid (input.filterMap view ++ auxiliary) := by
    dsimp only [bounds]
    rw [Approx.scanAuxiliary_eq]
    exact Approx.scan_valid _ hp
  have hmax : bounds.maximum ≤ (2 * n) ^ exponent := by
    dsimp only [bounds]
    rw [Approx.scanAuxiliary_eq]
    exact Approx.Measured.scan_maximum _ _ hw
  have ht := envelope_trials n bounds.minWeight bounds.maximum coefficient exponent confidence hv.minWeight_pos hmax
  have hc := envelope_catalog n accuracy _ coefficient exponent confidence hn haccuracy ht
  have hm := envelope_memory n accuracy _ coefficient exponent confidence hn haccuracy ht
  have hs := Approx.Measured.solve_resources view input auxiliary hn accuracy (Parameters.blockSize n) confidence ha source hp
  refine Early.Sampling.holds_mono hs ?_
  intro out ho call hcall
  have hq := ho.calls_valid call hcall
  refine ⟨hq.catalog_le.trans hc, ?_⟩
  intro hn' logical hpositive hlarge point
  exact (hq.every_prefix hn' logical hpositive (Parameters.blockSize_workspace_eventual n hlarge) point).trans hm

theorem handler_space (source : Fin n) (exponent confidence coefficient weightExponent : ℕ)
    (input : List (Edge n)) (request : Request n) (hC : 0 < coefficient)
    (h : request.rawBounds (EdgeTransducer.preprocessingEdges input source (n ^ exponent))
      (coefficient * Parameters.ell n) ((2 * n) ^ weightExponent)) :
    Early.Sampling.Holds (handler source exponent confidence input request)
      (fun out => ∀ call ∈ out.calls, call.SpaceBound coefficient weightExponent confidence) := by
  cases request with
  | base descriptor querySource denominator clock =>
      have hden : safeAccuracy denominator ≤ coefficient * Parameters.ell n :=
        max_le (by have he := Parameters.ell_pos n; nlinarith) h.1
      have hw : ∀ e ∈ input.filterMap (baseView descriptor) ++ baseAuxiliary descriptor source (n ^ exponent),
          e.weight ≤ (2 * n) ^ weightExponent := by rw [base_input_eq]; exact h.2
      have hs := approx_primitive_space (baseView descriptor) input (baseAuxiliary descriptor source (n ^ exponent))
        (sourcePositive querySource) (safeAccuracy denominator) coefficient weightExponent confidence
        (safeAccuracy_pos denominator) hden querySource (base_input_positive descriptor source (n ^ exponent) input) hw
      refine Early.Sampling.holds_map hs (fun out => (fromBase out).map integerLabels) _ ?_
      intro out ho call hc
      obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hc
      exact ho raw hr
  | level descriptor denominator clock =>
      have hden : safeAccuracy denominator ≤ coefficient * Parameters.ell (n + 1) :=
        max_le (by have he := Parameters.ell_pos (n + 1); nlinarith)
          (h.1.trans (Nat.mul_le_mul_left coefficient (ell_mono (by omega))))
      have hw : ∀ e ∈ input.filterMap (levelView descriptor) ++ levelAuxiliary descriptor source (n ^ exponent),
          e.weight ≤ (2 * (n + 1)) ^ weightExponent := by
        rw [level_input_eq]
        exact fun e he => (h.2 e he).trans (Nat.pow_le_pow_left (by omega) _)
      have hs := approx_primitive_space (levelView descriptor) input (levelAuxiliary descriptor source (n ^ exponent))
        (Nat.succ_pos n) (safeAccuracy denominator) coefficient weightExponent confidence
        (safeAccuracy_pos denominator) hden (Fin.last n) (level_input_positive descriptor source (n ^ exponent) input) hw
      refine Early.Sampling.holds_map hs (fun out => (fromLevel out).map integerLevelAnswer) _ ?_
      intro out ho call hc
      obtain ⟨raw, hr, rfl⟩ := List.mem_map.mp hc
      exact ho raw hr
  | parents => exact Early.Sampling.holds_pure _ _ (by intro call hc; cases hc)

theorem evaluate_primitive_space (source : Fin n) (exponent confidence : ℕ) (input : List (Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => ∀ call ∈ out.calls,
        call.SpaceBound (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence)) := by
  let conf := oracleConfidence exponent confidence
  have hr := execute_run (handler source exponent conf input) (parentReplyOfEdges input)
    (handler_parents source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have ho := execute_origins (handler source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have hb : Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) {}
        out.result.result out.result.cache out.result.trace ∧ Origins (handler source exponent conf input) out) :=
    fun atom hatom => ⟨hr atom hatom, ho atom hatom⟩
  refine Early.Sampling.holds_mono hb ?_
  intro out hout call hc
  obtain ⟨entry, he, atom, ha, _, hcall⟩ := hout.2.calls call hc
  have hraw := hout.1.raw_bounds input hw entry he
  exact handler_space source exponent conf _ _ input entry.request (by positivity) hraw atom ha call hcall

end StreamingReachability.Exact.Implementation.Measured
