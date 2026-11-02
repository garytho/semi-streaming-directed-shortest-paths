module

public import StreamingReachability.Exact.ReplyWords
public import StreamingReachability.Exact.SpaceComplexity
public import StreamingReachability.Hopset.CalibrationWords

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram
open Hopset.Measured

variable {n : ℕ}

def wordBits (n exponent confidence : ℕ) : ℕ :=
  max (registerBits n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence))
    (registerBits (n + 1) (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence))

def traceWords (trace : List (Answered n)) : List ℕ :=
  trace.flatMap (fun entry => entry.request.dataWords ++ entry.request.replyWords entry.answer ++ entry.request.approxClocks)

theorem wordBits_logarithmic (exponent confidence : ℕ) :
    ∃ coefficient : ℕ, ∀ n, 0 < n → wordBits n exponent confidence ≤ coefficient * Parameters.ell n := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let D := 1000 * (envelopeBase C A conf).log2 + 1001 + 2 * (A + 100 + 100 * envelopeDegree C)
  refine ⟨3 * D, ?_⟩
  intro n hn
  have h := register_width n C A conf
  have hs := register_width (n + 1) C A conf
  change registerBits n C A conf ≤ D * Parameters.ell n at h
  change registerBits (n + 1) C A conf ≤ D * Parameters.ell (n + 1) at hs
  have hn' := ell_successor n hn
  have hn2 := Nat.mul_le_mul_left D hn'
  change max (registerBits n C A conf) (registerBits (n + 1) C A conf) ≤ (3 * D) * Parameters.ell n
  apply max_le
  · exact h.trans (Nat.mul_le_mul_right _ (by omega : D ≤ 3 * D))
  · exact (hs.trans hn2).trans ((by ring : D * (2 * Parameters.ell n) = (2 * D) * Parameters.ell n).le.trans
      (Nat.mul_le_mul_right _ (by omega : 2 * D ≤ 3 * D)))

theorem capacity_wordBits (source : Fin n) (exponent confidence : ℕ) :
    replyCapacity n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) <
      2 ^ wordBits n exponent confidence := by
  have hn := sourcePositive source
  have h := capacity_binary n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) hn
  have hs := capacity_binary (n + 1) (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) (Nat.succ_pos n)
  exact max_lt_iff.mpr ⟨h.trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _)),
    hs.trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))⟩

theorem callCap_capacity (source : Fin n) (exponent confidence : ℕ) :
    callCap n exponent ≤ replyCapacity n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let B := envelopeBase C A conf
  have hb : 20 * C ≤ B := (envelope_base_facts C A conf).2.1
  have hlarge : 1024 ≤ B := (envelope_base_facts C A conf).1
  have hcoeff : 2308 * (exponent + 4) ^ 2 + 1 ≤ B ^ 2 := by
    dsimp only [C] at hb
    nlinarith
  have hK := callCap_logarithmic n exponent
  have hE : callCap n exponent ≤ Hopset.Measured.envelope n C A conf :=
    hK.trans ((Nat.mul_le_mul_right (Parameters.ell n ^ 2) hcoeff).trans
      (envelope_dominates n C A conf 2 2 (by omega) (by unfold envelopeDegree; omega)))
  have hcap : Hopset.Measured.envelope n C A conf ≤ valueCapacity n C A conf := by
    simpa only [pow_zero, one_mul, pow_one] using capacity_monomial n C A conf 0 1 (sourcePositive source) (by omega) (by omega)
  exact (hE.trans hcap).trans (le_max_left _ _)

theorem Run.clock_words {source : Fin n} {exponent : ℕ} {cache final : Cache n} {result : Result n}
    {trace : List (Answered n)} (input : List (StoredEdges.Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) cache result final trace) :
    ∀ entry ∈ trace, ∀ clock ∈ entry.request.approxClocks, clock ≤ callCap n exponent := by
  let G := StoredEdges.graphOfEdges input
  have hc := h.exact_clocks G
  intro entry he clock hclock
  have hm : clock ∈ traceClocks trace := List.mem_flatMap.mpr ⟨entry, he, hclock⟩
  rw [hc] at hm
  have hb := outerClockList_bounds (smoothingRounds (inputBits n exponent)) (inputBits n exponent + 1) clock hm
  have hlen : (traceClocks trace).length =
      (inputBits n exponent + 1) * (1 + 2 * smoothingRounds (inputBits n exponent)) := by rw [hc, outerClockList_length]
  have htrace := trace_length trace
  have hcap := h.exact_length G
  omega

theorem evaluate_trace_words (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => ∀ value ∈ traceWords out.result.trace, value < 2 ^ wordBits n exponent confidence) := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let cap := replyCapacity n C A conf
  have hcapacity := capacity_wordBits source exponent confidence
  have hK := callCap_capacity source exponent confidence
  have hr := execute_run (handler source exponent conf input) (parentReplyOfEdges input)
    (handler_parents source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have hp := evaluate_reply_words source exponent confidence input hw
  have hb : Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) {}
        out.result.result out.result.cache out.result.trace ∧
        ∀ entry ∈ out.result.trace, ∀ value ∈ entry.request.replyWords entry.answer, value ≤ cap) :=
    fun atom hatom => ⟨hr atom hatom, hp atom hatom⟩
  refine Early.Sampling.holds_mono hb ?_
  intro out hout value hv
  obtain ⟨entry, he, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · have hdata := hout.1.data_words input entry he value hv
      have hE : 1 ≤ Hopset.Measured.envelope n C A conf ^ 100 := by
        change 0 < _
        have h := envelope_large n C A conf
        positivity
      have hbound : (2 * n) ^ A ≤ valueCapacity n C A conf :=
        (Nat.pow_le_pow_right (by have h := sourcePositive source; omega : 1 ≤ 2 * n)
          (by omega : A ≤ A + 100)).trans (Nat.le_mul_of_pos_right _ hE)
      exact (hdata.trans (hbound.trans (le_max_left _ _))).trans_lt hcapacity
    · exact (hout.2 entry he value hv).trans_lt hcapacity
  · exact ((Run.clock_words input hout.1 entry he value hv).trans hK).trans_lt hcapacity

theorem exact_streaming_word_encoding (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => ∃ encoded : List (Fin (2 ^ wordBits n exponent confidence)),
        encoded.map Fin.val = traceWords out.result.trace ∧ encoded.length = (traceWords out.result.trace).length) := by
  refine Early.Sampling.holds_mono (evaluate_trace_words source exponent confidence input hw) ?_
  intro out ho
  exact encode_words _ _ ho

end StreamingReachability.Exact.Implementation.Measured
