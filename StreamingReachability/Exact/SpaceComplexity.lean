module

public import StreamingReachability.Exact.PrimitiveSpace
public import StreamingReachability.Exact.PassComplexity

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram
open Hopset.Measured

variable {n : ℕ}

theorem small_multiple_power (base coefficient degree : ℕ) (h : coefficient ≤ base) :
    coefficient * base ^ degree ≤ base ^ (degree + 1) := by
  exact (Nat.mul_le_mul_right _ h).trans_eq (by rw [pow_succ]; ring)

def Call.cells : Call n → ℕ
  | .base call => Core.Live.catalogCells call.request.catalog call.request.explicit + 32
  | .level call => Core.Live.catalogCells call.request.catalog call.request.explicit + 32

def globalEnvelope (n exponent confidence : ℕ) : ℕ :=
  Hopset.Measured.envelope n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) +
    Hopset.Measured.envelope (n + 1) (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) +
    callCap n exponent + 1024

/-- This conservative layout retains even the proof-accounting histories.
Their call count is polylogarithmic; no original edge stream is retained. -/
def retainedCells (out : Work n (Outcome n (Result n))) : ℕ :=
  (8 * n + 16) * out.result.trace.length + out.result.cache.cells +
    (out.calls.map Call.cells).sum + 3 * out.draws.length + 16 * n + 128

def workingCells (exponent confidence : ℕ) (out : Work n (Outcome n (Result n))) : ℕ :=
  retainedCells out +
    n * Hopset.Measured.envelope n (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) ^ 9 +
    (n + 1) * Hopset.Measured.envelope (n + 1) (20000000 * (exponent + 4)) (2000 * (exponent + 4)) (oracleConfidence exponent confidence) ^ 9

theorem call_storage (coefficient exponent confidence G : ℕ) (hn : 0 < n) (hG : 1024 ≤ G)
    (hE : Hopset.Measured.envelope n coefficient exponent confidence ≤ G)
    (hF : Hopset.Measured.envelope (n + 1) coefficient exponent confidence ≤ G)
    (call : Call n) (h : call.SpaceBound coefficient exponent confidence) :
    call.cells ≤ 4 * n * G ^ 6 := by
  have hN : 32 ≤ n * G ^ 6 := by
    have hpow : G ≤ G ^ 6 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ G) (by omega : 1 ≤ 6)
    have hm := Nat.le_mul_of_pos_left (G ^ 6) hn
    omega
  cases call with
  | base call =>
      have hc := h.catalog.trans (Nat.mul_le_mul_left n (Nat.pow_le_pow_left hE 6))
      change Core.Live.catalogCells call.request.catalog call.request.explicit + 32 ≤ _
      calc
        _ ≤ 2 * (n * G ^ 6) := by omega
        _ = (2 * n) * G ^ 6 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  | level call =>
      have hc := h.catalog.trans (Nat.mul_le_mul (show n + 1 ≤ 2 * n by omega) (Nat.pow_le_pow_left hF 6))
      change Core.Live.catalogCells call.request.catalog call.request.explicit + 32 ≤ _
      calc
        _ ≤ (2 * n) * G ^ 6 + n * G ^ 6 := Nat.add_le_add hc hN
        _ = (3 * n) * G ^ 6 := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem retained_bound (G : ℕ) (hn : 0 < n) (hG : 1024 ≤ G) (out : Work n (Outcome n (Result n)))
    (ht : out.result.trace.length ≤ G) (hc : out.calls.length ≤ G ^ 5) (hd : out.draws.length ≤ n * G ^ 7)
    (hcache : out.result.cache.cells ≤ (n + 2) * G) (hcall : ∀ call ∈ out.calls, call.cells ≤ 4 * n * G ^ 6) :
    retainedCells out ≤ n * G ^ 13 := by
  let F := n * G ^ 12
  have h1 : n * G ≤ F := Nat.mul_le_mul_left n (by simpa only [pow_one] using
    (Nat.pow_le_pow_right (by omega : 1 ≤ G) (by omega : 1 ≤ 12)))
  have htrace : (8 * n + 16) * out.result.trace.length ≤ F := by
    have hsmall : 8 * n + 16 ≤ 24 * n := by omega
    have hp : 24 * G ≤ G ^ 12 := by
      calc
        _ ≤ G * G := Nat.mul_le_mul_right G (by omega)
        _ = G ^ 2 := by ring
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.mul_le_mul hsmall ht).trans
      ((by ring : 24 * n * G = n * (24 * G)).le.trans (Nat.mul_le_mul_left n hp))
  have hcached : out.result.cache.cells ≤ F := by
    have hp : 3 * G ≤ G ^ 12 := by
      calc
        _ ≤ G * G := Nat.mul_le_mul_right G (by omega)
        _ = G ^ 2 := by ring
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    calc
      _ ≤ (n + 2) * G := hcache
      _ ≤ (3 * n) * G := Nat.mul_le_mul_right _ (by omega)
      _ = n * (3 * G) := by ring
      _ ≤ _ := Nat.mul_le_mul_left n hp
  have hsum := List.sum_le_sum (l := out.calls) (f := Call.cells) (g := fun _ => 4 * n * G ^ 6) hcall
  have hcalls : (out.calls.map Call.cells).sum ≤ F := by
    calc
      _ ≤ out.calls.length * (4 * n * G ^ 6) := by simpa using hsum
      _ ≤ G ^ 5 * (4 * n * G ^ 6) := Nat.mul_le_mul_right _ hc
      _ = n * (4 * G ^ 11) := by ring
      _ ≤ _ := Nat.mul_le_mul_left n (small_multiple_power G 4 11 (by omega))
  have hdraw : 3 * out.draws.length ≤ F := by
    have hp : 3 * G ^ 7 ≤ G ^ 12 := by
      calc
        _ ≤ G * G ^ 7 := Nat.mul_le_mul_right _ (by omega)
        _ = G ^ 8 := by ring
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    exact (Nat.mul_le_mul_left 3 hd).trans
      ((by ring : 3 * (n * G ^ 7) = n * (3 * G ^ 7)).le.trans (Nat.mul_le_mul_left n hp))
  have hcontrol : 16 * n + 128 ≤ F := by
    calc
      _ ≤ 144 * n := by omega
      _ ≤ G * n := Nat.mul_le_mul_right n (by omega)
      _ = n * G := by ring
      _ ≤ _ := h1
  unfold retainedCells
  calc
    _ ≤ 5 * F := by omega
    _ ≤ G * F := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by dsimp only [F]; ring

theorem evaluate_space (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => workingCells exponent confidence out ≤ n * globalEnvelope n exponent confidence ^ 14) := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let E := Hopset.Measured.envelope n C A conf
  let F := Hopset.Measured.envelope (n + 1) C A conf
  let G := globalEnvelope n exponent confidence
  have hn := sourcePositive source
  have hG : 1024 ≤ G := by dsimp only [G, globalEnvelope]; omega
  have hE : E ≤ G := by dsimp only [G, globalEnvelope, E, C, A, conf]; omega
  have hF : F ≤ G := by dsimp only [G, globalEnvelope, F, C, A, conf]; omega
  have hK : callCap n exponent ≤ G := by dsimp only [G, globalEnvelope]; omega
  have hr := execute_run (handler source exponent conf input) (parentReplyOfEdges input)
    (handler_parents source exponent conf input) (DescriptorProgram.exact source exponent) {}
  have hb := evaluate_resources source exponent confidence input hw
  have hs := evaluate_primitive_space source exponent confidence input hw
  have hboth : Early.Sampling.Holds (evaluate source exponent confidence input)
      (fun out => Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) {}
        out.result.result out.result.cache out.result.trace ∧
        out.calls.length ≤ callCap n exponent * (E ^ 3 + F ^ 3) ∧
        out.draws.length ≤ callCap n exponent * (n * E ^ 5 + (n + 1) * F ^ 5) ∧
        out.result.trace.length ≤ callCap n exponent ∧
        ∀ call ∈ out.calls, call.SpaceBound C A conf) := by
    intro atom hatom
    have hres := hb atom hatom
    exact ⟨hr atom hatom, hres.2.1, hres.2.2.1, hres.2.2.2, hs atom hatom⟩
  refine Early.Sampling.holds_mono hboth ?_
  intro out ho
  have hc : out.calls.length ≤ G ^ 5 := by
    calc
      _ ≤ callCap n exponent * (E ^ 3 + F ^ 3) := ho.2.1
      _ ≤ G * (G ^ 3 + G ^ 3) := by gcongr
      _ = 2 * G ^ 4 := by ring
      _ ≤ G ^ 5 := small_multiple_power G 2 4 (by omega)
  have hd : out.draws.length ≤ n * G ^ 7 := by
    calc
      _ ≤ callCap n exponent * (n * E ^ 5 + (n + 1) * F ^ 5) := ho.2.2.1
      _ ≤ G * (n * G ^ 5 + (2 * n) * G ^ 5) := by gcongr <;> omega
      _ = n * (3 * G ^ 6) := by ring
      _ ≤ _ := Nat.mul_le_mul_left n (small_multiple_power G 3 6 (by omega))
  have hcache : out.result.cache.cells ≤ (n + 2) * G :=
    ho.1.root_cache_cells.trans (Nat.mul_le_mul_left _ (ho.2.2.2.1.trans hK))
  have hretained := retained_bound G hn hG out (ho.2.2.2.1.trans hK) hc hd hcache
    (fun call hcall => call_storage C A conf G hn hG hE hF call (ho.2.2.2.2 call hcall))
  have hactive : n * E ^ 9 + (n + 1) * F ^ 9 ≤ n * G ^ 10 := by
    calc
      _ ≤ n * G ^ 9 + (2 * n) * G ^ 9 := by gcongr <;> omega
      _ = n * (3 * G ^ 9) := by ring
      _ ≤ _ := Nat.mul_le_mul_left n (small_multiple_power G 3 9 (by omega))
  change retainedCells out + n * E ^ 9 + (n + 1) * F ^ 9 ≤ n * G ^ 14
  calc
    _ ≤ n * G ^ 13 + n * G ^ 10 := by omega
    _ = n * (G ^ 10 + G ^ 13) := by ring
    _ ≤ _ := Nat.mul_le_mul_left n (pow_sum_bound G 10 13 (by omega) (by omega))

theorem ell_successor (n : ℕ) (hn : 0 < n) : Parameters.ell (n + 1) ≤ 2 * Parameters.ell n := by
  have he := Parameters.ell_pos n
  have hpow : n + 1 < 2 ^ (Parameters.ell n + 1) := by
    rw [pow_succ]
    have h := Parameters.lt_two_pow_ell n
    omega
  have hlog := (Nat.log2_lt (by omega : n + 1 ≠ 0)).mpr hpow
  unfold Parameters.ell at *
  omega

theorem globalEnvelope_polylog (exponent confidence : ℕ) :
    ∃ coefficient degree : ℕ, ∀ n, 0 < n →
      globalEnvelope n exponent confidence ≤ coefficient * Parameters.ell n ^ degree := by
  let C := 20000000 * (exponent + 4)
  let A := 2000 * (exponent + 4)
  let conf := oracleConfidence exponent confidence
  let B := envelopeBase C A conf
  let d := envelopeDegree C
  refine ⟨B ^ 10 * (1 + 2 ^ d) + (2308 * (exponent + 4) ^ 2 + 1) + 1024, d, ?_⟩
  intro n hn
  have hE : Hopset.Measured.envelope n C A conf = B ^ 10 * Parameters.ell n ^ d := rfl
  have hF : Hopset.Measured.envelope (n + 1) C A conf ≤ B ^ 10 * 2 ^ d * Parameters.ell n ^ d := by
    unfold Hopset.Measured.envelope
    exact (Nat.mul_le_mul_left (B ^ 10) (Nat.pow_le_pow_left (ell_successor n hn) d)).trans_eq (by rw [mul_pow]; ring)
  have hK := callCap_logarithmic n exponent
  have he := Parameters.ell_pos n
  have hd : 2 ≤ d := by dsimp only [d]; unfold envelopeDegree envelopeLevel; omega
  have hpow : Parameters.ell n ^ 2 ≤ Parameters.ell n ^ d := Nat.pow_le_pow_right he hd
  have h1 : 1 ≤ Parameters.ell n ^ d := by change 0 < _; positivity
  change Hopset.Measured.envelope n C A conf + Hopset.Measured.envelope (n + 1) C A conf +
    callCap n exponent + 1024 ≤ _
  rw [hE]
  nlinarith [Nat.mul_le_mul_left (2308 * (exponent + 4) ^ 2 + 1) hpow]

theorem exact_streaming_space (exponent confidence : ℕ) :
    ∃ coefficient degree : ℕ, ∀ n, 513 ≤ n → ∀ source : Fin n, ∀ input : List (StoredEdges.Edge n),
      (∀ e ∈ input, e.weight ≤ n ^ exponent) →
      Early.Sampling.Holds (evaluate source exponent confidence input)
        (fun out => workingCells exponent confidence out ≤ coefficient * n * Parameters.ell n ^ degree) := by
  obtain ⟨C, d, hC⟩ := globalEnvelope_polylog exponent confidence
  refine ⟨C ^ 14, d * 14, ?_⟩
  intro n hn source input hw
  refine Early.Sampling.holds_mono (evaluate_space source exponent confidence input hw) ?_
  intro out ho
  exact ho.trans ((Nat.mul_le_mul_left n (Nat.pow_le_pow_left (hC n (by omega)) 14)).trans_eq (by rw [mul_pow, ← pow_mul]; ring))

end StreamingReachability.Exact.Implementation.Measured
