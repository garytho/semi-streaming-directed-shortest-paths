module

public import StreamingReachability.Exact.WordComplexity

@[expose] public section

namespace StreamingReachability

open scoped Classical

/-- Exact distances, unreachable infinity, and an original-edge shortest-path
tree for the actual causal streaming implementation, on every positive size. -/
theorem exact_sssp_correct {n : ℕ} (source : Fin n) (exponent confidence : ℕ)
    (input : List (StoredEdges.Edge n)) (hw : ∀ e ∈ input, e.weight ≤ n ^ exponent) :
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Exact.Implementation.Measured.evaluate source exponent confidence input).prob
        (fun out => Exact.Implementation.CorrectResult input source out.result.result) :=
  Exact.Implementation.Measured.evaluate_correct source exponent confidence input hw

/-- The manuscript's streaming main theorem, with quantified eventual pass
exponent, near-linear word space, logarithmic register width, and actual
request/reply encodings. Correctness has no asymptotic-size restriction. -/
theorem streaming_sssp (exponent confidence : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ passConstant : ℝ, 0 < passConstant ∧ ∃ spaceConstant spaceDegree bitConstant threshold : ℕ,
      513 ≤ threshold ∧ ∀ n ≥ threshold, ∀ source : Fin n, ∀ input : List (StoredEdges.Edge n),
        (∀ e ∈ input, e.weight ≤ n ^ exponent) →
        (1 - 1 / (n : ℝ) ^ confidence ≤
          (Exact.Implementation.Measured.evaluate source exponent confidence input).prob
            (fun out => Exact.Implementation.CorrectResult input source out.result.result)) ∧
        Early.Sampling.Holds (Exact.Implementation.Measured.evaluate source exponent confidence input)
          (fun out =>
            (out.passes : ℝ) ≤ passConstant * (n : ℝ) ^ (1 / 3 + epsilon) ∧
            Exact.Implementation.Measured.workingCells exponent confidence out ≤
              spaceConstant * n * Parameters.ell n ^ spaceDegree ∧
            ∃ encoded : List (Fin (2 ^ Exact.Implementation.Measured.wordBits n exponent confidence)),
              encoded.map Fin.val = Exact.Implementation.Measured.traceWords out.result.trace ∧
                encoded.length = (Exact.Implementation.Measured.traceWords out.result.trace).length) ∧
        Exact.Implementation.Measured.wordBits n exponent confidence ≤ bitConstant * Parameters.ell n := by
  obtain ⟨P, hP, N, hpass⟩ := Exact.Implementation.Measured.exact_streaming_passes exponent confidence he
  obtain ⟨S, d, hspace⟩ := Exact.Implementation.Measured.exact_streaming_space exponent confidence
  obtain ⟨B, hbits⟩ := Exact.Implementation.Measured.wordBits_logarithmic exponent confidence
  refine ⟨P, hP, S, d, B, max N 513, le_max_right _ _, ?_⟩
  intro n hn source input hw
  have hnN : N ≤ n := (le_max_left N 513).trans hn
  have hnlarge : 513 ≤ n := (le_max_right N 513).trans hn
  have hp := hpass n hnN source input hw
  have hs := hspace n hnlarge source input hw
  have hwritten := Exact.Implementation.Measured.exact_streaming_word_encoding source exponent confidence input hw
  refine ⟨exact_sssp_correct source exponent confidence input hw, ?_, hbits n (by omega)⟩
  intro atom hatom
  exact ⟨hp atom hatom, hs atom hatom, hwritten atom hatom⟩

end StreamingReachability
