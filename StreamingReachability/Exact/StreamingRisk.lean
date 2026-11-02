module

public import StreamingReachability.Exact.StreamingFresh

@[expose] public section

namespace StreamingReachability.Exact.Implementation

open scoped Classical
open DescriptorProgram

noncomputable section

variable {n : ℕ} {A : Type*}

def freshCount : List (Answered n) → ℕ
  | [] => 0
  | entry :: trace => (if entry.fresh = true then 1 else 0) + freshCount trace

def badFreshCount (P : (request : Request n) → request.Reply → Prop) : List (Answered n) → ℕ
  | [] => 0
  | entry :: trace =>
      (if entry.fresh = true ∧ ¬ P entry.request entry.answer then 1 else 0) + badFreshCount P trace

theorem freshCount_le_length (trace : List (Answered n)) : freshCount trace ≤ trace.length := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      simp only [freshCount, List.length_cons]
      split_ifs <;> omega

theorem badFreshCount_zero (P : (request : Request n) → request.Reply → Prop) (trace : List (Answered n)) :
    badFreshCount P trace = 0 ↔ ∀ entry ∈ trace, entry.fresh = true → P entry.request entry.answer := by
  induction trace with
  | nil => simp [badFreshCount]
  | cons entry trace ih =>
      by_cases hf : entry.fresh = true <;> by_cases hp : P entry.request entry.answer <;>
        simp [badFreshCount, hf, hp, ih]

private theorem cast_indicator (P : Prop) [Decidable P] :
    ((if P then 1 else 0 : ℕ) : ℝ) = (if P then 1 else 0 : ℝ) := by
  split_ifs <;> norm_num

/-- Adaptive calls are charged when they occur; no independence of future
descriptors or a preselected collection of semantic graphs is assumed. -/
theorem execute_bad_mean (handler : (request : Request n) → Law request.Reply)
    (P : (request : Request n) → request.Reply → Prop) (delta : ℝ)
    (hfailure : ∀ request, (handler request).prob (fun answer => ¬ P request answer) ≤ delta)
    (program : Program n A) (cache : Cache n) :
    (execute handler program cache).expect (fun out => (badFreshCount P out.trace : ℝ)) ≤
      delta * (execute handler program cache).expect (fun out => (freshCount out.trace : ℝ)) := by
  induction program generalizing cache with
  | pure value => simp [execute, freshCount, badFreshCount]
  | ask request next ih =>
      cases hr : cache.response request with
      | some answer =>
          simpa only [execute, hr, Law.expect_map, Outcome.prepend, badFreshCount, freshCount,
            Bool.false_eq_true, false_and, ↓reduceIte, zero_add] using ih answer cache
      | none =>
          simp only [execute, hr, Law.expect_bind, Law.expect_map, Outcome.prepend,
            badFreshCount, freshCount, true_and, ↓reduceIte, Nat.cast_add,
            Nat.cast_one, cast_indicator]
          let mean := fun answer : request.Reply =>
            (execute handler (next answer) (cache.store request answer)).expect
              (fun out => (freshCount out.trace : ℝ))
          have hm :
              (handler request).expect (fun answer =>
                (execute handler (next answer) (cache.store request answer)).expect (fun out =>
                  (if ¬ P request answer then 1 else 0) + (badFreshCount P out.trace : ℝ))) ≤
                (handler request).expect (fun answer =>
                  (if ¬ P request answer then 1 else 0) + delta * mean answer) := by
            apply Law.expect_mono
            intro answer
            rw [Law.expect_add, Law.expect_const]
            exact add_le_add le_rfl (ih answer (cache.store request answer))
          calc
            _ ≤ (handler request).expect (fun answer =>
                (if ¬ P request answer then 1 else 0) + delta * mean answer) := hm
            _ = (handler request).prob (fun answer => ¬ P request answer) +
                delta * (handler request).expect mean := by
                  rw [Law.expect_add, Law.expect_indicator, Law.expect_mul]
            _ ≤ delta + delta * (handler request).expect mean :=
              add_le_add (hfailure request) le_rfl
            _ = _ := by
              simp only [Law.expect_add, Law.expect_const]
              ring

theorem execute_all_accurate (handler : (request : Request n) → Law request.Reply)
    (P : (request : Request n) → request.Reply → Prop) (delta : ℝ) (hd : 0 ≤ delta)
    (hfailure : ∀ request, (handler request).prob (fun answer => ¬ P request answer) ≤ delta)
    (program : Program n A) (cache : Cache n) (cap : ℕ)
    (hfresh : Early.Sampling.Holds (execute handler program cache)
      (fun out => ∀ entry ∈ out.trace, entry.fresh = true))
    (hcount : Early.Sampling.Holds (execute handler program cache)
      (fun out => freshCount out.trace ≤ cap)) :
    1 - delta * (cap : ℝ) ≤ (execute handler program cache).prob
      (fun out => ∀ entry ∈ out.trace, P entry.request entry.answer) := by
  let mu := execute handler program cache
  let good := fun out : Outcome n A => ∀ entry ∈ out.trace, P entry.request entry.answer
  have hbad : mu.prob (fun out => ¬ good out) ≤ mu.expect (fun out => (badFreshCount P out.trace : ℝ)) := by
    apply Early.Sampling.expect_mono_on
    refine Early.Sampling.holds_mono hfresh ?_
    intro out ho
    by_cases hg : good out
    · simp only [hg, not_true_eq_false, ↓reduceIte]
      exact Nat.cast_nonneg _
    · have hn : badFreshCount P out.trace ≠ 0 := by
        intro hz
        apply hg
        intro entry he
        exact (badFreshCount_zero P out.trace).mp hz entry he (ho entry he)
      have hn₁ : 1 ≤ badFreshCount P out.trace := by omega
      simp only [hg, not_false_eq_true, ↓reduceIte]
      exact_mod_cast hn₁
  have hc : mu.expect (fun out => (freshCount out.trace : ℝ)) ≤ (cap : ℝ) := by
    apply le_trans (Early.Sampling.expect_mono_on mu ?_)
    · exact (Law.expect_const mu (cap : ℝ)).le
    · refine Early.Sampling.holds_mono hcount ?_
      intro out ho
      exact_mod_cast ho
  have hm := execute_bad_mean handler P delta hfailure program cache
  have hb := hbad.trans (hm.trans (mul_le_mul_of_nonneg_left hc hd))
  have he := mu.prob_compl good
  change 1 - delta * (cap : ℝ) ≤ mu.prob good
  linarith

theorem root_all_accurate (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n)) :
    1 - (1 / (n : ℝ) ^ confidence) * (callCap n exponent : ℝ) ≤
      (execute (requestHandler source exponent confidence input) (DescriptorProgram.exact source exponent) {}).prob
        (fun out => ∀ entry ∈ out.trace, RequestAccurate source exponent input entry.request entry.answer) := by
  let handler := requestHandler source exponent confidence input
  let parent := parentReplyOfEdges input
  let program := DescriptorProgram.exact source exponent
  let G := preprocess (StoredEdges.graphOfEdges input) source (n ^ exponent)
  have hr := execute_run handler parent (requestHandler_parents source exponent confidence input) program {}
  have hf : ∀ request, (handler request).prob
      (fun answer => ¬ RequestAccurate source exponent input request answer) ≤ 1 / (n : ℝ) ^ confidence := by
    intro request
    have ha := requestHandler_accurate source exponent confidence input request
    rw [Law.prob_compl]
    linarith
  refine execute_all_accurate handler (RequestAccurate source exponent input)
    (1 / (n : ℝ) ^ confidence) (by positivity) hf program {} (callCap n exponent) ?_ ?_
  · exact Early.Sampling.holds_mono hr (fun out ho => ho.root_fresh input)
  · exact Early.Sampling.holds_mono hr (fun out ho =>
      (freshCount_le_length out.trace).trans (ho.exact_length G))

end

end StreamingReachability.Exact.Implementation
