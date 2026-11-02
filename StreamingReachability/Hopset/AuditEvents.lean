module

public import StreamingReachability.Hopset.AuditLaw

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def ResourceFit (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sample : Vector ℕ n × List (Entry n)) : Prop :=
  sample.2.length = cfg.maximumLevel + 1 ∧
    traceCost copyReward sample.2 ≤ cfg.copyCap ∧
    (globalState cfg stored input sample.1).records + traceCost recordReward sample.2 ≤ cfg.recordCap ∧
    traceCost blockReward sample.2 ≤ cfg.blockCap

theorem prob_mono_supported {A : Type*} (mu : Law A) (P Q : A → Prop)
    (h : Early.Sampling.Holds mu (fun a => P a → Q a)) : mu.prob P ≤ mu.prob Q := by
  unfold Law.prob
  apply Early.Sampling.expect_mono_on
  refine Early.Sampling.holds_mono h ?_
  intro a hpq
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

theorem resourceFit_accepted (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (sample : Vector ℕ n × List (Entry n)) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    ValidTrace cfg hn stored input sample.1 (cfg.maximumLevel + 1) 0 [Finset.univ] sample.2 →
      ResourceFit cfg stored input sample →
        AcceptedTrace cfg (globalState cfg stored input sample.1) sample.2 := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  dsimp only
  intro htrace hfit
  apply final_caps_accepted
  · exact calibrated_trace_blocks_small n hn accuracy x delta ha hd stored input sample.1
      hs hp hsize hpoly (Parameters.maximumLevel n + 1) 0 [Finset.univ] sample.2 htrace (by omega)
  · rw [complete_copy_cost sample.2 htrace hfit.1 (Parameters.threshold_le_maximum n x)
      (globalState cfg stored input sample.1) rfl]
    exact hfit.2.1
  · rw [replay_records]
    exact hfit.2.2.1
  · rw [replay_blocks]
    have hb : volume (globalState cfg stored input sample.1).output.blocks = 0 := rfl
    rw [hb, zero_add]
    exact hfit.2.2.2

theorem resourceFit_probability_le_code (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).prob (ResourceFit cfg stored input) ≤
      (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob
        (OutputSatisfies (fun _ => True)) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  calc
    _ ≤ (auditLaw cfg hn stored input).prob (fun sample =>
        sample.2.length = cfg.maximumLevel + 1 ∧
          AcceptedTrace cfg (globalState cfg stored input sample.1) sample.2 ∧ True) := by
      apply prob_mono_supported
      refine Early.Sampling.holds_mono (audit_valid cfg hn stored input) ?_
      intro sample htrace hfit
      exact ⟨hfit.1, resourceFit_accepted n hn accuracy x delta ha hd stored input
        hs hp hsize hpoly sample htrace hfit, trivial⟩
    _ ≤ _ := audit_success_le_code cfg hn stored input
      (Parameters.initial_copies_fit n accuracy x delta (volume stored.blocks) ha hd) hs hp hsize
      (fun _ => True)

end

end StreamingReachability.Hopset.Batched
