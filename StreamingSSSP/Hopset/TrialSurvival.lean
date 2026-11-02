module

public import StreamingSSSP.Hopset.AuditMoments

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

theorem markov_small {A : Type*} (mu : Law A) (f : A → ℕ) (budget : ℕ) (hb : 0 < budget)
    (hmean : 1024 * mu.expect (fun a => (f a : ℝ)) ≤ (budget : ℝ)) :
    mu.prob (fun a => budget < f a) ≤ 1 / 1024 := by
  have hbR : (0 : ℝ) < budget := by exact_mod_cast hb
  apply (mu.prob_mono (P := fun a => budget < f a) (Q := fun a => (budget : ℝ) ≤ f a)
    (by intro a ha; exact_mod_cast ha.le)).trans
  apply (mu.markov (fun a => (f a : ℝ)) (fun _ => Nat.cast_nonneg _) (budget : ℝ) hbR).trans
  apply (div_le_iff₀ hbR).mpr
  nlinarith

theorem audit_resources_small (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    let mu := auditLaw cfg hn stored input
    mu.prob (fun sample => cfg.copyCap < traceCost copyReward sample.2) ≤ 1 / 1024 ∧
      mu.prob (fun sample =>
        cfg.recordCap < (globalState cfg stored input sample.1).records + traceCost recordReward sample.2) ≤ 1 / 1024 ∧
      mu.prob (fun sample => cfg.blockCap < traceCost blockReward sample.2) ≤ 1 / 1024 := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let mu := auditLaw cfg hn stored input
  have he := Parameters.ell_pos n
  have hk : 0 < Parameters.k n := by have := Parameters.k_large n; omega
  have hcopy : 0 < cfg.copyCap := by
    change 0 < 2 ^ 30 * n * Parameters.ell n ^ 4
    positivity
  have hrecords : 0 < cfg.recordCap := by
    change 0 < 2 ^ 30 * Parameters.k n ^ (Parameters.advance n accuracy + 2) *
      Parameters.ell n ^ 4 * (n + volume stored.blocks)
    positivity
  have hblocks : 0 < cfg.blockCap := by
    change 0 < 2 ^ 30 * n * Parameters.k n * Parameters.ell n ^ 4
    positivity
  refine ⟨?_, ?_, ?_⟩
  · apply markov_small mu (fun sample => traceCost copyReward sample.2) cfg.copyCap hcopy
    exact (mul_le_mul_of_nonneg_left
      (expected_audit_copies n hn accuracy x delta ha hd stored input hs hp hsize)
      (by norm_num : (0 : ℝ) ≤ 1024)).trans (Parameters.copy_mean_slack n)
  · apply markov_small mu
      (fun sample => (globalState cfg stored input sample.1).records + traceCost recordReward sample.2)
      cfg.recordCap hrecords
    have hmean :
        mu.expect (fun sample =>
          (((globalState cfg stored input sample.1).records + traceCost recordReward sample.2 : ℕ) : ℝ)) ≤
        400 * (Parameters.k n : ℝ) ^ Parameters.advance n accuracy * Parameters.ell n *
            (n + volume stored.blocks) +
          Reference.recordVisitBudget n accuracy * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) *
            (n + volume stored.blocks) := by
      calc
        _ = mu.expect (fun sample => ((globalState cfg stored input sample.1).records : ℝ) +
            (traceCost recordReward sample.2 : ℝ)) := by
          apply congrArg mu.expect
          funext sample
          exact Nat.cast_add _ _
        _ ≤ _ := expected_audit_total_records n hn accuracy x delta ha hd stored input hs hp hsize
    exact (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 1024)).trans
      (Parameters.record_mean_slack n accuracy (volume stored.blocks))
  · apply markov_small mu (fun sample => traceCost blockReward sample.2) cfg.blockCap hblocks
    exact (mul_le_mul_of_nonneg_left
      (expected_audit_blocks n hn accuracy x delta ha hd stored input hs hp hsize)
      (by norm_num : (0 : ℝ) ≤ 1024)).trans (Parameters.block_mean_slack n)

theorem resourceFit_probability (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 1 / 256 ≤ (auditLaw cfg hn stored input).prob (ResourceFit cfg stored input) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let mu := auditLaw cfg hn stored input
  let short := fun sample : Vector ℕ n × List (Entry n) => sample.2.length ≠ cfg.maximumLevel + 1
  let copies := fun sample : Vector ℕ n × List (Entry n) => cfg.copyCap < traceCost copyReward sample.2
  let records := fun sample : Vector ℕ n × List (Entry n) =>
    cfg.recordCap < (globalState cfg stored input sample.1).records + traceCost recordReward sample.2
  let blocks := fun sample : Vector ℕ n × List (Entry n) => cfg.blockCap < traceCost blockReward sample.2
  have hshort : mu.prob short ≤ 1 / 1024 :=
    audit_short_small n hn hn2 accuracy x delta ha hd stored input hs hp hsize
  have hresources := audit_resources_small n hn accuracy x delta ha hd stored input hs hp hsize
  have hcopies : mu.prob copies ≤ 1 / 1024 := hresources.1
  have hrecords : mu.prob records ≤ 1 / 1024 := hresources.2.1
  have hblocks : mu.prob blocks ≤ 1 / 1024 := hresources.2.2
  have he :
      mu.prob (fun sample => ¬ ResourceFit cfg stored input sample) =
        mu.prob (fun sample => short sample ∨ copies sample ∨ records sample ∨ blocks sample) := by
    apply Law.prob_congr
    intro sample
    simp only [ResourceFit, short, copies, records, blocks, not_and_or, not_le]
  have hu₁ := mu.prob_union short (fun sample => copies sample ∨ records sample ∨ blocks sample)
  have hu₂ := mu.prob_union copies (fun sample => records sample ∨ blocks sample)
  have hu₃ := mu.prob_union records blocks
  have hbad : mu.prob (fun sample => ¬ ResourceFit cfg stored input sample) ≤ 1 / 256 := by
    rw [he]
    linarith
  have hcompl := mu.prob_compl (ResourceFit cfg stored input)
  change 1 - 1 / 256 ≤ mu.prob (ResourceFit cfg stored input)
  linarith

theorem fixedGuess_noAbort (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 1 / 256 ≤
      (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob
        (OutputSatisfies (fun _ => True)) :=
  (resourceFit_probability n hn hn2 accuracy x delta ha hd stored input hs hp hsize).trans
    (resourceFit_probability_le_code n hn accuracy x delta ha hd stored input hs hp hsize hpoly)

theorem fixedGuess_viewed_noAbort {n : ℕ} {E : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) (hn : 0 < n) (hn2 : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input.filterMap view, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 1 / 256 ≤
      (Code.evaluate (Backend.guardedViewedHandler view input) (fixedGuess cfg hn stored)).prob
        (OutputSatisfies (fun _ => True)) := by
  dsimp only
  rw [Backend.guardedViewedHandler_eq]
  exact fixedGuess_noAbort n hn hn2 accuracy x delta ha hd stored _ hs hp hsize hpoly

end

end StreamingSSSP.Hopset.Batched
