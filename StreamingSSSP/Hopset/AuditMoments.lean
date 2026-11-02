module

public import StreamingSSSP.Hopset.AuditEvents
public import StreamingSSSP.Hopset.CapSlack

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

theorem expected_audit_copies (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).expect (fun sample => (traceCost copyReward sample.2 : ℝ)) ≤
      2 * n * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) :=
  (calibrated_trace_marginal n hn accuracy x delta ha hd stored input _).le.trans
    (expected_trace_copies n hn accuracy x delta ha hd stored input hs hp hsize)

theorem expected_audit_records (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).expect (fun sample => (traceCost recordReward sample.2 : ℝ)) ≤
      Reference.recordVisitBudget n accuracy * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) *
        (n + volume stored.blocks) :=
  (calibrated_trace_marginal n hn accuracy x delta ha hd stored input _).le.trans
    (expected_trace_records n hn accuracy x delta ha hd stored input hs hp hsize)

theorem expected_audit_blocks (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).expect (fun sample => (traceCost blockReward sample.2 : ℝ)) ≤
      (400 * (Parameters.k n : ℝ) * Parameters.ell n) *
        (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) * n :=
  (calibrated_trace_marginal n hn accuracy x delta ha hd stored input _).le.trans
    (expected_trace_blocks n hn accuracy x delta ha hd stored input hs hp hsize)

theorem expected_audit_bad (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).expect
        (fun sample => (traceCost (badReward cfg stored input) sample.2 : ℝ)) ≤
      4 * (n : ℝ) ^ 3 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ) *
        Real.exp (-25 * Parameters.ell n) :=
  (calibrated_trace_marginal n hn accuracy x delta ha hd stored input _).le.trans
    (expected_trace_bad n hn accuracy x delta ha hd stored input hs hp hsize)

theorem expected_audit_globals (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).expect
        (fun sample => ((globalState cfg stored input sample.1).records : ℝ)) ≤
      400 * (Parameters.k n : ℝ) ^ Parameters.advance n accuracy * Parameters.ell n *
        (n + volume stored.blocks) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  dsimp only
  change (auditLaw cfg hn stored input).expect
    (fun sample => ((globalState cfg stored input sample.1).records : ℝ)) ≤ _
  rw [audit_rank_marginal cfg hn stored input
    (fun rank => ((globalState cfg stored input rank).records : ℝ))]
  change (Law.family n (fun _ => Ranks.firstHit (Reference.earlyRates n hn x))).expect
    (fun ranks => ((globalState cfg stored input (Vector.ofFn ranks)).records : ℝ)) ≤ _
  have he (ranks : Fin n → ℕ) :
      ((globalState cfg stored input (Vector.ofFn ranks)).records : ℝ) =
        (Reference.globalRecords cfg stored input ranks : ℝ) := by
    change (recordCharge stored.blocks (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg 0 stored.blocks (Vector.replicate 1 Finset.univ)
        (globalTargets cfg (Vector.ofFn ranks))) cfg.blockSize) input).records : ℝ) = _
    rw [raw_global_records cfg stored input hn hs hp hsize (Vector.ofFn ranks)]
    simp only [Vector.get_ofFn]
  simp_rw [he]
  exact Reference.expected_global_records n hn accuracy x delta (volume stored.blocks) ha hd stored input

theorem expected_audit_total_records (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).expect
        (fun sample => ((globalState cfg stored input sample.1).records + traceCost recordReward sample.2 : ℝ)) ≤
      400 * (Parameters.k n : ℝ) ^ Parameters.advance n accuracy * Parameters.ell n *
          (n + volume stored.blocks) +
        Reference.recordVisitBudget n accuracy * (2 * ((Parameters.maximumLevel n + 1 : ℕ) : ℝ)) *
          (n + volume stored.blocks) := by
  simp only [Law.expect_add]
  exact add_le_add (expected_audit_globals n hn accuracy x delta ha hd stored input hs hp hsize)
    (expected_audit_records n hn accuracy x delta ha hd stored input hs hp hsize)

theorem audit_short_le_bad {n : ℕ} (cfg : Config) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    (auditLaw cfg hn stored input).prob (fun sample => sample.2.length ≠ cfg.maximumLevel + 1) ≤
      (auditLaw cfg hn stored input).expect
        (fun sample => (traceCost (badReward cfg stored input) sample.2 : ℝ)) := by
  simp only [auditLaw, Law.prob_bind, Law.expect_bind, Law.prob_map, Law.expect_map]
  apply Law.expect_mono
  intro ranks
  apply short_probability_le_bad
  intro S hS
  have he := List.mem_singleton.mp hS
  subst S
  exact Reference.root_balls_good cfg stored input Finset.univ

theorem audit_short_small (n : ℕ) (hn : 0 < n) (hn2 : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (auditLaw cfg hn stored input).prob (fun sample => sample.2.length ≠ cfg.maximumLevel + 1) ≤
      1 / 1024 := by
  apply (audit_short_le_bad _ hn stored input).trans
  apply (expected_audit_bad n hn accuracy x delta ha hd stored input hs hp hsize).trans
  exact (Reference.bad_weight_negligible n hn2).trans (Parameters.inverse_tenth_small n hn2)

end

end StreamingSSSP.Hopset.Batched
