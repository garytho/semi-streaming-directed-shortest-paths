module

public import StreamingSSSP.Hopset.TraceShape
public import StreamingSSSP.Hopset.GlobalRecords

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def globalState (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) : State n :=
  let sets : Vector (Finset (Fin n)) 1 := Vector.replicate 1 Finset.univ
  let targets := globalTargets cfg rank
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg 0 stored.blocks sets targets) cfg.blockSize) input).records
  ⟨{ explicit := emittedStars cfg targets reply }, n, recordCharge stored.blocks reply⟩

def auditLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) : Law (Vector ℕ n × List (Entry n)) :=
  (Law.family n (fun _ =>
    Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).bind fun ranks =>
    (traceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ]).map
      fun trace => (Vector.ofFn ranks, trace)

theorem trialLaw_globalState (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) :
    trialLaw cfg hn stored input =
      if n ≤ cfg.copyCap then
        (Law.family n (fun _ =>
          Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).bind fun ranks =>
          let rank := Vector.ofFn ranks
          let state := globalState cfg stored input rank
          if state.records ≤ cfg.recordCap then
            levelsLaw cfg hn stored input rank (cfg.maximumLevel + 1) 0 [Finset.univ] state
          else Law.pure none
      else Law.pure none := rfl

theorem audit_valid (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) :
    Early.Sampling.Holds (auditLaw cfg hn stored input) (fun sample =>
      ValidTrace cfg hn stored input sample.1 (cfg.maximumLevel + 1) 0 [Finset.univ] sample.2) := by
  unfold auditLaw
  apply Early.Sampling.holds_bind
  intro ranks
  refine Early.Sampling.holds_map
    (traceLaw_valid cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ])
    (fun trace => (Vector.ofFn ranks, trace)) _ ?_
  intro trace ht
  exact ht

theorem accepted_nonempty_records (cfg : Config) (state : State n) (entry : Entry n)
    (trace : List (Entry n)) (h : AcceptedTrace cfg state (entry :: trace)) :
    state.records ≤ cfg.recordCap :=
  (Nat.le_add_right state.records entry.step.records).trans h.1.1

theorem audit_success_le_trial (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hc : n ≤ cfg.copyCap) (P : Output n → Prop) :
    (auditLaw cfg hn stored input).prob (fun sample =>
        sample.2.length = cfg.maximumLevel + 1 ∧
          AcceptedTrace cfg (globalState cfg stored input sample.1) sample.2 ∧
          P (replay (globalState cfg stored input sample.1) sample.2).output) ≤
      (trialLaw cfg hn stored input).prob (OutputSatisfies P) := by
  rw [auditLaw, Law.prob_bind]
  simp_rw [Law.prob_map]
  rw [trialLaw_globalState, ite_eq_left hc, Law.prob_bind]
  apply Law.expect_mono
  intro ranks
  let rank := Vector.ofFn ranks
  let state := globalState cfg stored input rank
  change (traceLaw cfg hn stored input rank (cfg.maximumLevel + 1) 0 [Finset.univ]).prob
      (fun trace => trace.length = cfg.maximumLevel + 1 ∧
        AcceptedTrace cfg state trace ∧ P (replay state trace).output) ≤
    (if state.records ≤ cfg.recordCap then
      levelsLaw cfg hn stored input rank (cfg.maximumLevel + 1) 0 [Finset.univ] state
      else Law.pure none).prob (OutputSatisfies P)
  by_cases hr : state.records ≤ cfg.recordCap
  · rw [ite_eq_left hr]
    exact trace_success_le cfg hn stored input rank _ _ _ state P
  · rw [ite_eq_right hr]
    have hfalse :
        (fun trace : List (Entry n) => trace.length = cfg.maximumLevel + 1 ∧
          AcceptedTrace cfg state trace ∧ P (replay state trace).output) = fun _ => False := by
      funext trace
      apply propext
      constructor
      · intro h
        cases trace with
        | nil => simp at h
        | cons entry trace => exact hr (accepted_nonempty_records cfg state entry trace h.2.1)
      · exact False.elim
    rw [hfalse, Law.prob_false]
    simp [Law.prob, OutputSatisfies]

theorem audit_success_le_code (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hc : n ≤ cfg.copyCap)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (P : Output n → Prop) :
    (auditLaw cfg hn stored input).prob (fun sample =>
        sample.2.length = cfg.maximumLevel + 1 ∧
          AcceptedTrace cfg (globalState cfg stored input sample.1) sample.2 ∧
          P (replay (globalState cfg stored input sample.1) sample.2).output) ≤
      (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob (OutputSatisfies P) := by
  have he := fixedGuess_equiv cfg hn stored input hs hp hsize
    (fun result => if OutputSatisfies P result then (1 : ℝ) else 0)
  change _ ≤ (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).expect
    (fun result => if OutputSatisfies P result then (1 : ℝ) else 0)
  rw [he]
  exact audit_success_le_trial cfg hn stored input hc P

theorem calibrated_trace_marginal (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (f : List (Entry n) → ℝ) :
    (auditLaw (Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd) hn stored input).expect
        (fun sample => f sample.2) =
      (calibratedTraceLaw n hn accuracy x delta ha hd stored input).expect f := by
  simp only [auditLaw, calibratedTraceLaw, Law.expect_bind, Law.expect_map]
  rfl

theorem audit_rank_marginal (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (f : Vector ℕ n → ℝ) :
    (auditLaw cfg hn stored input).expect (fun sample => f sample.1) =
      (Law.family n (fun _ =>
        Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).expect
        (fun ranks => f (Vector.ofFn ranks)) := by
  simp only [auditLaw, Law.expect_bind, Law.expect_map, Law.expect_const]

end

end StreamingSSSP.Hopset.Batched
