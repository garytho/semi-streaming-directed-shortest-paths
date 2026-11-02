module

public import StreamingSSSP.Hopset.PathEvents
public import StreamingSSSP.Hopset.ExecutionReplay
public import StreamingSSSP.Hopset.TraceSuffix

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

structure FrontierWitness (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator) (accuracy : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg)) where
  state : State cfg stored input cfg.earlyLevel
  follow : followControls cfg hnum stored input ranks (trace.map GeometricEntry.control) (some ⟨0, root⟩) =
    some ⟨cfg.earlyLevel, state⟩
  prefixFollow : followControls cfg hnum stored input ranks
    ((trace.take cfg.earlyLevel).map GeometricEntry.control) (some ⟨0, root⟩) =
      some ⟨cfg.earlyLevel, state⟩
  queue_eq : state.queue = afterQueue root.queue (trace.take cfg.earlyLevel)
  late_valid : FullValid cfg stored input (Vector.ofFn ranks) (cfg.maximumLevel - cfg.earlyLevel + 1)
    cfg.earlyLevel state.queue (trace.drop cfg.earlyLevel)
  late_good : TraceGood cfg stored input (trace.drop cfg.earlyLevel)
  count : (state.primeCount hnum : ℝ) ≤
    pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) cfg.earlyLevel
  work_eq : fullLateWork cfg hn hnum stored input root ranks
      (pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) cfg.earlyLevel) trace =
    lateFrontierWork cfg hn stored input cfg.earlyLevel (cfg.maximumLevel - cfg.earlyLevel) state.queue
      (splitAll cfg cfg.earlyLevel hnum state.paths) (trace.drop cfg.earlyLevel)

theorem PathEvent.frontier {cfg : Config} (hn : 0 < n) (hnum : 0 < cfg.initialNumerator) (accuracy : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
    (hEarly : cfg.earlyLevel ≤ cfg.maximumLevel)
    (he : PathEvent cfg hn hnum accuracy stored input root (ranks, trace))
    (hv : FullValid cfg stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue trace) :
    Nonempty (FrontierWitness cfg hn hnum accuracy stored input root ranks trace) := by
  obtain ⟨run, htrace⟩ := hv.execution
  obtain ⟨st, hf, hp, hq⟩ := execution_replay hnum run (Nat.zero_le _) (by omega) root rfl
  simp only [htrace, Vector.get_ofFn, Nat.sub_zero] at hf hp hq
  have hfull : replayEarly cfg hnum stored input root ranks (trace.map GeometricEntry.control) = some st := by
    simp only [replayEarly, hf, unpackState, ↓reduceDIte]
  have hpre : replayEarly cfg hnum stored input root ranks
      ((trace.take cfg.earlyLevel).map GeometricEntry.control) = some st := by
    simp only [replayEarly, hp, unpackState, ↓reduceDIte]
  have hfast := he.2.1
  rw [hfull] at hfast
  let T := pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ)
    (Parameters.ell n : ℝ) cfg.earlyLevel
  have hcount : (st.primeCount hnum : ℝ) ≤ T := by
    have h := hfast cfg.earlyLevel le_rfl
    simpa only [observedCount, lt_self_iff_false, ↓reduceIte] using h
  have hsub : cfg.maximumLevel + 1 - cfg.earlyLevel = cfg.maximumLevel - cfg.earlyLevel + 1 := by omega
  have hvalid : FullValid cfg stored input (Vector.ofFn ranks) (cfg.maximumLevel - cfg.earlyLevel + 1)
      cfg.earlyLevel st.queue (trace.drop cfg.earlyLevel) := by
    rw [hq]
    simpa only [Nat.zero_add, hsub] using hv.drop cfg.earlyLevel (by omega)
  have hgood := he.1.1.drop cfg.earlyLevel
  have hready : st.queue = afterQueue root.queue (trace.take cfg.earlyLevel) ∧
      AllGood cfg stored input cfg.earlyLevel st.queue ∧ (st.primeCount hnum : ℝ) ≤ T :=
    ⟨hq, hvalid.current_good hgood, hcount⟩
  have hwork : fullLateWork cfg hn hnum stored input root ranks T trace =
      lateFrontierWork cfg hn stored input cfg.earlyLevel (cfg.maximumLevel - cfg.earlyLevel) st.queue
        (splitAll cfg cfg.earlyLevel hnum st.paths) (trace.drop cfg.earlyLevel) := by
    simp only [fullLateWork, gatedLateWork, hpre, ite_eq_left hready]
  exact ⟨⟨st, hf, hp, hq, hvalid, hgood, hcount, hwork⟩⟩

theorem fullAudit_valid (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    Early.Sampling.Holds (fullAuditLaw cfg hn stored input) (fun sample =>
      FullValid cfg stored input (Vector.ofFn sample.1) (cfg.maximumLevel + 1) 0 [Finset.univ] sample.2) := by
  apply Early.Sampling.holds_bind
  intro ranks
  refine Early.Sampling.holds_map (fullTrace_valid cfg hn stored input (Vector.ofFn ranks)
    (cfg.maximumLevel + 1) 0 [Finset.univ] hs hp hsize hnum) (fun trace => (ranks, trace)) _ ?_
  intro trace ht
  exact ht

end

end StreamingSSSP.Hopset.Following
