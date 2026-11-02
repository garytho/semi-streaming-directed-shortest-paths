module

public import StreamingSSSP.Hopset.FullPathProbability
public import StreamingSSSP.Hopset.ReplayLive

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem prob_and_one {A : Type*} (mu : Law A) (P Q : A → Prop)
    (hP : mu.prob P = 1) (hQ : mu.prob Q = 1) : mu.prob (fun a => P a ∧ Q a) = 1 := by
  have h := prob_inter_lower mu P Q
  rw [hP, hQ] at h
  exact le_antisymm (mu.prob_le_one _) (by linarith)

def ReplayWitness (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (sample : (Fin n → ℕ) × List (Batched.GeometricEntry n cfg)) : Prop :=
  HasRun hnum root sample.1
      (replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control)) ∧
    (cfg.earlyLevel ≤ sample.2.length →
      ∃ st, replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control) = some st)

theorem geometric_replay_witness (cfg : Config) (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (hqueue : root.queue = [Finset.univ])
    (hlevels : cfg.earlyLevel ≤ cfg.maximumLevel + 1)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    (Batched.geometricAuditLaw cfg hn stored input).prob (ReplayWitness cfg hnum stored input root) = 1 := by
  simp only [Batched.geometricAuditLaw, Law.prob_bind, Law.prob_map]
  have hpoint (ranks : Fin n → ℕ) :
      (Batched.geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ]).prob
        (fun trace => ReplayWitness cfg hnum stored input root (ranks, trace)) = 1 := by
    have hr := geometric_replay_run cfg hnum hn stored input root ranks (cfg.maximumLevel + 1) hlevels hs hp hsize
    have hl := geometric_replay_live cfg hnum hn stored input root ranks (cfg.maximumLevel + 1) hs hp hsize
    have hi := prob_and_one
      (Batched.geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue) _ _ hr hl
    simpa only [ReplayWitness, hqueue] using hi
  simp_rw [hpoint, Law.expect_const]

def LiveRun (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (sample : (Fin n → ℕ) × List (Batched.GeometricEntry n cfg)) : Prop :=
  ∃ st : State cfg stored input cfg.earlyLevel,
    replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control) = some st ∧
      Run cfg hnum stored input root sample.1 cfg.earlyLevel st

theorem full_replay_certificate (cfg : Config) (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (hqueue : root.queue = [Finset.univ])
    (hlevels : cfg.earlyLevel ≤ cfg.maximumLevel + 1)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    (Batched.fullAuditLaw cfg hn stored input).prob (fun sample =>
      Batched.FullResourceFit cfg stored input sample → LiveRun cfg hnum stored input root sample) = 1 := by
  let mu := Batched.fullAuditLaw cfg hn stored input
  have hstopped : mu.prob (fun sample =>
      ReplayWitness cfg hnum stored input root (sample.1, Batched.stopTrace cfg stored input sample.2)) = 1 :=
    (Batched.fullAudit_stopped_probability cfg hn stored input (ReplayWitness cfg hnum stored input root)).trans
      (geometric_replay_witness cfg hnum hn stored input root hqueue hlevels hs hp hsize)
  have hm : mu.prob (fun sample =>
      ReplayWitness cfg hnum stored input root (sample.1, Batched.stopTrace cfg stored input sample.2)) ≤
      mu.prob (fun sample => Batched.FullResourceFit cfg stored input sample → LiveRun cfg hnum stored input root sample) := by
    apply mu.prob_mono
    intro sample hw hfit
    have he := (Batched.stopTrace_eq_iff cfg stored input sample.2).mpr hfit.1
    change HasRun hnum root sample.1
      (replayEarly cfg hnum stored input root sample.1
        ((Batched.stopTrace cfg stored input sample.2).map Batched.GeometricEntry.control)) ∧
      (cfg.earlyLevel ≤ (Batched.stopTrace cfg stored input sample.2).length →
        ∃ st, replayEarly cfg hnum stored input root sample.1
          ((Batched.stopTrace cfg stored input sample.2).map Batched.GeometricEntry.control) = some st) at hw
    rw [he] at hw
    have hlen : cfg.earlyLevel ≤ sample.2.length := by
      have h := hfit.2.1
      simp only [List.length_map] at h
      omega
    obtain ⟨st, hs⟩ := hw.2 hlen
    refine ⟨st, hs, ?_⟩
    simpa only [hs, HasRun] using hw.1
  rw [hstopped] at hm
  exact le_antisymm (mu.prob_le_one _) hm

end

end StreamingSSSP.Hopset.Following
