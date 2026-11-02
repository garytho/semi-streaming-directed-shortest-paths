module

public import StreamingSSSP.Hopset.EarlyPathProbability
public import StreamingSSSP.Hopset.PathReplayLaw
public import StreamingSSSP.Hopset.TrialSurvival

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

namespace Batched

def geometricAuditLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) : Law ((Fin n → ℕ) × List (GeometricEntry n cfg)) :=
  (Law.family n (fun _ =>
    Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).bind fun ranks =>
    (geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ]).map
      fun trace => (ranks, trace)

theorem geometricAudit_erase (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (f : Vector ℕ n × List (Entry n) → ℝ) :
    (geometricAuditLaw cfg hn stored input).expect (fun sample =>
      f (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase)) =
      (auditLaw cfg hn stored input).expect f := by
  simp only [geometricAuditLaw, auditLaw, Law.expect_bind, Law.expect_map]
  apply congrArg (Law.family n (fun _ =>
    Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).expect
  funext ranks
  exact geometricTrace_erase cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ]
    (fun trace => f (Vector.ofFn ranks, trace))

theorem geometricAudit_erase_probability (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (P : Vector ℕ n × List (Entry n) → Prop) :
    (geometricAuditLaw cfg hn stored input).prob (fun sample =>
      P (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase)) =
      (auditLaw cfg hn stored input).prob P :=
  geometricAudit_erase cfg hn stored input (fun sample => if P sample then 1 else 0)

theorem geometric_resources (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 1 / 256 ≤ (geometricAuditLaw cfg hn stored input).prob (fun sample =>
      ResourceFit cfg stored input (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase)) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  change 1 - 1 / 256 ≤ (geometricAuditLaw cfg hn stored input).prob (fun sample =>
    ResourceFit cfg stored input (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase))
  rw [geometricAudit_erase_probability cfg hn stored input (ResourceFit cfg stored input)]
  exact resourceFit_probability n hn hn₂ accuracy x delta ha hd stored input hs hp hsize

end Batched

namespace Following

theorem geometric_path_marginal (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (hn : 0 < n) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (hqueue : root.queue = [Finset.univ])
    (hlevels : cfg.earlyLevel ≤ cfg.maximumLevel + 1)
    (hprefix : ∀ i < cfg.earlyLevel,
      i < (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel).length ∧
      (((PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel).take i).map Rate.value).sum ≤ 1 / 2)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (f : Option (State cfg stored input cfg.earlyLevel) → ℝ) :
    (Batched.geometricAuditLaw cfg hn stored input).expect (fun sample =>
        f (replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control))) =
      (pathStateLaw cfg (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel)
        hnum stored input root cfg.earlyLevel).expect f := by
  let ps := PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel
  calc
    _ = (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
        (fixedPathStateLaw cfg hnum stored input root ranks cfg.earlyLevel).expect f) := by
      simp only [Batched.geometricAuditLaw, Law.expect_bind, Law.expect_map]
      apply congrArg (Law.family n (fun _ => Ranks.firstHit ps)).expect
      funext ranks
      have h := geometric_replay_fixed cfg hnum stored input hn root ranks (cfg.maximumLevel + 1) hlevels hs hp hsize f
      simpa only [hqueue] using h
    _ = _ := pathState_equiv cfg ps hnum stored input root hprefix cfg.earlyLevel f

theorem geometric_path_probability (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (hn : 0 < n) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (hqueue : root.queue = [Finset.univ])
    (hlevels : cfg.earlyLevel ≤ cfg.maximumLevel + 1)
    (hprefix : ∀ i < cfg.earlyLevel,
      i < (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel).length ∧
      (((PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel).take i).map Rate.value).sum ≤ 1 / 2)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (P : Option (State cfg stored input cfg.earlyLevel) → Prop) :
    (Batched.geometricAuditLaw cfg hn stored input).prob (fun sample =>
        P (replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control))) =
      (pathStateLaw cfg (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel)
        hnum stored input root cfg.earlyLevel).prob P :=
  geometric_path_marginal cfg hnum hn stored input root hqueue hlevels hprefix hs hp hsize
    (fun state => if P state then 1 else 0)

theorem geometric_fast_pieces (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    1 - 1 / 32 ≤ (Batched.geometricAuditLaw cfg hn stored input).prob (fun sample =>
      ∀ r ≤ cfg.earlyLevel,
        (observedCount hnum r
          (replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control)) : ℝ) ≤
            pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let good := fun state : Option (State cfg stored input cfg.earlyLevel) =>
    ∀ r ≤ cfg.earlyLevel, (observedCount hnum r state : ℝ) ≤
      pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r
  have hprefix : ∀ i < cfg.earlyLevel,
      i < (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel).length ∧
      (((PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel).take i).map Rate.value).sum ≤ 1 / 2 := by
    intro i hi
    have h := Reference.calibrated_prefix_budget n hn accuracy x delta (volume stored.blocks) ha hd i hi
    exact ⟨h.1, h.2.1⟩
  change 1 - 1 / 32 ≤ (Batched.geometricAuditLaw cfg hn stored input).prob (fun sample =>
    good (replayEarly cfg hnum stored input root sample.1 (sample.2.map Batched.GeometricEntry.control)))
  rw [geometric_path_probability cfg hnum hn stored input root rfl (by
    exact (Parameters.threshold_le_maximum n x).trans (Nat.le_succ _)) hprefix hs hp hsize good]
  exact calibrated_fast_pieces hn accuracy x delta (volume stored.blocks) ha hd stored input Q hweight

end Following

end

end StreamingSSSP.Hopset
