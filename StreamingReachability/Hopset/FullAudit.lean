module

public import StreamingReachability.Hopset.FullTrace
public import StreamingReachability.Hopset.PathAudit

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

def fullAuditLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) : Law ((Fin n → ℕ) × List (GeometricEntry n cfg)) :=
  (Law.family n (fun _ =>
    Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).bind fun ranks =>
    (fullTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ]).map
      fun trace => (ranks, trace)

theorem fullAudit_stopped (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (f : (Fin n → ℕ) × List (GeometricEntry n cfg) → ℝ) :
    (fullAuditLaw cfg hn stored input).expect (fun sample =>
      f (sample.1, stopTrace cfg stored input sample.2)) =
      (geometricAuditLaw cfg hn stored input).expect f := by
  simp only [fullAuditLaw, geometricAuditLaw, Law.expect_bind, Law.expect_map]
  apply congrArg (Law.family n (fun _ =>
    Ranks.firstHit (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).expect
  funext ranks
  exact fullTrace_stopped cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 [Finset.univ]
    (fun trace => f (ranks, trace))

theorem fullAudit_stopped_probability (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (P : (Fin n → ℕ) × List (GeometricEntry n cfg) → Prop) :
    (fullAuditLaw cfg hn stored input).prob (fun sample =>
      P (sample.1, stopTrace cfg stored input sample.2)) =
      (geometricAuditLaw cfg hn stored input).prob P :=
  fullAudit_stopped cfg hn stored input (fun sample => if P sample then 1 else 0)

def FullResourceFit (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (sample : (Fin n → ℕ) × List (GeometricEntry n cfg)) : Prop :=
  TraceGood cfg stored input sample.2 ∧
    ResourceFit cfg stored input (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase)

theorem fullFit_iff_stopped (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
    (hlen : trace.length = cfg.maximumLevel + 1) :
    FullResourceFit cfg stored input (ranks, trace) ↔
      ResourceFit cfg stored input (Vector.ofFn ranks, (stopTrace cfg stored input trace).map GeometricEntry.erase) := by
  constructor
  · rintro ⟨hg, hfit⟩
    rwa [(stopTrace_eq_iff cfg stored input trace).mpr hg]
  · intro hfit
    have hs : (stopTrace cfg stored input trace).length = trace.length := by
      have h := hfit.1
      simpa only [List.length_map, hlen] using h
    have he := stopTrace_eq_of_length cfg stored input trace hs
    exact ⟨(stopTrace_eq_iff cfg stored input trace).mp he, by simpa only [he] using hfit⟩

theorem fullAudit_length (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) :
    Early.Sampling.Holds (fullAuditLaw cfg hn stored input) (fun sample => sample.2.length = cfg.maximumLevel + 1) := by
  apply Early.Sampling.holds_bind
  intro ranks
  refine Early.Sampling.holds_map (fullTrace_length cfg hn stored input (Vector.ofFn ranks)
    (cfg.maximumLevel + 1) 0 [Finset.univ]) (fun trace => (ranks, trace)) _ ?_
  intro trace ht
  exact ht

theorem full_resources (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 1 / 256 ≤ (fullAuditLaw cfg hn stored input).prob (FullResourceFit cfg stored input) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  change 1 - 1 / 256 ≤ (fullAuditLaw cfg hn stored input).prob (FullResourceFit cfg stored input)
  have heq : (fullAuditLaw cfg hn stored input).prob (FullResourceFit cfg stored input) =
      (geometricAuditLaw cfg hn stored input).prob (fun sample =>
        ResourceFit cfg stored input (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase)) := by
    calc
      _ = (fullAuditLaw cfg hn stored input).prob (fun sample =>
          ResourceFit cfg stored input (Vector.ofFn sample.1,
            (stopTrace cfg stored input sample.2).map GeometricEntry.erase)) := by
        unfold Law.prob
        apply Reference.expect_congr_on
        refine Early.Sampling.holds_mono (fullAudit_length cfg hn stored input) ?_
        intro sample hlen
        exact congrArg (fun P : Prop => @ite ℝ P (Classical.propDecidable P) 1 0)
          (propext (fullFit_iff_stopped cfg stored input sample.1 sample.2 hlen))
      _ = _ := fullAudit_stopped cfg hn stored input (fun sample =>
        if ResourceFit cfg stored input (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase) then 1 else 0)
  rw [heq]
  exact geometric_resources hn hn₂ accuracy x delta ha hd stored input hs hp hsize

end

end StreamingReachability.Hopset.Batched
