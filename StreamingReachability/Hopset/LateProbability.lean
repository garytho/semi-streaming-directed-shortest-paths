module

public import StreamingReachability.Hopset.LateGate
public import StreamingReachability.Hopset.FullAudit
public import StreamingReachability.Hopset.PathRoot

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

theorem full_late_mean (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) (T : ℝ) (hT : 0 ≤ T)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    (fullAuditLaw cfg hn stored input).expect (fun sample =>
      fullLateWork cfg hn hnum stored input root sample.1 T sample.2) ≤
      (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  change (fullAuditLaw cfg hn stored input).expect (fun sample =>
    fullLateWork cfg hn hnum stored input root sample.1 T sample.2) ≤ _
  simp only [fullAuditLaw, Law.expect_bind, Law.expect_map]
  calc
    _ ≤ (Law.family n (fun _ => Ranks.firstHit
        (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel))).expect
          (fun _ => (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T) := by
      apply Law.expect_mono
      intro ranks
      exact fullLateWork_mean hn accuracy x delta (volume stored.blocks) ha hd stored input hs hp hsize root ranks T hT
    _ = _ := Law.expect_const _ _

theorem full_late_fast (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) (T : ℝ) (hT : 0 < T)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    1 - 1 / 32 ≤ (fullAuditLaw cfg hn stored input).prob (fun sample =>
      fullLateWork cfg hn hnum stored input root sample.1 T sample.2 ≤
        32 * ((14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T)) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let mu := fullAuditLaw cfg hn stored input
  let f := fun sample : (Fin n → ℕ) × List (GeometricEntry n cfg) =>
    fullLateWork cfg hn hnum stored input root sample.1 T sample.2
  let bound := (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T
  have hb : 0 < bound := by dsimp only [bound]; positivity
  have hf (sample : (Fin n → ℕ) × List (GeometricEntry n cfg)) : 0 ≤ f sample :=
    gatedLateWork_nonneg cfg hn hnum stored input root sample.1 T _ _
  have hm : mu.expect f ≤ bound := full_late_mean hn accuracy x delta ha hd stored input Q T hT.le hs hp hsize
  have hbad : mu.prob (fun sample => 32 * bound ≤ f sample) ≤ 1 / 32 := by
    calc
      _ ≤ mu.expect f / (32 * bound) := mu.markov f hf _ (by positivity)
      _ ≤ bound / (32 * bound) := div_le_div_of_nonneg_right hm (by positivity)
      _ = _ := by field_simp [hb.ne']
  have hcomp := mu.prob_compl (fun sample => 32 * bound ≤ f sample)
  have hi : mu.prob (fun sample => ¬ 32 * bound ≤ f sample) ≤
      mu.prob (fun sample => f sample ≤ 32 * bound) :=
    mu.prob_mono (fun sample h => (lt_of_not_ge h).le)
  change 1 - 1 / 32 ≤ mu.prob (fun sample => f sample ≤ 32 * bound)
  linarith

end

end StreamingReachability.Hopset.Following
