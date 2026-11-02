module

public import StreamingReachability.Hopset.FullPathProbability
public import StreamingReachability.Hopset.LateProbability

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

def PathEvent (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator) (accuracy : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (sample : (Fin n → ℕ) × List (GeometricEntry n cfg)) : Prop :=
  let T := pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ)
    (Parameters.ell n : ℝ) cfg.earlyLevel
  FullResourceFit cfg stored input sample ∧
    FastPieces hnum n accuracy (replayEarly cfg hnum stored input root sample.1 (sample.2.map GeometricEntry.control)) ∧
    fullLateWork cfg hn hnum stored input root sample.1 T sample.2 ≤
      32 * ((14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T)

theorem full_path_event (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    1 - 17 / 256 ≤ (fullAuditLaw cfg hn stored input).prob (PathEvent cfg hn hnum accuracy stored input root) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let mu := fullAuditLaw cfg hn stored input
  let T := pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ)
    (Parameters.ell n : ℝ) cfg.earlyLevel
  let early := fun sample : (Fin n → ℕ) × List (GeometricEntry n cfg) =>
    FullResourceFit cfg stored input sample ∧ FastPieces hnum n accuracy
      (replayEarly cfg hnum stored input root sample.1 (sample.2.map GeometricEntry.control))
  let late := fun sample : (Fin n → ℕ) × List (GeometricEntry n cfg) =>
    fullLateWork cfg hn hnum stored input root sample.1 T sample.2 ≤
      32 * ((14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T)
  have hC : 0 < Parameters.pathScale n accuracy := lt_of_lt_of_le (by norm_num) (Parameters.pathScale_one_le n accuracy)
  have hb : (0 : ℝ) < Parameters.split n := by exact_mod_cast Parameters.split_pos n
  have he : (0 : ℝ) < Parameters.ell n := by exact_mod_cast Parameters.ell_pos n
  have hT : 0 < T := by dsimp only [T, pieceThreshold]; positivity
  have hearly : 1 - 9 / 256 ≤ mu.prob early :=
    full_resource_fast hn hn₂ accuracy x delta ha hd stored input Q hweight hs hp hsize
  have hlate : 1 - 1 / 32 ≤ mu.prob late :=
    full_late_fast hn accuracy x delta ha hd stored input Q T hT hs hp hsize
  have hi := prob_inter_lower mu early late
  have hm : mu.prob (fun sample => early sample ∧ late sample) ≤
      mu.prob (PathEvent cfg hn hnum accuracy stored input root) :=
    mu.prob_mono (fun sample h => ⟨h.1.1, h.1.2, h.2⟩)
  change 1 - 17 / 256 ≤ mu.prob (PathEvent cfg hn hnum accuracy stored input root)
  linarith

end

end StreamingReachability.Hopset.Following
