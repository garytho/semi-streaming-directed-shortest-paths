module

public import StreamingSSSP.Hopset.FullAudit
public import StreamingSSSP.Hopset.ReplayProvenance

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

def FastPieces {cfg : Config} (hnum : 0 < cfg.initialNumerator) (n accuracy : ℕ)
    {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)} :
    Option (State cfg stored input cfg.earlyLevel) → Prop :=
  fun state => ∀ r ≤ cfg.earlyLevel, (observedCount hnum r state : ℝ) ≤
    pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r

theorem prob_inter_lower {A : Type*} (mu : Law A) (P Q : A → Prop) :
    mu.prob P + mu.prob Q - 1 ≤ mu.prob (fun a => P a ∧ Q a) := by
  have hu := mu.prob_union (fun a => ¬ P a) (fun a => ¬ Q a)
  have he : mu.prob (fun a => ¬ (P a ∧ Q a)) = mu.prob (fun a => ¬ P a ∨ ¬ Q a) := by
    apply mu.prob_congr
    intro a
    exact not_and_or
  rw [← he, mu.prob_compl P, mu.prob_compl Q, mu.prob_compl (fun a => P a ∧ Q a)] at hu
  linarith

theorem full_resource_fast (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    1 - 9 / 256 ≤ (Batched.fullAuditLaw cfg hn stored input).prob (fun sample =>
      Batched.FullResourceFit cfg stored input sample ∧
        FastPieces hnum n accuracy (replayEarly cfg hnum stored input root sample.1
          (sample.2.map Batched.GeometricEntry.control))) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let mu := Batched.fullAuditLaw cfg hn stored input
  let fastStopped := fun sample : (Fin n → ℕ) × List (Batched.GeometricEntry n cfg) =>
    FastPieces hnum n accuracy (replayEarly cfg hnum stored input root sample.1
      ((Batched.stopTrace cfg stored input sample.2).map Batched.GeometricEntry.control))
  let fastFull := fun sample : (Fin n → ℕ) × List (Batched.GeometricEntry n cfg) =>
    FastPieces hnum n accuracy (replayEarly cfg hnum stored input root sample.1
      (sample.2.map Batched.GeometricEntry.control))
  have hresources : 1 - 1 / 256 ≤ mu.prob (Batched.FullResourceFit cfg stored input) :=
    Batched.full_resources hn hn₂ accuracy x delta ha hd stored input hs hp hsize
  have hfast : 1 - 1 / 32 ≤ mu.prob fastStopped := by
    have he := Batched.fullAudit_stopped_probability cfg hn stored input (fun sample =>
      FastPieces hnum n accuracy (replayEarly cfg hnum stored input root sample.1
        (sample.2.map Batched.GeometricEntry.control)))
    change 1 - 1 / 32 ≤ (Batched.fullAuditLaw cfg hn stored input).prob _
    rw [he]
    exact geometric_fast_pieces hn accuracy x delta ha hd stored input Q hweight hs hp hsize
  have hi := prob_inter_lower mu (Batched.FullResourceFit cfg stored input) fastStopped
  have hm : mu.prob (fun sample => Batched.FullResourceFit cfg stored input sample ∧ fastStopped sample) ≤
      mu.prob (fun sample => Batched.FullResourceFit cfg stored input sample ∧ fastFull sample) := by
    apply mu.prob_mono
    intro sample h
    have he := (Batched.stopTrace_eq_iff cfg stored input sample.2).mpr h.1.1
    exact ⟨h.1, by simpa only [fastFull, fastStopped, he] using h.2⟩
  change 1 - 9 / 256 ≤ mu.prob (fun sample =>
    Batched.FullResourceFit cfg stored input sample ∧ fastFull sample)
  linarith

end

end StreamingSSSP.Hopset.Following
