module

public import StreamingReachability.Hopset.LateChainLaw
public import StreamingReachability.Hopset.LateChainSemantics

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem chain_graph_contains (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (q remaining : ℕ)
    (queue : List (Finset (Fin n))) (trace : List (GeometricEntry n cfg)) (i : Fin queue.toArray.size)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (hv : FullValid cfg stored input rank (remaining + 1) q queue trace)
    (F : Graph (Fin n)) (hold : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (hblocks : ∀ B ∈ trace.flatMap (fun entry => entry.frame.result.output.blocks),
      ∀ u v, F u v ≤ Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v) :
    ∀ u v, F u v ≤ (actualLateConfig n hn cfg).graph stored (StoredEdges.graphOfEdges input)
      (queue.toArray.toVector.get i) (Reference.distanceScale cfg q) (chainStages cfg i.val trace) u v := by
  apply Implicit.le_closures
  · intro u v
    exact (hold u v).trans (Implicit.closures_le_base _ _ u v)
  · intro B hB u v
    rcases List.mem_append.mp hB with hB | hB
    · exact (hold u v).trans (Implicit.closures_le_member _ _ hB u v)
    · exact hblocks B (chain_blocks hn q remaining queue trace i he hlevel hv B hB) u v

theorem chain_real_path (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (q remaining : ℕ)
    (queue : List (Finset (Fin n))) (trace : List (GeometricEntry n cfg)) (i : Fin queue.toArray.size)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (hv : FullValid cfg stored input rank (remaining + 1) q queue trace)
    (hg : TraceGood cfg stored input trace) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (F : Graph (Fin n)) (hold : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (hblocks : ∀ B ∈ trace.flatMap (fun entry => entry.frame.result.output.blocks),
      ∀ u v, F u v ≤ Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v) :
    ∃ T : Late.Route F s t Q.micro,
      (T.hops : ℝ) = (actualLateConfig n hn cfg).stoppedHops stored (StoredEdges.graphOfEdges input)
        Q remaining (queue.toArray.toVector.get i) (Reference.distanceScale cfg q) (chainStages cfg i.val trace) := by
  let C := actualLateConfig n hn cfg
  let P := C.path stored (StoredEdges.graphOfEdges input) Q (queue.toArray.toVector.get i)
    (Reference.distanceScale cfg q) (chainStages cfg i.val trace)
  let T := P.mono (chain_graph_contains cfg hn stored input rank q remaining queue trace i he hlevel hv F hold hblocks)
  refine ⟨T, ?_⟩
  have hgood := chain_good hn q remaining queue trace i he hlevel hv hg
  simp only [Late.Config.stoppedHops, hgood, ↓reduceIte]
  rfl

theorem calibrated_late_hops (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (q remaining : ℕ)
    (he : Parameters.threshold n x ≤ q) (hlevel : q + remaining = Parameters.maximumLevel n)
    (queue : List (Finset (Fin n))) (i : Fin queue.toArray.size)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hQ : Q.Inside (queue.toArray.toVector.get i))
    (hshort : (Q.searchWeight delta : ℝ) ≤
      Reference.distanceScale (Parameters.configuration n accuracy x delta blockVolume ha hd) q) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let C := actualLateConfig n hn cfg
    (fullTraceLaw cfg hn stored input rank (remaining + 1) q queue).expect (fun trace =>
      C.stoppedHops stored (StoredEdges.graphOfEdges input) Q remaining (queue.toArray.toVector.get i)
        (Reference.distanceScale cfg q) (chainStages cfg i.val trace)) ≤
      (14 : ℝ) ^ (remaining + 1) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let C := actualLateConfig n hn cfg
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  change (fullTraceLaw cfg hn stored input rank (remaining + 1) q queue).expect (fun trace =>
    C.stoppedHops stored (StoredEdges.graphOfEdges input) Q remaining (queue.toArray.toVector.get i)
      (Reference.distanceScale cfg q) (chainStages cfg i.val trace)) ≤ (14 : ℝ) ^ (remaining + 1)
  rw [late_chain_law cfg hn hnum stored input rank q remaining he hlevel queue i hs hp hsize
    (C.stoppedHops stored (StoredEdges.graphOfEdges input) Q remaining (queue.toArray.toVector.get i)
      (Reference.distanceScale cfg q))]
  apply C.expected_stopped_hops_source (Parameters.ell n)
  · change 2 ≤ Parameters.k n
    have h := Parameters.k_large n
    omega
  · exact Parameters.ell_pos n
  · change 384 * 100 ^ 2 * Parameters.k n ^ 2 * Parameters.ell n ^ 2 ≤ Parameters.groups n
    exact le_rfl
  · exact actual_late_balance n hn accuracy x delta blockVolume ha hd
  · exact hQ
  · exact Reference.distanceScale_pos cfg hnum q
  · exact Reference.calibrated_shift_grid n accuracy x delta blockVolume ha hd q
  · exact hshort

end

end StreamingReachability.Hopset.Batched
