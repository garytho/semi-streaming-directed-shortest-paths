module

public import StreamingReachability.Hopset.LateChainPaths
public import StreamingReachability.Hopset.TrackedPaths

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

def lateFrontierWork (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (q remaining : ℕ) (queue : List (Finset (Fin n)))
    (paths : List (TrackedPath stored input queue.toArray.toVector)) (trace : List (GeometricEntry n cfg)) : ℝ :=
  (paths.map fun P => (actualLateConfig n hn cfg).stoppedHops stored (StoredEdges.graphOfEdges input)
    P.path remaining (queue.toArray.toVector.get P.node) (Reference.distanceScale cfg q)
    (chainStages cfg P.node.val trace)).sum

theorem lateFrontierWork_nonneg (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (q remaining : ℕ) (queue : List (Finset (Fin n)))
    (paths : List (TrackedPath stored input queue.toArray.toVector)) (trace : List (GeometricEntry n cfg)) :
    0 ≤ lateFrontierWork cfg hn stored input q remaining queue paths trace := by
  induction paths with
  | nil => exact le_rfl
  | cons P paths ih =>
      exact add_nonneg ((actualLateConfig n hn cfg).stoppedHops_nonneg _ _ _ _ _ _ _) ih

theorem lateFrontierWork_mean (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (q remaining : ℕ)
    (he : Parameters.threshold n x ≤ q) (hlevel : q + remaining = Parameters.maximumLevel n)
    (queue : List (Finset (Fin n)))
    (paths : List (TrackedPath stored input queue.toArray.toVector))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hshort : ∀ P ∈ paths, (P.path.searchWeight delta : ℝ) ≤
      Reference.distanceScale (Parameters.configuration n accuracy x delta blockVolume ha hd) q) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    (fullTraceLaw cfg hn stored input rank (remaining + 1) q queue).expect
        (lateFrontierWork cfg hn stored input q remaining queue paths) ≤
      (14 : ℝ) ^ (remaining + 1) * paths.length := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  change (fullTraceLaw cfg hn stored input rank (remaining + 1) q queue).expect
      (lateFrontierWork cfg hn stored input q remaining queue paths) ≤ _
  unfold lateFrontierWork
  rw [Late.expect_list_sum]
  induction paths with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero, mul_zero, le_refl]
  | cons P paths ih =>
      have hP := calibrated_late_hops hn accuracy x delta blockVolume ha hd stored input rank
        q remaining he hlevel queue P.node hs hp hsize P.path P.inside (hshort P List.mem_cons_self)
      have htail := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem lateFrontierWork_actual (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (q remaining : ℕ)
    (queue : List (Finset (Fin n))) (trace : List (GeometricEntry n cfg))
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (hv : FullValid cfg stored input rank (remaining + 1) q queue trace)
    (hg : TraceGood cfg stored input trace) (paths : List (TrackedPath stored input queue.toArray.toVector)) :
    lateFrontierWork cfg hn stored input q remaining queue paths trace =
      ((paths.map fun P => ((actualLateConfig n hn cfg).path stored (StoredEdges.graphOfEdges input)
        P.path (queue.toArray.toVector.get P.node) (Reference.distanceScale cfg q)
        (chainStages cfg P.node.val trace)).hops).sum : ℕ) := by
  induction paths with
  | nil => simp only [lateFrontierWork, List.map_nil, List.sum_nil, Nat.cast_zero]
  | cons P paths ih =>
      have hgood := chain_good hn q remaining queue trace P.node he hlevel hv hg
      simp only [lateFrontierWork, List.map_cons, List.sum_cons, Late.Config.stoppedHops,
        hgood, ↓reduceIte, Nat.cast_add]
      exact congrArg (fun w : ℝ => (((actualLateConfig n hn cfg).path stored (StoredEdges.graphOfEdges input)
        P.path (queue.toArray.toVector.get P.node) (Reference.distanceScale cfg q)
        (chainStages cfg P.node.val trace)).hops : ℝ) + w) ih

end

end StreamingReachability.Hopset.Following
