module

public import StreamingSSSP.Hopset.ShortTrees
public import StreamingSSSP.Hopset.BridgeStarRoutes

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

theorem ancestor_star_route (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hL : 0 < cfg.advance)
    {fuel q : ℕ} {queue : List (Finset (Fin n))} (frame : Frame n cfg queue.toArray.size)
    (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q)
    (w : ShortNode.BridgeWitness (ShortNode.ofRun (.next frame valid rest) P hshort) cfg.advance)
    (F : Graph (Fin n))
    (hF : ∀ e ∈ frame.result.output.explicit, F e.source e.target ≤ (e.weight : Distance)) :
    ∃ debt : ℕ, (debt : ℝ) ≤ 3 * cfg.etaMax * Reference.distanceScale cfg (q + cfg.advance) ∧
      ∃ T : Late.Route F P.source P.target (cfg.inputScale * (P.path.searchWeight cfg.inputScale + debt)),
        T.hops ≤ 2 := by
  have hlevel : w.node.level = q + cfg.advance := w.descent.level
  have hq : q < cfg.earlyLevel := by have h := w.early; omega
  have hfinite : rank.get w.pivot < cfg.earlyLevel := by rw [w.rank_eq]; exact w.early
  have hrank : rank.get w.pivot = q + cfg.advance := w.rank_eq.trans hlevel
  have hmem : w.pivot ∈ queue.toArray.toVector.get P.node := w.descent.subset w.mem
  let target : Target n queue.toArray.size := ⟨P.node, w.pivot, .advanceStar⟩
  have ht : target ∈ earlyTargets cfg q rank queue.toArray.toVector :=
    advance_target_mem cfg q rank queue.toArray.toVector P.node w.pivot hmem hfinite hrank
  obtain ⟨index, hindex⟩ := target_has_index _ target ht
  have hmono := Geometry.child_distance_mono cfg stored input w.descent.subset
  have hscale : Reference.distanceScale cfg w.node.level ≤ Reference.distanceScale cfg q / 2 := by
    apply Reference.distanceScale_gap cfg
    omega
  have hstars : ∀ e ∈ emittedStars cfg (earlyTargets cfg q rank queue.toArray.toVector)
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg q stored.blocks queue.toArray.toVector (earlyTargets cfg q rank queue.toArray.toVector))
        cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance) := by
    rw [← valid.stars hq]
    exact hF
  have h := raw_advance_bridge cfg q w.node.level stored input hn hs hp hsize
    queue.toArray.toVector (earlyTargets cfg q rank queue.toArray.toVector) index target hindex rfl
    (Backend.roundedRestricted stored input w.node.vertexSet cfg.inputScale)
    (P.localView cfg q hshort) (w.node.piece.localView cfg w.node.level w.node.short)
    w.descent.subpath.vertices_infix P.source P.target P.path.endpoints hmono w.bridge hscale F hstars
  simp only [hlevel] at h
  exact h

theorem global_star_from_witness (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    {parent : ShortNode cfg stored input rank} {depth : ℕ}
    (w : ShortNode.BridgeWitness parent depth) (hrank : w.node.level < cfg.advance)
    (Delta : ℕ) (hradius : cfg.globalRadius = 8 * Delta)
    (hsearch : Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg 0) ≤ Delta)
    {s t : Fin n} (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hsubpath : parent.piece.path.IsSubpath Q) (hshort : (Q.searchWeight cfg.inputScale : ℝ) ≤ 3 * Delta)
    (F : Graph (Fin n))
    (hF : ∀ e ∈ emittedStars cfg (globalTargets cfg rank)
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg 0 stored.blocks (Vector.replicate 1 Finset.univ) (globalTargets cfg rank))
        cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance)) :
    ∃ debt : ℕ, (debt : ℝ) ≤ 3 * cfg.etaMax * Reference.distanceScale cfg w.node.level ∧
      ∃ T : Late.Route F s t (cfg.inputScale * (Q.searchWeight cfg.inputScale + debt)),
        T.hops ≤ 2 := by
  have hfinite : rank.get w.pivot < cfg.earlyLevel := by rw [w.rank_eq]; exact w.early
  have hr : rank.get w.pivot < cfg.advance := by rw [w.rank_eq]; exact hrank
  let target : Target n 1 := ⟨0, w.pivot, .globalStar⟩
  obtain ⟨index, hindex⟩ := target_has_index (globalTargets cfg rank) target
    (global_target_mem cfg rank w.pivot hfinite hr)
  let outer := Q.shortView cfg.inputScale Finset.univ (fun v _ => Finset.mem_univ v) (3 * Delta) hshort
  have hmono := Geometry.child_distance_mono cfg stored input (Finset.subset_univ w.node.vertexSet)
  have hscale := Reference.distanceScale_antitone cfg (Nat.zero_le w.node.level)
  have hinit : (cfg.etaMax : ℝ) * Reference.distanceScale cfg 0 ≤ Delta := by
    simpa only [searchRadius_eta] using hsearch
  have hdet := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg cfg.etaMax : (0 : ℝ) ≤ cfg.etaMax)
  have hnear : (cfg.etaMax : ℝ) * Reference.distanceScale cfg w.node.level ≤ 5 * Delta := by
    have hnDelta : (0 : ℝ) ≤ Delta := Nat.cast_nonneg _
    linarith
  exact raw_global_bridge cfg w.node.level Delta stored input hn hs hp hsize
    (Vector.replicate 1 Finset.univ) (globalTargets cfg rank) index target hindex rfl hradius
    (Backend.roundedRestricted stored input w.node.vertexSet cfg.inputScale)
    outer (w.node.piece.localView cfg w.node.level w.node.short)
    (w.descent.subpath.trans hsubpath).vertices_infix s t Q.endpoints hmono w.bridge hnear F hF

end

end StreamingSSSP.Hopset.Following
