module

public import StreamingReachability.Hopset.ShortTreeStarRoutes
public import StreamingReachability.Hopset.ShortTreeLevels
public import StreamingReachability.Hopset.TrackedSearchRoutes
public import StreamingReachability.Hopset.LateChainPaths

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical BigOperators
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

def originalNodeHops (node : ShortNode cfg stored input rank) : ℕ :=
  node.piece.path.vertices.length - 1

def lateNodeHops (hn : 0 < n) (node : ShortNode cfg stored input rank) : ℕ :=
  ((actualLateConfig n hn cfg).path stored (StoredEdges.graphOfEdges input) node.piece.path node.vertexSet
    (Reference.distanceScale cfg node.level) (chainStages cfg node.piece.node.val node.execution.entries)).hops

def nodeDetour (node : ShortNode cfg stored input rank) : ℝ :=
  if node.level + cfg.advance < cfg.earlyLevel then
    3 * cfg.etaMax * Reference.distanceScale cfg (node.level + cfg.advance)
  else 0

theorem nodeDetour_nonneg (node : ShortNode cfg stored input rank) : 0 ≤ nodeDetour node := by
  have hD : 0 ≤ Reference.distanceScale cfg (node.level + cfg.advance) := by
    unfold Reference.distanceScale
    positivity
  unfold nodeDetour
  split_ifs <;> positivity

theorem tree_search_solution (hn : 0 < n) (hnum : 0 < cfg.initialNumerator)
    (hEarly : cfg.earlyLevel ≤ cfg.maximumLevel) (hL : 0 < cfg.advance)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (F : Graph (Fin n)) (hold : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    {fuel q : ℕ} {queue : List (Finset (Fin n))}
    (run : FullExecution cfg stored input rank fuel q queue)
    (hlevel : q + fuel = cfg.maximumLevel + 1) (hq : q ≤ cfg.earlyLevel)
    (hedges : ∀ entry ∈ run.entries, ∀ e ∈ entry.frame.result.output.explicit,
      F e.source e.target ≤ (e.weight : Distance))
    (hblocks : ∀ B ∈ run.entries.flatMap (fun entry => entry.frame.result.output.blocks),
      ∀ u v, F u v ≤ Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v)
    (P : TrackedPath stored input queue.toArray.toVector) :
    ∃ solution : SearchSolution cfg F P,
      ∀ hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q,
        solution.hops ≤ ((shortTree hnum run P hshort).prune cfg.advance).hopTally originalNodeHops (lateNodeHops hn) ∧
        (solution.debt : ℝ) ≤ ((shortTree hnum run P hshort).prune cfg.advance).markSum nodeDetour := by
  induction run with
  | done =>
      have hbad : cfg.maximumLevel + 1 ≤ cfg.maximumLevel := by omega
      omega
  | @next fuel q queue frame valid rest ih =>
      let run := FullExecution.next frame valid rest
      have hrestLevel : (q + 1) + fuel = cfg.maximumLevel + 1 := by omega
      have hrestEdges : ∀ entry ∈ rest.entries, ∀ e ∈ entry.frame.result.output.explicit,
          F e.source e.target ≤ (e.weight : Distance) :=
        fun entry he => hedges entry (List.mem_cons_of_mem _ he)
      have hrestBlocks : ∀ B ∈ rest.entries.flatMap (fun entry => entry.frame.result.output.blocks),
          ∀ u v, F u v ≤ Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v :=
        fun B hB => hblocks B (List.mem_append_right _ hB)
      by_cases hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q
      · let node := ShortNode.ofRun run P hshort
        by_cases he : q < cfg.earlyLevel
        · by_cases hstop : Early.stopped (P.localView cfg q hshort) (frame.choices P.node).pivots
              (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg q))
          · refine ⟨SearchSolution.original cfg F hold P, ?_⟩
            intro _
            simp only [shortTree, he, hstop, ↓reduceDIte, ↓reduceIte, PieceTree.prune, PieceTree.hopTally,
              PieceTree.markSum, SearchSolution.original, SearchSolution.hops, originalNodeHops, ShortNode.ofRun,
              Late.Route.weaken, Late.Path.originalRoute, Late.Route.hops, Nat.cast_zero, le_refl, and_self]
          · let children := P.nextPieces cfg q hnum he frame.choices hshort
            let childTree := fun i : Fin children.length => shortTree hnum rest (children.get i)
              (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))
            have htree : shortTree hnum run P hshort = .branch node children.length childTree := by
              simp only [run, shortTree, he, hstop, ↓reduceDIte, ↓reduceIte]
              rfl
            by_cases hmark : (shortTree hnum run P hshort).bridgeAt cfg.advance
            · let w := Classical.choice (shortTree_bridge hnum run P hshort cfg.advance hmark)
              obtain ⟨debt, hd, T, hT⟩ := ancestor_star_route hn hs hp hsize hL frame valid rest P hshort w F
                (hedges _ List.mem_cons_self)
              let solution : SearchSolution cfg F P := ⟨debt, T⟩
              have hmark' : (PieceTree.branch node children.length childTree).bridgeAt cfg.advance := by
                simpa only [htree] using hmark
              have hmarked : node.level + cfg.advance < cfg.earlyLevel := by
                have hw := w.early
                have hl := w.descent.level
                change w.node.level = node.level + cfg.advance at hl
                omega
              refine ⟨solution, ?_⟩
              intro _
              change solution.hops ≤ ((shortTree hnum run P hshort).prune cfg.advance).hopTally
                  originalNodeHops (lateNodeHops hn) ∧
                (solution.debt : ℝ) ≤ ((shortTree hnum run P hshort).prune cfg.advance).markSum nodeDetour
              simp only [htree, PieceTree.prune, hmark', ↓reduceIte, PieceTree.hopTally, PieceTree.markSum]
              refine ⟨hT, ?_⟩
              have hmarkedQ : q + cfg.advance < cfg.earlyLevel := hmarked
              change (debt : ℝ) ≤ if q + cfg.advance < cfg.earlyLevel then
                3 * cfg.etaMax * Reference.distanceScale cfg (q + cfg.advance) else 0
              rw [ite_eq_left hmarkedQ]
              exact hd
            · have hrestQ : q + 1 ≤ cfg.earlyLevel := by omega
              let solve := fun Q => Classical.choose (ih hrestLevel hrestQ hrestEdges hrestBlocks Q)
              have hsolve (Q : TrackedPath stored input
                  (geometricChildren cfg q stored input queue.toArray.toVector frame.choices).toArray.toVector)
                  (hQ : (Q.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg (q + 1)) :=
                Classical.choose_spec (ih hrestLevel hrestQ hrestEdges hrestBlocks Q) hQ
              obtain ⟨solution, hdebt, hhops⟩ := P.advance_search_solution cfg q hnum he frame.choices hshort hstop F hold solve
              have hmark' : ¬ (PieceTree.branch node children.length childTree).bridgeAt cfg.advance := by
                simpa only [htree] using hmark
              have hhopSum : (children.map fun Q => (solve Q).hops).sum ≤
                  ∑ i : Fin children.length, ((childTree i).prune cfg.advance).hopTally originalNodeHops (lateNodeHops hn) := by
                rw [list_sum_indices children (fun Q => (solve Q).hops)]
                apply Finset.sum_le_sum
                intro i _
                exact (hsolve (children.get i)
                  (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))).1
              have hdebtSum : (solution.debt : ℝ) ≤
                  ∑ i : Fin children.length, ((childTree i).prune cfg.advance).markSum nodeDetour := by
                have heq : (solution.debt : ℝ) = ∑ i : Fin children.length, ((solve (children.get i)).debt : ℝ) := by
                  rw [hdebt, list_sum_indices children (fun Q => (solve Q).debt), Nat.cast_sum]
                rw [heq]
                exact Finset.sum_le_sum (fun i _ =>
                  (hsolve (children.get i)
                    (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))).2)
              refine ⟨solution, ?_⟩
              intro _
              change solution.hops ≤ ((shortTree hnum run P hshort).prune cfg.advance).hopTally
                  originalNodeHops (lateNodeHops hn) ∧
                (solution.debt : ℝ) ≤ ((shortTree hnum run P hshort).prune cfg.advance).markSum nodeDetour
              simp only [htree, PieceTree.prune, hmark', ↓reduceIte, PieceTree.hopTally, PieceTree.markSum]
              exact ⟨hhops.trans (Nat.add_le_add_left hhopSum _), hdebtSum⟩
        · have hlate : cfg.earlyLevel ≤ q := by omega
          have hlast : q + fuel = cfg.maximumLevel := by omega
          let C := actualLateConfig n hn cfg
          let path := C.path stored (StoredEdges.graphOfEdges input) P.path (queue.toArray.toVector.get P.node)
            (Reference.distanceScale cfg q) (chainStages cfg P.node.val run.entries)
          let T := path.mono (chain_graph_contains cfg hn stored input rank q fuel queue run.entries P.node
            hlate hlast run.fullValid F hold hblocks)
          let solution : SearchSolution cfg F P := ⟨0, T.weaken
            (by simpa only [Nat.add_zero] using P.path.micro_le_search cfg.inputScale cfg.inputScale_pos)⟩
          refine ⟨solution, ?_⟩
          intro _
          simp only [shortTree, he, ↓reduceDIte, PieceTree.prune, PieceTree.hopTally, PieceTree.markSum,
            SearchSolution.hops, solution, T, path, C, run, Late.Route.hops_weaken, Late.Route.hops_mono,
            lateNodeHops, ShortNode.ofRun, ShortNode.vertexSet, Nat.cast_zero, le_refl, and_self]
      · exact ⟨SearchSolution.original cfg F hold P, fun h => False.elim (hshort h)⟩

end

end StreamingReachability.Hopset.Following
