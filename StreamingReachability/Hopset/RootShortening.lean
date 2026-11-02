module

public import StreamingReachability.Hopset.CalibratedForest

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

theorem calibrated_root_route (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (hx : 0 < x)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    ∀ (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
      (run : FullExecution cfg stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue),
      run.entries = trace → PathEvent cfg hn hnum accuracy stored input root (ranks, trace) →
      ∀ (F : Graph (Fin n)),
      (∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v) →
      (∀ entry ∈ trace, ∀ e ∈ entry.frame.result.output.explicit, F e.source e.target ≤ (e.weight : Distance)) →
      (∀ B ∈ trace.flatMap (fun entry => entry.frame.result.output.blocks),
        ∀ u v, F u v ≤ Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v) →
      (∀ e ∈ emittedStars cfg (globalTargets cfg (Vector.ofFn ranks))
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg 0 stored.blocks (Vector.replicate 1 Finset.univ) (globalTargets cfg (Vector.ofFn ranks)))
          cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance)) →
      ∃ debt : ℕ, (debt : ℝ) ≤
          (Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy ∧
        ∃ T : Late.Route F s t (delta * (Q.searchWeight delta + debt)),
          T.hops ≤ Parameters.hopBound n accuracy x := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  dsimp only
  intro ranks trace run hentries hevent F hold hedges hblocks hglobals
  let P : TrackedPath stored input root.queue.toArray.toVector :=
    root.paths.get ⟨0, by simp [root, rootState]⟩
  have hpaths : root.paths = [P] := rfl
  let pieces := splitAll cfg 0 hnum root.paths
  have hpieces : pieces = P.split cfg 0 hnum := by
    simp only [pieces, hpaths, splitAll, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hEarly : cfg.earlyLevel ≤ cfg.maximumLevel := Nat.min_le_left _ _
  have hL : 0 < cfg.advance := by
    change 0 < Parameters.advance n accuracy
    have h := Parameters.advance_large n accuracy
    omega
  have hedgesRun : ∀ entry ∈ run.entries, ∀ e ∈ entry.frame.result.output.explicit,
      F e.source e.target ≤ (e.weight : Distance) := by rw [hentries]; exact hedges
  have hblocksRun : ∀ B ∈ run.entries.flatMap (fun entry => entry.frame.result.output.blocks),
      ∀ u v, F u v ≤ Implicit.closure (stored.base (StoredEdges.graphOfEdges input)) B u v := by
    rw [hentries]
    exact hblocks
  let shallow : Prop := ∃ C : TrackedPath stored input root.queue.toArray.toVector, C ∈ pieces ∧
    ∃ (hshort : (C.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg 0) (d : ℕ),
      d < cfg.advance ∧ (shortTree hnum run C hshort).bridgeAt d
  by_cases hshallow : shallow
  · obtain ⟨C, hC, hshort, d, hdepth, hb⟩ := hshallow
    let w := Classical.choice (shortTree_bridge hnum run C hshort d hb)
    have hrank : w.node.level < cfg.advance := by
      have h := w.descent.level
      change w.node.level = 0 + d at h
      omega
    have hsubpath : C.path.IsSubpath Q := by
      have hm : C ∈ P.split cfg 0 hnum := by rw [← hpieces]; exact hC
      exact P.split_subpath cfg 0 hnum C hm
    have hshortRoot : (Q.searchWeight cfg.inputScale : ℝ) ≤ 3 * Parameters.queryUnit n accuracy x := by
      change (Q.searchWeight delta : ℝ) ≤ 3 * (Parameters.queryUnit n accuracy x : ℝ)
      exact_mod_cast hweight
    obtain ⟨debt, hdebt, T, hhops⟩ := global_star_from_witness hn hs hp hsize w hrank
      (Parameters.queryUnit n accuracy x) rfl
      (calibrated_initial_search n accuracy x delta blockVolume ha hd) Q hsubpath hshortRoot F hglobals
    have hdetour := Parameters.global_detour_budget n accuracy x delta blockVolume ha hd w.node.level
    have htwo : 2 ≤ Parameters.hopBound n accuracy x := by
      calc
        2 ≤ (2 : ℕ) ^ 30 := by norm_num
        _ ≤ 2 ^ 30 * (100 ^ (Parameters.advance n accuracy + Parameters.maximumLevel n + 2) *
            Parameters.split n ^ (Parameters.advance n accuracy + 3) * (Nat.sqrt (Parameters.ceilDiv n x) + 1)) :=
          Nat.le_mul_of_pos_right _ (by have h := Parameters.split_pos n; positivity)
        _ = _ := by unfold Parameters.hopBound; ring
    exact ⟨debt, hdebt.trans hdetour, T, hhops.trans htwo⟩
  · let solve := fun C => Classical.choose
      (tree_search_solution hn hnum hEarly hL hs hp hsize F hold run (Nat.zero_add _) (Nat.zero_le _)
        hedgesRun hblocksRun C)
    have hsolve (C : TrackedPath stored input root.queue.toArray.toVector)
        (hshort : (C.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg 0) :=
      Classical.choose_spec
        (tree_search_solution hn hnum hEarly hL hs hp hsize F hold run (Nat.zero_add _) (Nat.zero_le _)
          hedgesRun hblocksRun C) hshort
    let solution := SearchSolution.splitWith cfg F 0 hnum hold solve P
    have hglobal : ∀ C ∈ splitAll cfg 0 hnum root.paths,
        ∀ (hshort : (C.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg 0) (d : ℕ),
          d < cfg.advance → ¬ (shortTree hnum run C hshort).bridgeAt d := by
      intro C hC hshort d hd hb
      exact hshallow ⟨C, hC, hshort, d, hd, hb⟩
    have hbulk := family_solution_hops hnum hn hL run root.paths hglobal F solve (fun C h => (hsolve C h).1)
    change (pieces.map fun C => (solve C).hops).sum + 2 * pieces.length ≤
      4 * familySize hnum run root.paths + familyLateWeight hnum hn run root.paths at hbulk
    have hroot : solution.hops ≤ pieces.length + (pieces.map fun C => (solve C).hops).sum := by
      simpa only [hpieces] using SearchSolution.splitWith_hops cfg F 0 hnum hold solve P
    have hhop : solution.hops ≤ 4 * familySize hnum run root.paths + familyLateWeight hnum hn run root.paths := by omega
    have hforest := calibrated_forest_bounds hn accuracy x delta blockVolume ha hd stored input root ranks trace
      run hentries hevent
    have hdebt : (solution.debt : ℝ) ≤
        (Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy := by
      have h := hforest.2.2 F solve (fun C h => (hsolve C h).2)
      have heq := SearchSolution.splitWith_debt cfg F 0 hnum hold solve P
      rw [← hpieces] at heq
      exact (congrArg (fun k : ℕ => (k : ℝ)) heq).le.trans h
    let T0 := pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) cfg.earlyLevel
    have hsizeBound : (familySize hnum run root.paths : ℝ) ≤ ((Parameters.ell n : ℝ) + 1) * T0 := hforest.1
    have hlateBound : (familyLateWeight hnum hn run root.paths : ℝ) ≤
        32 * ((14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T0) := hforest.2.1
    have hreal : (solution.hops : ℝ) ≤
        4 * (familySize hnum run root.paths : ℝ) + (familyLateWeight hnum hn run root.paths : ℝ) := by exact_mod_cast hhop
    have htotal : (solution.hops : ℝ) ≤
        (4 * ((Parameters.ell n : ℝ) + 1) + 32 * (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1)) * T0 := by
      nlinarith
    have hbudget := Parameters.combined_hop_budget n accuracy x hx
    have hfinal : (solution.hops : ℝ) ≤ Parameters.hopBound n accuracy x := htotal.trans hbudget
    have hnat : solution.hops ≤ Parameters.hopBound n accuracy x := by exact_mod_cast hfinal
    exact ⟨solution.debt, hdebt, solution.route, hnat⟩

end

end StreamingReachability.Hopset.Following
