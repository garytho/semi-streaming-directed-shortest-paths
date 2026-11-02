module

public import StreamingSSSP.Hopset.LateWave

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem late_chain_law (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n)
    (q remaining : ℕ) (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (queue : List (Finset (Fin n))) (i : Fin queue.toArray.size)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (f : List ((actualLateConfig n hn cfg).Stage n) → ℝ) :
    (fullTraceLaw cfg hn stored input rank (remaining + 1) q queue).expect (fun trace =>
        f (chainStages cfg i.val trace)) =
      ((actualLateConfig n hn cfg).law stored (StoredEdges.graphOfEdges input) remaining
        (queue.toArray.toVector.get i) (Reference.distanceScale cfg q)).expect f := by
  induction remaining generalizing q queue i f with
  | zero =>
      simp only [fullTraceLaw, Law.expect_bind, Law.expect_map, Law.expect_pure, chainStages,
        List.map_cons, List.map_nil, nodeStage_at, Late.Config.law]
      have h := frame_late_stage cfg hn stored input rank q 0 he hlevel queue.toArray.toVector i
        (fun stage => f [stage])
      simp only [↓reduceIte, Law.expect_map] at h
      exact h
  | succ remaining ih =>
      have hq : q < cfg.maximumLevel := by omega
      let C := actualLateConfig n hn cfg
      let S := queue.toArray.toVector.get i
      let D := Reference.distanceScale cfg q
      let value := fun stage : C.Stage n =>
        (C.law stored (StoredEdges.graphOfEdges input) remaining (C.child stored (StoredEdges.graphOfEdges input) S D stage)
          (D / 4)).expect (fun run => f (stage :: run))
      simp only [fullTraceLaw, Law.expect_bind, Law.expect_map, chainStages, List.map_cons, nodeStage_at]
      calc
        _ = (frameLaw cfg hn stored input rank q queue.toArray.toVector).expect (fun frame =>
            value (lateStage cfg S (frame.choices i))) := by
          apply Reference.expect_congr_on
          refine Early.Sampling.holds_mono
            (frame_valid cfg hn stored input rank q queue.toArray.toVector hs hp hsize hnum) ?_
          intro frame hframe
          have hlen : frame.result.children.toArray.size = queue.toArray.size := by
            rw [hframe.children]
            exact late_children_length cfg q stored input queue.toArray.toVector frame.choices he hq
          let j : Fin frame.result.children.toArray.size := ⟨i.val, by rw [hlen]; exact i.isLt⟩
          have hoption : frame.result.children[i.val]? =
              some (Reference.lateChild (Backend.roundedRestricted stored input S cfg.inputScale) S
                (frame.choices i).pivots
                (Reference.radii cfg q (Backend.roundedRestricted stored input S cfg.inputScale) (frame.choices i).owners)) := by
            rw [hframe.children]
            exact late_children_option cfg q stored input queue.toArray.toVector frame.choices he hq i
          have hchild : frame.result.children.toArray.toVector.get j =
              C.child stored (StoredEdges.graphOfEdges input) S D (lateStage cfg S (frame.choices i)) := by
            have hget := Option.some.inj ((queue_get_option frame.result.children j).symm.trans hoption)
            exact hget.trans (actual_late_child cfg hn stored input q S (frame.choices i) (hframe.subset i)).symm
          have htail := ih (q + 1) (by omega) (by omega) frame.result.children j
            (fun run => f (lateStage cfg S (frame.choices i) :: run))
          rw [hchild, actual_late_scale cfg q he] at htail
          simp only [fullTraceLaw, chainStages, Law.expect_bind, Law.expect_map, List.map_cons] at htail
          exact htail
        _ = (C.fresh S (remaining + 1)).expect value := by
          have h := frame_late_stage cfg hn stored input rank q (remaining + 1) he hlevel
            queue.toArray.toVector i value
          simpa only [Nat.succ_ne_zero, ↓reduceIte] using h
        _ = _ := by
          rw [Late.Config.law, Law.expect_bind]
          simp only [Law.expect_map]
          rfl

end

end StreamingSSSP.Hopset.Batched
