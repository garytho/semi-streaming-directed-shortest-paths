module

public import StreamingSSSP.Hopset.LateWave

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

namespace FrameValid

variable {ns q : ℕ} {sets : Vector (Finset (Fin n)) ns} {frame : Frame n cfg ns}

theorem late_size (h : FrameValid cfg stored input rank q sets frame)
    (he : cfg.earlyLevel ≤ q) (hq : q < cfg.maximumLevel) : frame.result.children.toArray.size = ns := by
  rw [h.children]
  exact late_children_length cfg q stored input sets frame.choices he hq

def nextNode (h : FrameValid cfg stored input rank q sets frame)
    (he : cfg.earlyLevel ≤ q) (hq : q < cfg.maximumLevel) (i : Fin ns) : Fin frame.result.children.toArray.size :=
  ⟨i.val, by rw [h.late_size he hq]; exact i.isLt⟩

theorem late_child (hn : 0 < n) (h : FrameValid cfg stored input rank q sets frame)
    (he : cfg.earlyLevel ≤ q) (hq : q < cfg.maximumLevel) (i : Fin ns) :
    frame.result.children.toArray.toVector.get (h.nextNode he hq i) =
      (actualLateConfig n hn cfg).child stored (StoredEdges.graphOfEdges input) (sets.get i)
        (Reference.distanceScale cfg q) (lateStage cfg (sets.get i) (frame.choices i)) := by
  have ho : frame.result.children[i.val]? =
      some (Reference.lateChild (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (sets.get i)
        (frame.choices i).pivots
        (Reference.radii cfg q (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (frame.choices i).owners)) := by
    rw [h.children]
    exact late_children_option cfg q stored input sets frame.choices he hq i
  have hget := Option.some.inj ((queue_get_option frame.result.children (h.nextNode he hq i)).symm.trans ho)
  exact hget.trans (actual_late_child cfg hn stored input q (sets.get i) (frame.choices i) (h.subset i)).symm

theorem late_blocks (hn : 0 < n) (h : FrameValid cfg stored input rank q sets frame)
    (he : cfg.earlyLevel ≤ q) (i : Fin ns) :
    ∀ B ∈ (actualLateConfig n hn cfg).stageBlocks stored (StoredEdges.graphOfEdges input) (sets.get i)
        (Reference.distanceScale cfg q) (lateStage cfg (sets.get i) (frame.choices i)),
      B ∈ frame.result.output.blocks := by
  intro B hB
  rw [h.blocks]
  exact List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
    actual_late_blocks cfg hn stored input q he (sets.get i) (frame.choices i) (h.subset i) B hB⟩

end FrameValid

theorem chain_good (hn : 0 < n) (q remaining : ℕ) (queue : List (Finset (Fin n)))
    (trace : List (GeometricEntry n cfg)) (i : Fin queue.toArray.size)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (hv : FullValid cfg stored input rank (remaining + 1) q queue trace)
    (hg : TraceGood cfg stored input trace) :
    (actualLateConfig n hn cfg).Good stored (StoredEdges.graphOfEdges input) remaining
      (queue.toArray.toVector.get i) (Reference.distanceScale cfg q) (chainStages cfg i.val trace) := by
  induction remaining generalizing q queue trace i with
  | zero =>
      cases hv with
      | next hframe rest =>
          cases rest
          rfl
  | succ remaining ih =>
      cases hv with
      | @next fuel q queue frame tail hframe rest =>
          have hq : q < cfg.maximumLevel := by omega
          let j := hframe.nextNode he hq i
          have hgood : Reference.BallsGood cfg stored input q (queue.toArray.toVector.get i) :=
            hg _ (List.mem_cons_self) _ (queue_get_mem queue i)
          have hcurrent : (actualLateConfig n hn cfg).BallsGood stored (StoredEdges.graphOfEdges input)
              (remaining + 1) (queue.toArray.toVector.get i) (Reference.distanceScale cfg q) := by
            have hr : remaining + 1 = cfg.maximumLevel - q := by omega
            rw [hr]
            exact (actual_late_balls hn cfg stored input q (by omega) _).mpr hgood
          have htail := ih (q + 1) frame.result.children tail j (by omega) (by omega) rest
            (fun entry he => hg entry (List.mem_cons_of_mem _ he))
          rw [hframe.late_child hn he hq i, actual_late_scale cfg q he] at htail
          change (actualLateConfig n hn cfg).BallsGood stored (StoredEdges.graphOfEdges input)
              (remaining + 1) (queue.toArray.toVector.get i) (Reference.distanceScale cfg q) ∧ _
          simp only [nodeStage_at]
          exact ⟨hcurrent, htail⟩

theorem chain_blocks (hn : 0 < n) (q remaining : ℕ) (queue : List (Finset (Fin n)))
    (trace : List (GeometricEntry n cfg)) (i : Fin queue.toArray.size)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (hv : FullValid cfg stored input rank (remaining + 1) q queue trace) :
    ∀ B ∈ (actualLateConfig n hn cfg).blocks stored (StoredEdges.graphOfEdges input)
        (queue.toArray.toVector.get i) (Reference.distanceScale cfg q) (chainStages cfg i.val trace),
      B ∈ trace.flatMap (fun entry => entry.frame.result.output.blocks) := by
  induction remaining generalizing q queue trace i with
  | zero =>
      cases hv with
      | next hframe rest =>
          cases rest
          intro B hB
          simp only [chainStages, List.map_cons, List.map_nil, nodeStage_at, Late.Config.blocks,
            List.append_nil] at hB
          have hcurrent := hframe.late_blocks hn he i B
          simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using hcurrent hB
  | succ remaining ih =>
      cases hv with
      | @next fuel q queue frame tail hframe rest =>
          have hq : q < cfg.maximumLevel := by omega
          let j := hframe.nextNode he hq i
          intro B hB
          simp only [chainStages, List.map_cons, nodeStage_at, Late.Config.blocks] at hB
          change B ∈
            (actualLateConfig n hn cfg).stageBlocks stored (StoredEdges.graphOfEdges input)
                (queue.toArray.toVector.get i) (Reference.distanceScale cfg q)
                (lateStage cfg (queue.toArray.toVector.get i) (frame.choices i)) ++
              (actualLateConfig n hn cfg).blocks stored (StoredEdges.graphOfEdges input)
                ((actualLateConfig n hn cfg).child stored (StoredEdges.graphOfEdges input)
                  (queue.toArray.toVector.get i) (Reference.distanceScale cfg q)
                  (lateStage cfg (queue.toArray.toVector.get i) (frame.choices i)))
                (Reference.distanceScale cfg q / 4) (chainStages cfg i.val tail) at hB
          rcases List.mem_append.mp hB with hB | hB
          · exact List.mem_append_left _ (hframe.late_blocks hn he i B hB)
          · have hc := ih (q + 1) frame.result.children tail j (by omega) (by omega) rest B
            rw [hframe.late_child hn he hq i, actual_late_scale cfg q he] at hc
            exact List.mem_append_right _ (hc hB)

end

end StreamingSSSP.Hopset.Batched
