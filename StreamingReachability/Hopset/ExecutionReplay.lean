module

public import StreamingReachability.Hopset.FullExecution
public import StreamingReachability.Hopset.FullTraceSplit
public import StreamingReachability.Hopset.PathReplayLaw

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

theorem follow_valid_head (hnum : 0 < cfg.initialNumerator) {q : ℕ}
    (st : State cfg stored input q) (frame : Frame n cfg st.queue.toArray.size)
    (valid : FrameValid cfg stored input rank q st.queue.toArray.toVector frame)
    (he : q < cfg.earlyLevel) (tail : List (ControlEntry n cfg)) :
    followControls cfg hnum stored input (fun v => rank.get v)
      (⟨q, st.queue, frame.choices⟩ :: tail) (some ⟨q, st⟩) =
      followControls cfg hnum stored input (fun v => rank.get v) tail
        (some ⟨q + 1, st.update hnum he (fun v => decide (rank.get v = q), fun i => (frame.choices i).owners)⟩) := by
  have hc := valid.currentChoices he
  calc
    _ = followControls cfg hnum stored input (fun v => rank.get v)
        (⟨q, st.queue, currentChoices cfg st.queue.toArray.toVector (fun v => decide (rank.get v = q))
          (fun i => (frame.choices i).owners)⟩ :: tail) (some ⟨q, st⟩) :=
      congrArg (fun choices => followControls cfg hnum stored input (fun v => rank.get v)
        (⟨q, st.queue, choices⟩ :: tail) (some ⟨q, st⟩)) hc.symm
    _ = _ := followControls_head cfg hnum stored input (fun v => rank.get v) q st he _ tail

theorem execution_replay (hnum : 0 < cfg.initialNumerator) {fuel q : ℕ}
    {queue : List (Finset (Fin n))} (run : FullExecution cfg stored input rank fuel q queue)
    (hq : q ≤ cfg.earlyLevel) (hlen : cfg.earlyLevel ≤ q + fuel)
    (st : State cfg stored input q) (hqueue : st.queue = queue) :
    ∃ final : State cfg stored input cfg.earlyLevel,
      followControls cfg hnum stored input (fun v => rank.get v) (run.entries.map GeometricEntry.control)
        (some ⟨q, st⟩) = some ⟨cfg.earlyLevel, final⟩ ∧
      followControls cfg hnum stored input (fun v => rank.get v)
        ((run.entries.take (cfg.earlyLevel - q)).map GeometricEntry.control) (some ⟨q, st⟩) =
          some ⟨cfg.earlyLevel, final⟩ ∧
      final.queue = afterQueue queue (run.entries.take (cfg.earlyLevel - q)) := by
  induction run with
  | done q queue =>
      have he : q = cfg.earlyLevel := by omega
      subst q
      refine ⟨st, ?_, ?_, ?_⟩
      · exact followControls_done cfg hnum stored input _ [] _ st le_rfl
      · simpa only [FullExecution.entries, List.take_nil, List.map_nil] using
          followControls_done cfg hnum stored input (fun v => rank.get v) [] _ st le_rfl
      · simpa only [FullExecution.entries, List.take_nil, afterQueue] using hqueue
  | @next fuel q queue frame valid rest ih =>
      by_cases he : q < cfg.earlyLevel
      · subst queue
        let next := st.update hnum he
          (fun v => decide (rank.get v = q), fun i => (frame.choices i).owners)
        have hnext : next.queue = geometricChildren cfg q stored input st.queue.toArray.toVector frame.choices := by
          exact congrArg (geometricChildren cfg q stored input st.queue.toArray.toVector) (valid.currentChoices he)
        obtain ⟨final, hf, hp, hqf⟩ := ih (by omega) (by omega) next hnext
        have hsub : cfg.earlyLevel - q = (cfg.earlyLevel - (q + 1)) + 1 := by omega
        refine ⟨final, ?_, ?_, ?_⟩
        · exact (follow_valid_head hnum st frame valid he _).trans hf
        · change followControls cfg hnum stored input (fun v => rank.get v)
            (((⟨q, st.queue, frame⟩ : GeometricEntry n cfg) :: rest.entries).take (cfg.earlyLevel - q)
              |>.map GeometricEntry.control) (some ⟨q, st⟩) = _
          rw [hsub, List.take_succ_cons, List.map_cons]
          exact (follow_valid_head hnum st frame valid he _).trans hp
        · change final.queue = afterQueue st.queue
            (((⟨q, st.queue, frame⟩ : GeometricEntry n cfg) :: rest.entries).take (cfg.earlyLevel - q))
          rw [hsub, List.take_succ_cons, afterQueue]
          exact hqf.trans (congrArg
            (fun sets => afterQueue sets (rest.entries.take (cfg.earlyLevel - (q + 1)))) valid.children.symm)
      · have heq : q = cfg.earlyLevel := by omega
        subst q
        refine ⟨st, ?_, ?_, ?_⟩
        · exact followControls_done cfg hnum stored input _ _ _ st le_rfl
        · simpa only [Nat.sub_self, List.take_zero, List.map_nil] using
            followControls_done cfg hnum stored input (fun v => rank.get v) [] _ st le_rfl
        · simpa only [Nat.sub_self, List.take_zero, afterQueue] using hqueue

theorem execution_replay_root (hnum : 0 < cfg.initialNumerator) {fuel : ℕ}
    (root : State cfg stored input 0) (run : FullExecution cfg stored input rank fuel 0 root.queue)
    (hlen : cfg.earlyLevel ≤ fuel) :
    ∃ final : State cfg stored input cfg.earlyLevel,
      replayEarly cfg hnum stored input root (fun v => rank.get v) (run.entries.map GeometricEntry.control) = some final ∧
      replayEarly cfg hnum stored input root (fun v => rank.get v)
        ((run.entries.take cfg.earlyLevel).map GeometricEntry.control) = some final ∧
      final.queue = afterQueue root.queue (run.entries.take cfg.earlyLevel) := by
  obtain ⟨final, hf, hp, hq⟩ := execution_replay hnum run (Nat.zero_le _) (by omega) root rfl
  refine ⟨final, ?_, ?_, ?_⟩
  · simp only [replayEarly, hf, unpackState, ↓reduceDIte]
  · simpa only [Nat.sub_zero, replayEarly, hp, unpackState, ↓reduceDIte] using congrArg (unpackState cfg.earlyLevel) hp
  · simpa only [Nat.sub_zero] using hq

end

end StreamingReachability.Hopset.Following
