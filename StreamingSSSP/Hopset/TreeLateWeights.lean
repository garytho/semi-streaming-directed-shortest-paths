module

public import StreamingSSSP.Hopset.TreeRouteRealization
public import StreamingSSSP.Hopset.ShortTreeCounts
public import StreamingSSSP.Hopset.LateFrontier
public import StreamingSSSP.Hopset.ExecutionReplay

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}
    {fuel q : ℕ} {queue : List (Finset (Fin n))}

def shortLateWeight (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (run : FullExecution cfg stored input rank fuel q queue)
    (P : TrackedPath stored input queue.toArray.toVector) : ℕ :=
  if hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q then
    (shortTree hnum run P hshort).lateWeight (lateNodeHops hn)
  else 0

theorem shortLateWeight_eq (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (run : FullExecution cfg stored input rank fuel q queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    shortLateWeight hnum hn run P = (shortTree hnum run P hshort).lateWeight (lateNodeHops hn) := by
  simp only [shortLateWeight, hshort, ↓reduceDIte]

def familyLateWeight (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector)) : ℕ :=
  ((splitAll cfg q hnum paths).map (shortLateWeight hnum hn run)).sum

theorem shortLateWeight_step (hnum : 0 < cfg.initialNumerator) (hn : 0 < n) (he : q < cfg.earlyLevel)
    (frame : Frame n cfg queue.toArray.size) (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    shortLateWeight hnum hn (.next frame valid rest) P =
      ((P.nextPieces cfg q hnum he frame.choices hshort).map (shortLateWeight hnum hn rest)).sum := by
  rw [shortLateWeight_eq hnum hn _ P hshort]
  by_cases hs : Early.stopped (P.localView cfg q hshort) (frame.choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg q))
  · simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.lateWeight, TrackedPath.nextPieces,
      TrackedPath.advance, splitAll, List.flatMap_nil, List.map_nil, List.sum_nil]
  · let children := P.nextPieces cfg q hnum he frame.choices hshort
    let childTree := fun i : Fin children.length => shortTree hnum rest (children.get i)
      (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))
    have ht : shortTree hnum (.next frame valid rest) P hshort =
        .branch (ShortNode.ofRun (.next frame valid rest) P hshort) children.length childTree := by
      simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte]
      rfl
    rw [ht, PieceTree.lateWeight, list_sum_indices children (shortLateWeight hnum hn rest)]
    apply Finset.sum_congr rfl
    intro i _
    exact (shortLateWeight_eq hnum hn rest (children.get i)
      (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))).symm

theorem shortLateWeights_step (hnum : 0 < cfg.initialNumerator) (hn : 0 < n) (he : q < cfg.earlyLevel)
    (frame : Frame n cfg queue.toArray.size) (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (paths : List (TrackedPath stored input queue.toArray.toVector))
    (hshort : ∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    (paths.map (shortLateWeight hnum hn (.next frame valid rest))).sum =
      ((splitAll cfg (q + 1) hnum (advanceAll cfg q hnum he frame.choices paths hshort)).map
        (shortLateWeight hnum hn rest)).sum := by
  induction paths with
  | nil => rfl
  | cons P paths ih =>
      have hP := shortLateWeight_step hnum hn he frame valid rest P (hshort P List.mem_cons_self)
      have ht := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      simp only [List.map_cons, List.sum_cons, advanceAll, splitAll, List.flatMap_append,
        List.map_append, List.sum_append]
      exact congrArg₂ Nat.add hP ht

theorem familyLateWeight_step (hnum : 0 < cfg.initialNumerator) (hn : 0 < n) (he : q < cfg.earlyLevel)
    (frame : Frame n cfg queue.toArray.size) (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (paths : List (TrackedPath stored input queue.toArray.toVector)) :
    familyLateWeight hnum hn (.next frame valid rest) paths =
      familyLateWeight hnum hn rest
        (advanceAll cfg q hnum he frame.choices (splitAll cfg q hnum paths)
          (splitAll_short cfg q hnum paths)) :=
  shortLateWeights_step hnum hn he frame valid rest _ (splitAll_short cfg q hnum paths)

theorem shortLateWeight_current (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (run : FullExecution cfg stored input rank fuel q queue) (he : cfg.earlyLevel ≤ q)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    shortLateWeight hnum hn run P = lateNodeHops hn (ShortNode.ofRun run P hshort) := by
  rw [shortLateWeight_eq hnum hn run P hshort]
  cases run with
  | done => rfl
  | next frame valid rest =>
      simp only [shortTree, show ¬ q < cfg.earlyLevel by omega, ↓reduceDIte, PieceTree.lateWeight]

theorem familyLateWeight_actual (hnum : 0 < cfg.initialNumerator) (hn : 0 < n) {remaining : ℕ}
    (run : FullExecution cfg stored input rank (remaining + 1) q queue)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (hg : TraceGood cfg stored input run.entries)
    (paths : List (TrackedPath stored input queue.toArray.toVector)) :
    (familyLateWeight hnum hn run paths : ℝ) =
      lateFrontierWork cfg hn stored input q remaining queue (splitAll cfg q hnum paths) run.entries := by
  rw [lateFrontierWork_actual cfg hn stored input rank q remaining queue run.entries he hlevel run.fullValid hg]
  apply congrArg (fun k : ℕ => (k : ℝ))
  unfold familyLateWeight
  apply congrArg List.sum
  apply List.map_congr_left
  intro P hP
  exact shortLateWeight_current hnum hn run he P (splitAll_short cfg q hnum paths P hP)

theorem familyLateWeight_replay (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (hEarly : cfg.earlyLevel ≤ cfg.maximumLevel)
    (run : FullExecution cfg stored input rank fuel q queue)
    (hlevel : q + fuel = cfg.maximumLevel + 1) (hq : q ≤ cfg.earlyLevel)
    (hg : TraceGood cfg stored input run.entries)
    (known : Fin n → Option (Fin q))
    (paths : List (TrackedPath stored input queue.toArray.toVector)) (layers : List (Layer cfg stored input))
    (final : State cfg stored input cfg.earlyLevel)
    (hf : followControls cfg hnum stored input (fun v => rank.get v) (run.entries.map GeometricEntry.control)
      (some ⟨q, ⟨known, queue, paths, layers⟩⟩) = some ⟨cfg.earlyLevel, final⟩) :
    (familyLateWeight hnum hn run paths : ℝ) =
      lateFrontierWork cfg hn stored input cfg.earlyLevel (cfg.maximumLevel - cfg.earlyLevel) final.queue
        (splitAll cfg cfg.earlyLevel hnum final.paths) (run.entries.drop (cfg.earlyLevel - q)) := by
  induction run generalizing layers with
  | done =>
      have hbad : cfg.maximumLevel + 1 ≤ cfg.maximumLevel := by omega
      omega
  | @next fuel q queue frame valid rest ih =>
      let st : State cfg stored input q := ⟨known, queue, paths, layers⟩
      by_cases he : q < cfg.earlyLevel
      · let coins := fun v => decide (rank.get v = q)
        let makeState := fun choices : Fin queue.toArray.size → Reference.Choice n cfg =>
          { known := fun v => RankPrefix.nextKnown q (known v) (coins v)
            queue := geometricChildren cfg q stored input queue.toArray.toVector choices
            paths := advanceAll cfg q hnum he choices (splitAll cfg q hnum paths) (splitAll_short cfg q hnum paths)
            layers := layers ++ [⟨q, queue, paths, choices⟩] : State cfg stored input (q + 1) }
        let next := makeState frame.choices
        have hupdate : st.update hnum he (coins, fun i => (frame.choices i).owners) = next :=
          congrArg makeState (valid.currentChoices he)
        have hfollow : followControls cfg hnum stored input (fun v => rank.get v)
            (rest.entries.map GeometricEntry.control) (some ⟨q + 1, next⟩) = some ⟨cfg.earlyLevel, final⟩ := by
          rw [← hupdate]
          exact (follow_valid_head hnum st frame valid he _).symm.trans hf
        have hc : familyLateWeight hnum hn (.next frame valid rest) paths =
            familyLateWeight hnum hn rest next.paths :=
          familyLateWeight_step hnum hn he frame valid rest paths
        have ht := ih (by omega) (by omega) (FullExecution.tail_good hg)
          next.known next.paths next.layers hfollow
        have hsub : cfg.earlyLevel - q = (cfg.earlyLevel - (q + 1)) + 1 := by omega
        have hdrop : (FullExecution.next frame valid rest).entries.drop (cfg.earlyLevel - q) =
            rest.entries.drop (cfg.earlyLevel - (q + 1)) := by
          rw [hsub]
          rfl
        rw [hdrop]
        exact (congrArg (fun k : ℕ => (k : ℝ)) hc).trans ht
      · have heq : q = cfg.earlyLevel := by omega
        subst q
        have hs : st = final := by
          have h := congrArg (unpackState cfg.earlyLevel) hf
          rw [followControls_done cfg hnum stored input (fun v => rank.get v)
            ((FullExecution.next frame valid rest).entries.map GeometricEntry.control) cfg.earlyLevel st le_rfl] at h
          simpa only [unpackState, ↓reduceDIte, Option.some.injEq] using h
        subst final
        have hm := familyLateWeight_actual hnum hn (.next frame valid rest) le_rfl (by omega) hg paths
        have hrem : fuel = cfg.maximumLevel - cfg.earlyLevel := by omega
        simp only [Nat.sub_self, List.drop_zero]
        exact hm.trans (congrArg (fun remaining => lateFrontierWork cfg hn stored input cfg.earlyLevel remaining queue
          (splitAll cfg cfg.earlyLevel hnum paths) (FullExecution.next frame valid rest).entries) hrem)

end

end StreamingSSSP.Hopset.Following
