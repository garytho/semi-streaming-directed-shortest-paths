module

public import StreamingReachability.Hopset.ShortTrees
public import StreamingReachability.Hopset.EarlyPathFamilies
public import StreamingReachability.Hopset.EarlyPlanRoutes

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}
    {fuel q : ℕ} {queue : List (Finset (Fin n))}

def shortCount (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue) (d : ℕ)
    (P : TrackedPath stored input queue.toArray.toVector) : ℕ :=
  if hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q then
    (shortTree hnum run P hshort).countAt d
  else 0

theorem shortCount_eq (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue) (d : ℕ)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    shortCount hnum run d P = (shortTree hnum run P hshort).countAt d := by
  simp only [shortCount, hshort, ↓reduceDIte]

def familyCount (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector)) (d : ℕ) : ℕ :=
  ((splitAll cfg q hnum paths).map (shortCount hnum run d)).sum

theorem shortCounts_zero (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector))
    (hshort : ∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    (paths.map (shortCount hnum run 0)).sum = paths.length := by
  induction paths with
  | nil => rfl
  | cons P paths ih =>
      have hP := shortCount_eq hnum run 0 P (hshort P List.mem_cons_self)
      simp only [PieceTree.countAt] at hP
      simp only [List.map_cons, List.sum_cons, List.length_cons, hP]
      have ht := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      omega

theorem familyCount_zero (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector)) :
    familyCount hnum run paths 0 = (splitAll cfg q hnum paths).length :=
  shortCounts_zero hnum run _ (splitAll_short cfg q hnum paths)

theorem shortCount_step (hnum : 0 < cfg.initialNumerator) (he : q < cfg.earlyLevel)
    (frame : Frame n cfg queue.toArray.size) (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) (d : ℕ) :
    shortCount hnum (.next frame valid rest) (d + 1) P =
      ((P.nextPieces cfg q hnum he frame.choices hshort).map (shortCount hnum rest d)).sum := by
  rw [shortCount_eq hnum _ (d + 1) P hshort]
  by_cases hs : Early.stopped (P.localView cfg q hshort) (frame.choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg q))
  · simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.countAt, TrackedPath.nextPieces,
      TrackedPath.advance, splitAll, List.flatMap_nil, List.map_nil, List.sum_nil]
  · let children := P.nextPieces cfg q hnum he frame.choices hshort
    let childTree := fun i : Fin children.length => shortTree hnum rest (children.get i)
      (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))
    have ht : shortTree hnum (.next frame valid rest) P hshort =
        .branch (ShortNode.ofRun (.next frame valid rest) P hshort) children.length childTree := by
      simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte]
      rfl
    rw [ht, PieceTree.countAt, list_sum_indices children (shortCount hnum rest d)]
    apply Finset.sum_congr rfl
    intro i _
    exact (shortCount_eq hnum rest d (children.get i)
      (P.nextPieces_short cfg q hnum he frame.choices hshort _ (List.get_mem children i))).symm

theorem shortCounts_step (hnum : 0 < cfg.initialNumerator) (he : q < cfg.earlyLevel)
    (frame : Frame n cfg queue.toArray.size) (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (paths : List (TrackedPath stored input queue.toArray.toVector))
    (hshort : ∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) (d : ℕ) :
    (paths.map (shortCount hnum (.next frame valid rest) (d + 1))).sum =
      ((splitAll cfg (q + 1) hnum (advanceAll cfg q hnum he frame.choices paths hshort)).map
        (shortCount hnum rest d)).sum := by
  induction paths with
  | nil => rfl
  | cons P paths ih =>
      have hP := shortCount_step hnum he frame valid rest P (hshort P List.mem_cons_self) d
      have ht := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      simp only [List.map_cons, List.sum_cons, advanceAll, splitAll, List.flatMap_append,
        List.map_append, List.sum_append]
      exact congrArg₂ Nat.add hP ht

theorem familyCount_step (hnum : 0 < cfg.initialNumerator) (he : q < cfg.earlyLevel)
    (frame : Frame n cfg queue.toArray.size) (valid : FrameValid cfg stored input rank q queue.toArray.toVector frame)
    (rest : FullExecution cfg stored input rank fuel (q + 1)
      (geometricChildren cfg q stored input queue.toArray.toVector frame.choices))
    (paths : List (TrackedPath stored input queue.toArray.toVector)) (d : ℕ) :
    familyCount hnum (.next frame valid rest) paths (d + 1) =
      familyCount hnum rest
        (advanceAll cfg q hnum he frame.choices (splitAll cfg q hnum paths)
          (splitAll_short cfg q hnum paths)) d :=
  shortCounts_step hnum he frame valid rest _ (splitAll_short cfg q hnum paths) d

end

end StreamingReachability.Hopset.Following
