module

public import StreamingSSSP.Hopset.ShortTrees
public import StreamingSSSP.Hopset.TreeBudgets

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

theorem shortTree_leveled (hnum : 0 < cfg.initialNumerator) {fuel r : ℕ}
    {queue : List (Finset (Fin n))} (run : FullExecution cfg stored input rank fuel r queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    (shortTree hnum run P hshort).Leveled ShortNode.level r := by
  induction run with
  | done => rfl
  | @next fuel r queue frame valid rest ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hs : Early.stopped (P.localView cfg r hshort) (frame.choices P.node).pivots
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        · simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.Leveled, ShortNode.ofRun]
        · simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.Leveled, ShortNode.ofRun]
          exact ⟨trivial, fun i => ih _ _⟩
      · simp only [shortTree, he, ↓reduceDIte, PieceTree.Leveled, ShortNode.ofRun]

theorem shortTree_height (hnum : 0 < cfg.initialNumerator) {fuel r : ℕ}
    {queue : List (Finset (Fin n))} (run : FullExecution cfg stored input rank fuel r queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    (shortTree hnum run P hshort).height ≤ cfg.earlyLevel - r := by
  induction run with
  | done => exact Nat.zero_le _
  | @next fuel r queue frame valid rest ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hs : Early.stopped (P.localView cfg r hshort) (frame.choices P.node).pivots
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        · simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.height, Nat.zero_le]
        · let children := P.nextPieces cfg r hnum he frame.choices hshort
          let childTree := fun i : Fin children.length => shortTree hnum rest (children.get i)
            (P.nextPieces_short cfg r hnum he frame.choices hshort _ (List.get_mem children i))
          have hm : (Finset.univ : Finset (Fin children.length)).sup (fun i => (childTree i).height) ≤
              cfg.earlyLevel - (r + 1) := by
            apply Finset.sup_le
            intro i _
            exact ih _ _
          simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.height]
          change 1 + (Finset.univ : Finset (Fin children.length)).sup (fun i => (childTree i).height) ≤ _
          omega
      · simp only [shortTree, he, ↓reduceDIte, PieceTree.height, Nat.zero_le]

end

end StreamingSSSP.Hopset.Following
