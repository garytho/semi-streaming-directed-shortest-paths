module

public import StreamingReachability.Hopset.FullExecution
public import StreamingReachability.Hopset.TrackedNextPieces
public import StreamingReachability.Hopset.AncestorPruning

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}

structure ShortNode (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) where
  level : ℕ
  fuel : ℕ
  queue : List (Finset (Fin n))
  execution : FullExecution cfg stored input rank fuel level queue
  piece : TrackedPath stored input queue.toArray.toVector
  short : (piece.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg level

namespace ShortNode

def ofRun {fuel r : ℕ} {queue : List (Finset (Fin n))}
    (run : FullExecution cfg stored input rank fuel r queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    ShortNode cfg stored input rank :=
  ⟨r, fuel, queue, run, P, hshort⟩

def vertexSet (node : ShortNode cfg stored input rank) : Finset (Fin n) :=
  node.queue.toArray.toVector.get node.piece.node

structure Descent (parent child : ShortNode cfg stored input rank) (depth : ℕ) : Prop where
  level : child.level = parent.level + depth
  subpath : child.piece.path.IsSubpath parent.piece.path
  subset : child.vertexSet ⊆ parent.vertexSet
  entries : child.execution.entries ⊆ parent.execution.entries

theorem Descent.refl (node : ShortNode cfg stored input rank) : Descent node node 0 :=
  ⟨(Nat.add_zero _).symm, .refl _, Finset.Subset.refl _, List.Subset.refl _⟩

theorem Descent.trans {parent child leaf : ShortNode cfg stored input rank} {d e : ℕ}
    (h : Descent parent child d) (k : Descent child leaf e) :
    Descent parent leaf (d + e) :=
  ⟨by rw [k.level, h.level, Nat.add_assoc],
    k.subpath.trans h.subpath, k.subset.trans h.subset,
    fun _ he => h.entries (k.entries he)⟩

structure BridgeWitness (parent : ShortNode cfg stored input rank) (depth : ℕ) where
  node : ShortNode cfg stored input rank
  descent : Descent parent node depth
  pivot : Fin n
  early : node.level < cfg.earlyLevel
  rank_eq : rank.get pivot = node.level
  mem : pivot ∈ node.vertexSet
  bridge : Early.Bridge (node.piece.localView cfg node.level node.short) pivot
    (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg node.level))

end ShortNode

def shortTree (hnum : 0 < cfg.initialNumerator) :
    {fuel r : ℕ} → {queue : List (Finset (Fin n))} →
    (run : FullExecution cfg stored input rank fuel r queue) →
    (P : TrackedPath stored input queue.toArray.toVector) →
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) →
    PieceTree (ShortNode cfg stored input rank)
  | _, _, _, .done r queue, P, hshort =>
      .late (ShortNode.ofRun (.done r queue) P hshort)
  | _, r, _, run@(.next frame _ rest), P, hshort =>
      let node := ShortNode.ofRun run P hshort
      if he : r < cfg.earlyLevel then
        if Early.stopped (P.localView cfg r hshort) (frame.choices P.node).pivots
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) then
          .bridge node
        else
          let children := P.nextPieces cfg r hnum he frame.choices hshort
          .branch node children.length (fun i =>
            shortTree hnum rest (children.get i)
              (P.nextPieces_short cfg r hnum he frame.choices hshort _ (List.get_mem children i)))
      else .late node

theorem shortTree_value (hnum : 0 < cfg.initialNumerator) {fuel r : ℕ}
    {queue : List (Finset (Fin n))} (run : FullExecution cfg stored input rank fuel r queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    (shortTree hnum run P hshort).value = ShortNode.ofRun run P hshort := by
  cases run with
  | done => rfl
  | next frame valid rest =>
      simp only [shortTree]
      split_ifs <;> rfl

theorem shortTree_bridge (hnum : 0 < cfg.initialNumerator) {fuel r : ℕ}
    {queue : List (Finset (Fin n))} (run : FullExecution cfg stored input rank fuel r queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (depth : ℕ) (hbridge : (shortTree hnum run P hshort).bridgeAt depth) :
    Nonempty (ShortNode.BridgeWitness (ShortNode.ofRun run P hshort) depth) := by
  induction run generalizing depth with
  | done =>
      simp only [shortTree, PieceTree.bridgeAt] at hbridge
  | @next fuel r queue frame valid rest ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hs : Early.stopped (P.localView cfg r hshort) (frame.choices P.node).pivots
            (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        · cases depth with
          | succ d => simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.bridgeAt] at hbridge
          | zero =>
              obtain ⟨p, hp, hb⟩ := hs
              have hmem := valid.subset P.node hp
              have hrank := hp
              rw [valid.earlyPivots he P.node] at hrank
              have hr : rank.get p = r := by
                have hpair : p ∈ queue.toArray.toVector.get P.node ∧ rank.get p = r := by
                  simpa only [CopyHistory.pivots, Finset.mem_filter] using hrank
                exact hpair.2
              exact ⟨⟨ShortNode.ofRun (.next frame valid rest) P hshort, .refl _, p, he, hr, hmem, hb⟩⟩
        · cases depth with
          | zero => simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.bridgeAt] at hbridge
          | succ d =>
              let children := P.nextPieces cfg r hnum he frame.choices hshort
              simp only [shortTree, he, hs, ↓reduceDIte, ↓reduceIte, PieceTree.bridgeAt] at hbridge
              change ∃ i : Fin children.length,
                (shortTree hnum rest (children.get i)
                  (P.nextPieces_short cfg r hnum he frame.choices hshort _ (List.get_mem children i))).bridgeAt d at hbridge
              obtain ⟨i, hi⟩ := hbridge
              let Q := children.get i
              have hQ : Q ∈ P.nextPieces cfg r hnum he frame.choices hshort := List.get_mem children i
              have hq := P.nextPieces_short cfg r hnum he frame.choices hshort Q hQ
              obtain ⟨w⟩ := ih Q hq d hi
              have step : ShortNode.Descent
                  (ShortNode.ofRun (.next frame valid rest) P hshort)
                  (ShortNode.ofRun rest Q hq) 1 :=
                ⟨rfl, P.nextPieces_subpath cfg r hnum he frame.choices hshort Q hQ,
                  P.nextPieces_set_subset cfg r hnum he frame.choices hshort Q hQ,
                  fun entry hentry => List.mem_cons_of_mem _ hentry⟩
              refine ⟨⟨w.node, ?_, w.pivot, w.early, w.rank_eq, w.mem, w.bridge⟩⟩
              simpa only [Nat.add_comm 1 d] using step.trans w.descent
      · simp only [shortTree, he, ↓reduceDIte, PieceTree.bridgeAt] at hbridge

end

end StreamingReachability.Hopset.Following
