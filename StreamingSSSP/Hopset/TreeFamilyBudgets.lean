module

public import StreamingSSSP.Hopset.TreeRouteRealization
public import StreamingSSSP.Hopset.ShortTreeCounts
public import StreamingSSSP.Hopset.DetourCalibration
public import StreamingSSSP.Hopset.TreeLateWeights

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical BigOperators
open Batched

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}
    {fuel q : ℕ} {queue : List (Finset (Fin n))}

def shortSize (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (P : TrackedPath stored input queue.toArray.toVector) : ℕ :=
  if hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q then
    (shortTree hnum run P hshort).size
  else 0

theorem shortSize_eq (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    shortSize hnum run P = (shortTree hnum run P hshort).size := by
  simp only [shortSize, hshort, ↓reduceDIte]

def familySize (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector)) : ℕ :=
  ((splitAll cfg q hnum paths).map (shortSize hnum run)).sum

theorem shortSize_counts (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) :
    (shortSize hnum run P : ℝ) =
      ∑ d ∈ Finset.range (cfg.earlyLevel - q + 1), (shortCount hnum run d P : ℝ) := by
  rw [shortSize_eq hnum run P hshort, PieceTree.size_counts _ _ (shortTree_height hnum run P hshort)]
  exact Finset.sum_congr rfl (fun d _ =>
    congrArg (fun k : ℕ => (k : ℝ)) (shortCount_eq hnum run d P hshort).symm)

theorem familySize_counts (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector)) :
    (familySize hnum run paths : ℝ) =
      ∑ d ∈ Finset.range (cfg.earlyLevel - q + 1), (familyCount hnum run paths d : ℝ) := by
  let roots := splitAll cfg q hnum paths
  change ((roots.map (shortSize hnum run)).sum : ℝ) = _
  rw [list_sum_indices roots (shortSize hnum run), Nat.cast_sum]
  calc
    _ = ∑ i : Fin roots.length, ∑ d ∈ Finset.range (cfg.earlyLevel - q + 1),
        (shortCount hnum run d (roots.get i) : ℝ) :=
      Finset.sum_congr rfl (fun i _ =>
        shortSize_counts hnum run (roots.get i) (splitAll_short cfg q hnum paths _ (List.get_mem roots i)))
    _ = ∑ d ∈ Finset.range (cfg.earlyLevel - q + 1),
        ∑ i : Fin roots.length, (shortCount hnum run d (roots.get i) : ℝ) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      change _ = ((roots.map (shortCount hnum run d)).sum : ℝ)
      rw [list_sum_indices roots (shortCount hnum run d), Nat.cast_sum]

theorem family_debt_profile (hnum : 0 < cfg.initialNumerator)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector))
    (F : Graph (Fin n)) (solve : (P : TrackedPath stored input queue.toArray.toVector) → SearchSolution cfg F P)
    (hsolve : ∀ P (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q),
      ((solve P).debt : ℝ) ≤ ((shortTree hnum run P hshort).prune cfg.advance).markSum nodeDetour) :
    (((splitAll cfg q hnum paths).map fun P => (solve P).debt).sum : ℝ) ≤
      ∑ d ∈ Finset.range (cfg.earlyLevel - q + 1),
        Reference.detourAt cfg (q + d) * (familyCount hnum run paths d : ℝ) := by
  let roots := splitAll cfg q hnum paths
  let hroot := fun i : Fin roots.length => splitAll_short cfg q hnum paths _ (List.get_mem roots i)
  let tree := fun i : Fin roots.length => shortTree hnum run (roots.get i)
    (hroot i)
  change ((roots.map fun P => (solve P).debt).sum : ℝ) ≤ _
  rw [list_sum_indices roots (fun P => (solve P).debt), Nat.cast_sum]
  calc
    _ ≤ ∑ i : Fin roots.length, (tree i).profileSum (Reference.detourAt cfg) q := by
      apply Finset.sum_le_sum
      intro i _
      exact (hsolve (roots.get i) (hroot i)).trans
        ((tree i).markSum_prune_le_profile cfg.advance ShortNode.level (Reference.detourAt cfg)
          (Reference.detourAt_nonneg cfg) q (shortTree_leveled hnum run (roots.get i) (hroot i)))
    _ = ∑ i : Fin roots.length, ∑ d ∈ Finset.range (cfg.earlyLevel - q + 1),
        Reference.detourAt cfg (q + d) * (shortCount hnum run d (roots.get i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [PieceTree.profileSum_counts _ _ _ _ (shortTree_height hnum run (roots.get i) (hroot i))]
      apply Finset.sum_congr rfl
      intro d _
      rw [shortCount_eq hnum run d _ (splitAll_short cfg q hnum paths _ (List.get_mem roots i))]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      change _ = Reference.detourAt cfg (q + d) * ((roots.map (shortCount hnum run d)).sum : ℝ)
      rw [list_sum_indices roots (shortCount hnum run d), Nat.cast_sum, Finset.mul_sum]

theorem short_solution_hops (hnum : 0 < cfg.initialNumerator) (hn : 0 < n) (hL : 0 < cfg.advance)
    (run : FullExecution cfg stored input rank fuel q queue)
    (P : TrackedPath stored input queue.toArray.toVector)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q)
    (hglobal : ∀ d < cfg.advance, ¬ (shortTree hnum run P hshort).bridgeAt d)
    (F : Graph (Fin n)) (solution : SearchSolution cfg F P)
    (hhops : solution.hops ≤ ((shortTree hnum run P hshort).prune cfg.advance).hopTally originalNodeHops (lateNodeHops hn)) :
    solution.hops + 2 ≤ 4 * shortSize hnum run P + shortLateWeight hnum hn run P := by
  let T := shortTree hnum run P hshort
  have hno : ∀ d, ¬ (T.prune cfg.advance).bridgeAt d := T.prune_no_bridge cfg.advance hL hglobal
  have ht := (T.prune cfg.advance).hopTally_bound originalNodeHops (lateNodeHops hn) hno
  rw [shortSize_eq hnum run P hshort, shortLateWeight_eq hnum hn run P hshort]
  calc
    _ ≤ (T.prune cfg.advance).hopTally originalNodeHops (lateNodeHops hn) + 2 := Nat.add_le_add_right hhops 2
    _ ≤ 4 * (T.prune cfg.advance).size + (T.prune cfg.advance).lateWeight (lateNodeHops hn) := ht
    _ ≤ _ := Nat.add_le_add (Nat.mul_le_mul_left 4 (T.size_prune_le cfg.advance))
      (T.lateWeight_prune_le cfg.advance (lateNodeHops hn))

theorem family_solution_hops (hnum : 0 < cfg.initialNumerator) (hn : 0 < n) (hL : 0 < cfg.advance)
    (run : FullExecution cfg stored input rank fuel q queue)
    (paths : List (TrackedPath stored input queue.toArray.toVector))
    (hglobal : ∀ P ∈ splitAll cfg q hnum paths,
      ∀ (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q) (d : ℕ),
        d < cfg.advance → ¬ (shortTree hnum run P hshort).bridgeAt d)
    (F : Graph (Fin n)) (solve : (P : TrackedPath stored input queue.toArray.toVector) → SearchSolution cfg F P)
    (hhops : ∀ P (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg q),
      (solve P).hops ≤ ((shortTree hnum run P hshort).prune cfg.advance).hopTally originalNodeHops (lateNodeHops hn)) :
    ((splitAll cfg q hnum paths).map fun P => (solve P).hops).sum + 2 * (splitAll cfg q hnum paths).length ≤
      4 * familySize hnum run paths + familyLateWeight hnum hn run paths := by
  let roots := splitAll cfg q hnum paths
  have hone (i : Fin roots.length) :
      (solve (roots.get i)).hops + 2 ≤
        4 * shortSize hnum run (roots.get i) + shortLateWeight hnum hn run (roots.get i) := by
    have hshort := splitAll_short cfg q hnum paths _ (List.get_mem roots i)
    exact short_solution_hops hnum hn hL run (roots.get i) hshort
      (hglobal _ (List.get_mem roots i) hshort) F (solve (roots.get i)) (hhops (roots.get i) hshort)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin roots.length))) (fun i _ => hone i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id, ← Finset.mul_sum] at hs
  change ((roots.map fun P => (solve P).hops).sum + 2 * roots.length) ≤
    4 * (roots.map (shortSize hnum run)).sum + (roots.map (shortLateWeight hnum hn run)).sum
  rw [list_sum_indices roots (fun P => (solve P).hops), list_sum_indices roots (shortSize hnum run),
    list_sum_indices roots (shortLateWeight hnum hn run)]
  omega

end

end StreamingSSSP.Hopset.Following
