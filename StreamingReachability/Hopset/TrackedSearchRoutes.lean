module

public import StreamingReachability.Hopset.TrackedNextPieces
public import StreamingReachability.Hopset.EarlyPlanSearchRoutes

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

structure SearchSolution (cfg : Config) (F : Graph (Fin n))
    (P : TrackedPath stored input sets) where
  debt : ℕ
  route : Late.Route F P.source P.target (cfg.inputScale * (P.path.searchWeight cfg.inputScale + debt))

namespace SearchSolution

variable (cfg : Config) (F : Graph (Fin n))

def hops {cfg : Config} {F : Graph (Fin n)} {P : TrackedPath stored input sets}
    (solution : SearchSolution cfg F P) : ℕ :=
  solution.route.hops

def original (hF : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (P : TrackedPath stored input sets) : SearchSolution cfg F P :=
  ⟨0, (P.path.originalRoute F hF).weaken
    (by simpa only [Nat.add_zero] using P.path.micro_le_search cfg.inputScale cfg.inputScale_pos)⟩

def splitWith (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (hF : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (solve : (Q : TrackedPath stored input sets) → SearchSolution cfg F Q)
    (P : TrackedPath stored input sets) : SearchSolution cfg F P :=
  let B := P.type2Plan cfg r hnum
  let debt := fun C => (solve (TrackedPath.ofChild P.node (A := cfg.inputScale)
    (D := Reference.distanceScale cfg r) C)).debt
  let child := fun C => (solve (TrackedPath.ofChild P.node (A := cfg.inputScale)
    (D := Reference.distanceScale cfg r) C)).route
  ⟨(B.pieces.map debt).sum, B.assembleSearch cfg.inputScale_pos hF debt child⟩

theorem splitWith_debt (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (hF : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (solve : (Q : TrackedPath stored input sets) → SearchSolution cfg F Q)
    (P : TrackedPath stored input sets) :
    (splitWith cfg F r hnum hF solve P).debt =
      ((P.split cfg r hnum).map fun Q => (solve Q).debt).sum := by
  simp only [splitWith, TrackedPath.split, List.map_map, Function.comp_def]

theorem splitWith_hops (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (hF : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (solve : (Q : TrackedPath stored input sets) → SearchSolution cfg F Q)
    (P : TrackedPath stored input sets) :
    (splitWith cfg F r hnum hF solve P).hops ≤
      (P.split cfg r hnum).length + ((P.split cfg r hnum).map fun Q => (solve Q).hops).sum := by
  let B := P.type2Plan cfg r hnum
  let debt := fun C => (solve (TrackedPath.ofChild P.node (A := cfg.inputScale)
    (D := Reference.distanceScale cfg r) C)).debt
  let child := fun C => (solve (TrackedPath.ofChild P.node (A := cfg.inputScale)
    (D := Reference.distanceScale cfg r) C)).route
  have hh := B.assembleSearch_hops cfg.inputScale_pos hF debt child
  have hn := B.piece_count
  change (B.assembleSearch cfg.inputScale_pos hF debt child).hops ≤
    (P.split cfg r hnum).length + ((P.split cfg r hnum).map fun Q => (solve Q).route.hops).sum
  simp only [TrackedPath.split, List.length_map, List.map_map, Function.comp_def]
  change (B.assembleSearch cfg.inputScale_pos hF debt child).hops ≤
    B.pieces.length + (B.pieces.map fun C => (child C).hops).sum
  exact hh.trans (Nat.add_le_add_right (by omega : B.boundaries ≤ B.pieces.length) _)

end SearchSolution

theorem mapped_flatMap_sum {A B : Type*} (xs : List A) (f : A → List B) (g : B → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem TrackedPath.advance_search_solution (cfg : Config) (r : ℕ)
    (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (hstop : ¬ Early.stopped (P.localView cfg r hshort) (choices P.node).pivots
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)))
    (F : Graph (Fin n)) (hF : ∀ u v, F u v ≤ stored.graph (StoredEdges.graphOfEdges input) u v)
    (solve : (Q : TrackedPath stored input
      (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector) → SearchSolution cfg F Q) :
    ∃ solution : SearchSolution cfg F P,
      solution.debt = ((P.nextPieces cfg r hnum he choices hshort).map fun Q => (solve Q).debt).sum ∧
      solution.hops ≤ 2 * (P.nextPieces cfg r hnum he choices hshort).length +
        ((P.nextPieces cfg r hnum he choices hshort).map fun Q => (solve Q).hops).sum := by
  let B := P.earlyPlan cfg r hnum hshort (choices P.node) hstop
  let next := Batched.geometricChildren cfg r stored input sets choices
  let raw := fun (label : B.Label)
      (C : Late.ChildPiece stored (StoredEdges.graphOfEdges input) (B.target label) cfg.inputScale
        (Reference.distanceScale cfg r)) =>
    TrackedPath.schedule next (B.target label) (P.earlyPlan_target_mem cfg r hnum he choices hshort hstop label) C
  let joined := fun label C => SearchSolution.splitWith cfg F (r + 1) hnum hF solve (raw label C)
  let debt := fun label C => (joined label C).debt
  let child := fun label C => (joined label C).route
  obtain ⟨T, hT⟩ := B.build_search_route cfg.inputScale_pos hF debt child
  let solution : SearchSolution cfg F P := ⟨∑ i : B.ChildIndex, debt i.1 (B.piece i), T⟩
  let rawPaths := P.advance cfg r hnum he choices hshort
  let rawPiece := fun i : B.ChildIndex => raw i.1 (by exact B.piece i)
  have hraw : rawPaths = (Finset.univ : Finset B.ChildIndex).toList.map
      rawPiece := by
    simp only [rawPaths, TrackedPath.advance, hstop, ↓reduceDIte]
    rfl
  have hsum (f : TrackedPath stored input next.toArray.toVector → ℕ) :
      ((P.nextPieces cfg r hnum he choices hshort).map f).sum =
        ∑ i : B.ChildIndex, (((rawPiece i).split cfg (r + 1) hnum).map f).sum := by
    change ((splitAll cfg (r + 1) hnum rawPaths).map f).sum = _
    rw [hraw]
    simp only [splitAll, mapped_flatMap_sum, List.map_map, Function.comp_def, Finset.sum_map_toList]
  have hlength : (P.nextPieces cfg r hnum he choices hshort).length =
      ∑ i : B.ChildIndex, ((rawPiece i).split cfg (r + 1) hnum).length := by
    change (splitAll cfg (r + 1) hnum rawPaths).length = _
    rw [hraw]
    simp only [splitAll, List.length_flatMap, List.map_map, Function.comp_def, Finset.sum_map_toList]
  have hrawLength : rawPaths.length = B.overhead := by
    rw [hraw]
    simp only [List.length_map, Finset.length_toList, Finset.card_univ]
    exact B.child_count
  have hbase : B.overhead ≤ (P.nextPieces cfg r hnum he choices hshort).length := by
    have h := splitAll_length cfg (r + 1) hnum rawPaths
    change (P.nextPieces cfg r hnum he choices hshort).length = _ at h
    omega
  have hdebt : solution.debt =
      ((P.nextPieces cfg r hnum he choices hshort).map fun Q => (solve Q).debt).sum := by
    rw [hsum]
    change (∑ i : B.ChildIndex, (joined i.1 (B.piece i)).debt) = _
    apply Finset.sum_congr rfl
    intro i _
    exact SearchSolution.splitWith_debt cfg F (r + 1) hnum hF solve _
  have hhops := Finset.sum_le_sum (s := (Finset.univ : Finset B.ChildIndex))
    (fun i _ => SearchSolution.splitWith_hops cfg F (r + 1) hnum hF solve (rawPiece i))
  rw [Finset.sum_add_distrib, ← hlength, ← hsum (fun Q => (solve Q).hops)] at hhops
  change T.hops ≤ B.overhead + ∑ i : B.ChildIndex, (joined i.1 (B.piece i)).hops at hT
  refine ⟨solution, hdebt, ?_⟩
  change T.hops ≤ _
  calc
    _ ≤ B.overhead + ∑ i : B.ChildIndex,
        (SearchSolution.splitWith cfg F (r + 1) hnum hF solve (rawPiece i)).hops := hT
    _ ≤ B.overhead + ((P.nextPieces cfg r hnum he choices hshort).length +
        ((P.nextPieces cfg r hnum he choices hshort).map fun Q => (solve Q).hops).sum) :=
      Nat.add_le_add_left hhops _
    _ ≤ _ := by omega

end

end StreamingReachability.Hopset.Following
