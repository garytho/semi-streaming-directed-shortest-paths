module

public import StreamingSSSP.Core.GuardedInterface
public import StreamingSSSP.Hopset.Trial

@[expose] public section

namespace StreamingSSSP.Hopset.Backend

open scoped Classical
open StoredEdges

variable {n nb ns nq : ℕ}

theorem vector_indices {A : Type*} {m : ℕ} (xs : Vector A m) :
    (List.finRange m).map xs.get = xs.toList := by
  rw [← List.ofFn_eq_map, ← Vector.toList_ofFn]
  congr 1
  ext i hi
  simp [Vector.get_eq_getElem]

theorem fold_membership (blocks : List (Finset (Fin n))) (v : Fin n) (start : ℕ) :
    blocks.foldl (fun count B => if v ∈ B then count + 1 else count) start =
      start + (blocks.filter fun B => decide (v ∈ B)).length := by
  induction blocks generalizing start with
  | nil => simp
  | cons B blocks ih =>
      by_cases h : v ∈ B <;> simp [h, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem vertexCharge (c : Core.Shared.Catalog n nb ns nq) (v : Fin n) :
    Core.RecordGuard.vertexCharge c v =
      1 + (c.blocks.toList.filter fun B => decide (v ∈ B)).length := by
  unfold Core.RecordGuard.vertexCharge
  rw [← List.foldl_map (f := c.blocks.get)
    (g := fun (count : ℕ) (B : Finset (Fin n)) =>
      if v ∈ B then count + 1 else count) (l := List.finRange nb)]
  rw [vector_indices, fold_membership, Nat.zero_add]

theorem replyCharge (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (workspace : ℕ) (reply : Core.BatchAPI.SparseReply n) :
    Core.BatchAPI.replyCharge
        (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg r stored.blocks sets targets) workspace) reply =
      recordCharge stored.blocks reply := by
  unfold Core.BatchAPI.replyCharge recordCharge
  congr 1
  apply List.map_congr_left
  intro record _
  rw [vertexCharge]
  simp [Core.BatchAPI.Request.ofCatalog, catalog, Vector.toList_mk, List.toList_toArray]

def edgeView (S : Finset (Fin n)) (backward : Bool) (e : Edge n) : Option (Edge n) :=
  if e.source ∈ S ∧ e.target ∈ S then some (Core.OrdinaryScan.orient backward e) else none

theorem graph_view_forward (S : Finset (Fin n)) (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges (edges.filterMap (edgeView S false)) u v =
      Implicit.induced (graphOfEdges edges) S u v := by
  induction edges with
  | nil => simp [edgeView, Implicit.induced]
  | cons e edges ih =>
      by_cases h : u ∈ S ∧ v ∈ S
      · by_cases he : e.source ∈ S ∧ e.target ∈ S
        · simp [edgeView, Core.OrdinaryScan.orient, he, ih, Implicit.induced, h]
        · have hne : ¬ (e.source = u ∧ e.target = v) := by
            intro hends
            apply he
            simpa only [hends.1, hends.2] using h
          simp [edgeView, Core.OrdinaryScan.orient, he, ih, Implicit.induced,
            h, edgeCost, hne]
      · by_cases he : e.source ∈ S ∧ e.target ∈ S
        · have hne : ¬ (e.source = u ∧ e.target = v) := by
            intro hends
            apply h
            simpa only [hends.1, hends.2] using he
          simp [edgeView, Core.OrdinaryScan.orient, he, ih, Implicit.induced,
            h, edgeCost, hne]
        · simp [edgeView, Core.OrdinaryScan.orient, he, ih, Implicit.induced, h]

theorem graph_view_backward (S : Finset (Fin n)) (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges (edges.filterMap (edgeView S true)) u v =
      graphOfEdges (edges.filterMap (edgeView S false)) v u := by
  induction edges with
  | nil => rfl
  | cons e edges ih =>
      by_cases h : e.source ∈ S ∧ e.target ∈ S <;>
        simp [edgeView, Core.OrdinaryScan.orient, edgeCost, h, ih, and_comm]

theorem graph_view (S : Finset (Fin n)) (backward : Bool) (edges : List (Edge n)) :
    graphOfEdges (edges.filterMap (edgeView S backward)) =
      if backward then (Implicit.induced (graphOfEdges edges) S).reverse
      else Implicit.induced (graphOfEdges edges) S := by
  funext u v
  cases backward
  · exact graph_view_forward S edges u v
  · exact (graph_view_backward S edges u v).trans (graph_view_forward S edges v u)

theorem closures_inf (G : Graph (Fin n)) (blocks : List (Finset (Fin n))) (u v : Fin n) :
    Implicit.closures G blocks u v =
      min (G u v) (blocks.toFinset.inf fun B => Implicit.closure G B u v) := by
  induction blocks with
  | nil => simp [Implicit.closures]
  | cons B blocks ih =>
      simp only [Implicit.closures, Graph.union_apply, ih, List.toFinset_cons,
        Finset.inf_insert]
      exact min_left_comm _ _ _

theorem queryGraph_rounding (edges : List (Edge n)) (blocks : List (Finset (Fin n)))
    (A : ℕ) (hA : 0 < A) (u v : Fin n) :
    Core.queryGraph edges blocks A u v =
      Core.roundDistance A (Implicit.closures (graphOfEdges edges) blocks u v) := by
  rw [closures_inf, Core.roundDistance_min A hA, Core.roundDistance_inf A hA]
  unfold Core.queryGraph
  congr 1
  apply Finset.inf_congr rfl
  intro B _
  have hblock : Core.BlockSearch.blockGraph edges B =
      Implicit.induced (graphOfEdges edges) B := by
    funext a b
    by_cases h : a ∈ B ∧ b ∈ B <;>
      simp [Core.BlockSearch.blockGraph, Implicit.induced, h]
  rw [hblock]
  by_cases h : u ∈ B ∧ v ∈ B ∧ u ≠ v <;>
    simp [Implicit.closure, h, Core.roundDistance]

theorem induced_reverse (G : Graph (Fin n)) (S : Finset (Fin n)) :
    Implicit.induced G.reverse S = (Implicit.induced G S).reverse := by
  funext u v
  simp [Implicit.induced, Graph.reverse, and_comm]

theorem closure_reverse (G : Graph (Fin n)) (B : Finset (Fin n)) (u v : Fin n) :
    Implicit.closure G.reverse B u v = Implicit.closure G B v u := by
  unfold Implicit.closure
  rw [induced_reverse, Graph.dist_reverse]
  simp [and_comm, and_left_comm, and_assoc, ne_comm]

theorem closures_reverse (G : Graph (Fin n)) (blocks : List (Finset (Fin n))) :
    Implicit.closures G.reverse blocks = (Implicit.closures G blocks).reverse := by
  funext u v
  induction blocks with
  | nil => rfl
  | cons B blocks ih =>
      simp only [Implicit.closures, Graph.union_apply, closure_reverse, Graph.reverse] at *
      rw [ih]

theorem reference_blocks (c : Core.Shared.Catalog n nb ns nq) (j : Fin nq) :
    (Core.Shared.referenceProblem c j).blocks.toList =
      c.blocks.toList.map (fun B => B ∩ Core.Shared.vertices c j) := by
  simp only [Core.Shared.referenceProblem, Core.Shared.block, Vector.toList_ofFn]
  rw [← vector_indices, List.map_map, ← List.ofFn_eq_map]
  rfl

noncomputable def roundedRestricted (stored : Implicit.Representation n)
    (input : List (Edge n)) (S : Finset (Fin n)) (A : ℕ) : Graph (Fin n) :=
  fun u v => Core.roundDistance A (stored.restricted (graphOfEdges input) S u v)

theorem base_input (stored : Implicit.Representation n) (input : List (Edge n)) :
    graphOfEdges (stored.explicit ++ input) = stored.base (graphOfEdges input) := by
  rw [graphOfEdges_append]
  funext u v
  exact min_comm _ _

theorem viewed_closures (stored : Implicit.Representation n) (input : List (Edge n))
    (S : Finset (Fin n)) (backward : Bool) :
    Implicit.closures
        (graphOfEdges ((stored.explicit ++ input).filterMap (edgeView S backward)))
        (stored.blocks.map (· ∩ S)) =
      if backward then (stored.restricted (graphOfEdges input) S).reverse
      else stored.restricted (graphOfEdges input) S := by
  rw [graph_view, base_input]
  cases backward
  · rfl
  · exact closures_reverse _ _

theorem queryGraph_model (stored : Implicit.Representation n) (input : List (Edge n))
    (S : Finset (Fin n)) (backward : Bool) (A : ℕ) (hA : 0 < A) :
    Core.queryGraph ((stored.explicit ++ input).filterMap (edgeView S backward))
        (stored.blocks.map (· ∩ S)) A =
      if backward then (roundedRestricted stored input S A).reverse
      else roundedRestricted stored input S A := by
  funext u v
  rw [queryGraph_rounding _ _ A hA, viewed_closures]
  cases backward <;> rfl

theorem distance_model (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (Edge n))
    (hblocks : c.blocks.toList = stored.blocks) (hA : 0 < c.scale)
    (j : Fin nq) (s t : Fin n) :
    (Core.fullQueryGraph ((stored.explicit ++ input).filterMap (Core.Shared.view c j))
        (Core.Shared.referenceProblem c j).blocks.toList c.scale).dist s t =
      (if (c.searches.get j).backward then
          (roundedRestricted stored input (Core.Shared.vertices c j) c.scale).reverse
        else roundedRestricted stored input (Core.Shared.vertices c j) c.scale).dist s t := by
  rw [← Core.queryGraph_dist_eq_full, reference_blocks, hblocks]
  have hview : Core.Shared.view c j =
      edgeView (Core.Shared.vertices c j) (c.searches.get j).backward := rfl
  rw [hview, queryGraph_model stored input _ _ c.scale hA]

theorem raw_lookup (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hblocks : c.blocks.toList = stored.blocks) (hA : 0 < c.scale) (workspace : ℕ)
    (hx : ∀ i, (c.blocks.get i).card ≤ workspace)
    (j : Fin nq) (v : Fin n) :
    lookup (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c workspace) input).records
        j.val v =
      let F := if (c.searches.get j).backward then
          (roundedRestricted stored input (Core.Shared.vertices c j) c.scale).reverse
        else roundedRestricted stored input (Core.Shared.vertices c j) c.scale
      if F.dist (c.searches.get j).source v ≤ ((c.searches.get j).radius : Distance)
        then F.dist (c.searches.get j).source v else ⊤ := by
  let request := Core.BatchAPI.Request.ofCatalog stored.explicit c workspace
  have h := Core.BatchAPI.run_correct request input hn hs hp hA hx j v
  change Core.BatchAPI.lookup _ _ _ = _
  dsimp only [request, Core.BatchAPI.Request.ofCatalog] at h
  simp only [distance_model c stored input hblocks hA j] at h
  exact h

def guardedHandler (input : List (Edge n)) : Code.Handler n :=
  fun request budget => Law.pure <|
    match Core.BatchAPI.runGuarded request budget input with
    | .error _ => none
    | .ok result => some result.records

def rawHandler (input : List (Edge n)) : Code.Handler n :=
  fun request _ => Law.pure (some (Core.BatchAPI.run request input).records)

end StreamingSSSP.Hopset.Backend
