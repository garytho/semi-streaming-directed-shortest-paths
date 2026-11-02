module

public import StreamingReachability.Hopset.Representation

@[expose] public section

namespace StreamingReachability.Implicit

open scoped Classical

variable {V : Type*}

theorem endpoints_mem {xs : List V} {s t : V} (h : Graph.Endpoints xs s t) :
    s ∈ xs ∧ t ∈ xs := by
  constructor
  · cases xs with
    | nil => simp [Graph.Endpoints] at h
    | cons x xs =>
        have he : x = s := by simpa [Graph.Endpoints] using h.1
        simp [he]
  · obtain ⟨ys, he⟩ := List.getLast?_eq_some_iff.mp h.2
    rw [he]
    simp

theorem induced_path_cost (G : Graph V) (S : Finset V) (xs : List V)
    (hS : ∀ v ∈ xs, v ∈ S) :
    (induced G S).pathCost xs = G.pathCost xs := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
      cases xs with
      | nil => simp
      | cons v xs =>
          have hu := hS u (by simp)
          have hv := hS v (by simp)
          have ht : ∀ z ∈ v :: xs, z ∈ S := fun z hz => hS z (by simp [hz])
          have hin : u ∈ S ∧ v ∈ S := ⟨hu, hv⟩
          simp only [Graph.pathCost_cons_cons, induced, ite_eq_left hin, ih ht]

theorem induced_path_members (G : Graph V) (S : Finset V) (u : V) (xs : List V)
    (hu : u ∈ S) (hf : (induced G S).pathCost (u :: xs) ≠ ⊤) :
    ∀ v ∈ u :: xs, v ∈ S := by
  induction xs generalizing u with
  | nil => simpa using hu
  | cons v xs ih =>
      have hv : v ∈ S := by
        by_contra hn
        simp [Graph.pathCost_cons_cons, induced, hn] at hf
      have ht : (induced G S).pathCost (v :: xs) ≠ ⊤ := by
        intro he
        have hh := Graph.pathCost_tail_le (induced G S) u (v :: xs)
        rw [he] at hh
        exact hf (top_le_iff.mp hh)
      intro z hz
      rcases List.mem_cons.mp hz with he | he
      · simpa only [he] using hu
      · exact ih v hv ht z he

namespace Representation

variable {n : ℕ}

theorem restricted_edge_le_block (R : Representation n) (G : Graph (Fin n))
    (S B : Finset (Fin n)) (hB : B ∈ R.blocks) (u v : Fin n) :
    R.restricted G S u v ≤ closure (R.base G) (B ∩ S) u v := by
  have hm : B ∩ S ∈ R.blocks.map (· ∩ S) := List.mem_map.mpr ⟨B, hB, rfl⟩
  have h := closures_le_member (induced (R.base G) S) _ hm u v
  rw [closure_induced (R.base G) S (B ∩ S) Finset.inter_subset_right] at h
  exact h

theorem restricted_subpath_edge (R : Representation n) (G : Graph (Fin n))
    (S B : Finset (Fin n)) (hB : B ∈ R.blocks)
    (pre middle post : List (Fin n)) {u v : Fin n}
    (he : Graph.Endpoints middle u v) (hne : u ≠ v)
    (hmem : ∀ z ∈ middle, z ∈ B ∩ S) :
    R.restricted G S u v ≤ (R.base G).pathCost (pre ++ middle ++ post) := by
  have hu := hmem u (endpoints_mem he).1
  have hv := hmem v (endpoints_mem he).2
  have hdist : (induced (R.base G) (B ∩ S)).dist u v ≤ (R.base G).pathCost middle := by
    have h := Graph.dist_le_pathCost (induced (R.base G) (B ∩ S)) he
    rw [induced_path_cost _ _ middle hmem] at h
    exact h
  have hblock := R.restricted_edge_le_block G S B hB u v
  have hin : u ∈ B ∩ S ∧ v ∈ B ∩ S ∧ u ≠ v := ⟨hu, hv, hne⟩
  simp only [closure, ite_eq_left hin] at hblock
  exact hblock.trans (hdist.trans (Graph.pathCost_segment_le (R.base G) pre middle post))

structure ClosureWitness (R : Representation n) (G : Graph (Fin n)) (u v : Fin n) where
  block : Finset (Fin n)
  member : block ∈ R.blocks
  vertices : List (Fin n)
  endpoints : Graph.Endpoints vertices u v
  inside : ∀ z ∈ vertices, z ∈ block
  weight_eq : (R.base G).pathCost vertices = R.graph G u v

theorem exists_origin (R : Representation n) (G : Graph (Fin n))
    (u v : Fin n) (hf : R.graph G u v ≠ ⊤) :
    R.base G u v = R.graph G u v ∨ Nonempty (ClosureWitness R G u v) := by
  rcases closure_origin (R.base G) R.blocks u v with h | ⟨B, hB, hw⟩
  · exact Or.inl h
  · right
    have hclosure : closure (R.base G) B u v ≠ ⊤ := fun he => hf (hw.symm.trans he)
    have hin : u ∈ B ∧ v ∈ B ∧ u ≠ v := by
      by_contra h
      simp [closure, h] at hclosure
    have hdist : (induced (R.base G) B).dist u v ≠ ⊤ := by
      simpa only [closure, ite_eq_left hin] using hclosure
    obtain ⟨xs, _hn, he, _hlen, hc⟩ := Graph.exists_dist_path (induced (R.base G) B) hdist
    have hu : u ∈ xs := (endpoints_mem he).1
    have hinside : ∀ z ∈ xs, z ∈ B := by
      cases xs with
      | nil => simp at hu
      | cons x xs =>
          have hx : x = u := by simpa [Graph.Endpoints] using he.1
          subst x
          apply induced_path_members (R.base G) B u xs hin.1
          rw [hc]
          exact hdist
    refine ⟨⟨B, hB, xs, he, hinside, ?_⟩⟩
    rw [← induced_path_cost (R.base G) B xs hinside, hc]
    exact (by simpa only [closure, ite_eq_left hin, graph] using hw)

theorem witness_survives (R : Representation n) (G : Graph (Fin n))
    {u v : Fin n} (W : ClosureWitness R G u v) (hne : u ≠ v)
    (S : Finset (Fin n)) (hS : ∀ z ∈ W.vertices, z ∈ S) :
    R.restricted G S u v = R.graph G u v := by
  have hle : R.restricted G S u v ≤ R.graph G u v := by
    have h := R.restricted_subpath_edge G S W.block W.member [] W.vertices []
      W.endpoints hne (fun z hz => Finset.mem_inter.mpr ⟨W.inside z hz, hS z hz⟩)
    simpa only [List.nil_append, List.append_nil, W.weight_eq] using h
  have hge := R.restricted_mono G (S := Finset.univ) (T := S) (Finset.subset_univ S) u v
  rw [restricted_univ] at hge
  exact le_antisymm hle hge

end Representation

end StreamingReachability.Implicit
