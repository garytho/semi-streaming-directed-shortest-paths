module

public import StreamingReachability.Late.Peeling

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t : Fin n}

theorem edge_endpoints_vertices (Q : Path R G s t) {e : Path.PackedEdge R G}
    (he : e ∈ Q.edges) : e.1 ∈ Q.vertices ∧ e.2.1 ∈ Q.vertices := by
  obtain ⟨Pre, Post, hQ⟩ := Q.edge_decompose he
  rw [hQ]
  constructor
  · exact Pre.mem_vertices_append_right (.cons e.2.2 Post) (by simp [Path.vertices])
  · exact Pre.mem_vertices_append_right (.cons e.2.2 Post)
      (List.mem_cons_of_mem _ (endpoints_mem Post.endpoints).1)

theorem middle_badEdges_le (Q : Path R G s t) (H : Graph (Fin n))
    (S P : Finset (Fin n)) (rho : Fin n → ℝ) (D Rmax : ℝ)
    {a b : Fin n} (T : Path R G a b)
    (hsub : T.edges.Sublist Q.edges)
    (hX : ∀ z ∈ T.vertices, z ∈ emptyChild H S P rho) :
    T.badEdges (emptyChild H S P rho) ≤ type3Count Q H S P rho D Rmax := by
  let X := emptyChild H S P rho
  let f := fun e : Path.PackedEdge R G =>
    if Type3 H S P rho D Rmax Q.vertices e.2.2 then 1 else 0
  have hpoint : T.badEdges X ≤ (T.edges.map f).sum := by
    apply List.sum_le_sum
    intro e he
    by_cases h : e.2.2.Inside X
    · simp [h, f]
    · have hends := edge_endpoints_vertices T he
      have hcut : Type3 H S P rho D Rmax Q.vertices e.2.2 := by
        refine ⟨X, Or.inl ⟨(∅, ∅), emptyChild_eq_core H S P rho⟩,
          hX _ hends.1, hX _ hends.2, h⟩
      simp [h, f, hcut]
  exact hpoint.trans ((hsub.map f).sum_le_sum (by intro a _; exact Nat.zero_le _))

/-- A plan is an output of the proved peeling and greedy split, fixed before
future choices. Its builder concatenates real routes in any later supergraph. -/
structure Plan (R : Representation n) (G : Graph (Fin n)) (F₀ : Graph (Fin n))
    (X : Finset (Fin n)) (A : ℕ) (d : ℝ) {s t : Fin n} (Q : Path R G s t) where
  pieces : List (ChildPiece R G X A d)
  overhead : ℕ
  build : (F : Graph (Fin n)) → (∀ u v, F u v ≤ F₀ u v) →
    ((C : ChildPiece R G X A d) → Route F C.source C.target C.path.micro) →
    Route F s t Q.micro
  hops : ∀ (F : Graph (Fin n)) (hF : ∀ u v, F u v ≤ F₀ u v)
      (child : (C : ChildPiece R G X A d) → Route F C.source C.target C.path.micro),
    (build F hF child).hops ≤ overhead + (pieces.map fun C => (child C).hops).sum

/-- The plan construction works for any comparison radius in the boundary
charge. Core cuts do not use a no-bridge hypothesis. -/
theorem exists_plan_at (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S P : Finset (Fin n)) (hS : Q.Inside S) (rho : Fin n → ℝ) (D Rmax : ℝ)
    (hD : 0 < D) (hshort : (Q.searchWeight A : ℝ) ≤ D)
    (F₀ : Graph (Fin n)) (hF₀ : ∀ u v, F₀ u v ≤ R.graph G u v)
    (hblocks : ∀ p ∈ P, ∀ u v, F₀ u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p (rho p) D) u v) :
    ∃ B : Plan R G F₀ (emptyChild (rounded A (R.restricted G S)) S P rho) A (D / 4) Q,
      B.overhead ≤ 8 + type3Count Q (rounded A (R.restricted G S)) S P rho D Rmax ∧
      B.pieces.length ≤ 5 + type3Count Q (rounded A (R.restricted G S)) S P rho D Rmax := by
  let H := rounded A (R.restricted G S)
  let X := emptyChild H S P rho
  have hp := local_peeling Q A hA S P hS rho D hshort F₀ hF₀ hblocks
  unfold PeelResult at hp
  rcases hp with hdone | hframe
  · obtain ⟨T, hT⟩ := hdone
    let B : Plan R G F₀ X A (D / 4) Q := {
      pieces := []
      overhead := 3
      build := fun F hF _ => T.mono hF
      hops := by
        intro F hF child
        simpa using hT }
    exact ⟨B, by dsimp [B]; omega, by dsimp [B]; simp⟩
  · obtain ⟨frame⟩ := hframe
    obtain ⟨part, hpart⟩ := Partition.exists_greedy frame.middle X A (D / 4)
      (by positivity) frame.vertices_inside
    have hcounts := part.late_counts hpart (by positivity : 0 < D / 4)
      (by nlinarith [frame.short])
    have hbad := middle_badEdges_le Q H S P rho D Rmax frame.middle
      frame.edges_sublist frame.vertices_inside
    let B : Plan R G F₀ X A (D / 4) Q := {
      pieces := part.pieces
      overhead := 4 + part.boundaries
      build := fun F hF child =>
        (((frame.left.mono hF).append
          (part.assemble (fun u v => (hF u v).trans (hF₀ u v)) child)).append
          (frame.right.mono hF)).weaken frame.budget
      hops := by
        intro F hF child
        have hmid := part.assemble_hops (fun u v => (hF u v).trans (hF₀ u v)) child
        have hleft := (frame.left.mono hF).hops_append
          (part.assemble (fun u v => (hF u v).trans (hF₀ u v)) child)
        have hright := ((frame.left.mono hF).append
          (part.assemble (fun u v => (hF u v).trans (hF₀ u v)) child)).hops_append
          (frame.right.mono hF)
        simp only [Route.hops_mono] at hleft hright
        simp only [Route.hops_weaken]
        have hframe := frame.hops
        omega }
    dsimp only [X, H] at hcounts hbad
    exact ⟨B, by dsimp only [B, X, H]; omega, by dsimp only [B, X, H]; omega⟩

end

end StreamingReachability.Late
