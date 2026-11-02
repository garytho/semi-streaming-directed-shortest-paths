module

public import StreamingReachability.Hopset.EarlyPlans

@[expose] public section

namespace StreamingReachability

open scoped Classical BigOperators

noncomputable section

namespace Late.Partition

theorem pieces_search_sum_le {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)}
    {X : Finset (Fin n)} {A : ℕ} {d : ℝ} {s t : Fin n} {Q : Path R G s t}
    (B : Partition R G X A d Q) :
    (B.pieces.map fun C => C.path.searchWeight A).sum ≤ Q.searchWeight A := by
  induction B with
  | one => simp [pieces]
  | cut Pre e Tail hinside hshort rest ih =>
      simp only [pieces, List.map_cons, List.sum_cons, Path.searchWeight_append, Path.searchWeight]
      omega

end Late.Partition

namespace Hopset.EarlyPlan

variable {n : ℕ} {R : Implicit.Representation n} {G F : Graph (Fin n)} {s t : Fin n}
    {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {hS : Q.Inside S}
    {D : ℝ} {hshort : (Q.searchWeight A : ℝ) ≤ D}
    {P : Finset (Fin n)} {rho : Fin n → ℝ} {Rmax d : ℝ}

theorem piece_weight_sum (B : EarlyPlan Q A S hS D hshort P rho Rmax d) :
    (∑ i : B.ChildIndex, (B.piece i).path.searchWeight A) ≤ Q.searchWeight A := by
  let C := type1VertexCover (Q.shortView A S hS D hshort) P rho Rmax
  calc
    _ = ∑ label : B.Label,
        ((B.parts label).pieces.map fun piece => piece.path.searchWeight A).sum := by
      simp only [ChildIndex, piece, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro label hl
      exact (list_sum_indices (B.parts label).pieces (fun piece => piece.path.searchWeight A)).symm
    _ ≤ ∑ label : B.Label, Q.intervalSearch A (C.interval label.val) := by
      apply Finset.sum_le_sum
      intro label hl
      exact (B.parts label).pieces_search_sum_le
    _ = ∑ label ∈ C.labels, Q.intervalSearch A (C.interval label) := by
      change (∑ label : {label // label ∈ C.labels}, Q.intervalSearch A (C.interval label.val)) = _
      exact Finset.sum_coe_sort C.labels (fun label => Q.intervalSearch A (C.interval label))
    _ ≤ _ := intervalSearch_sum_le Q C A

theorem build_route (B : EarlyPlan Q A S hS D hshort P rho Rmax d)
    (hF : ∀ u v, F u v ≤ R.graph G u v)
    (child : (label : B.Label) →
      (C : Late.ChildPiece R G
        (type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val) A d) →
        Late.Route F C.source C.target C.path.micro) :
    ∃ T : Late.Route F s t Q.micro,
      T.hops ≤ B.overhead + ∑ i : B.ChildIndex, (child i.1 (B.piece i)).hops := by
  let C := type1VertexCover (Q.shortView A S hS D hshort) P rho Rmax
  let runs := fun label : B.Label => (B.parts label).assemble hF (child label)
  have hw (label : B.Label) :
      Graph.Endpoints (runs label).vertices (Q.vertex (C.interval label.val).1)
          (Q.vertex ((C.interval label.val).2 - 1)) ∧
        F.pathCost (runs label).vertices ≤ (Q.intervalMicro (C.interval label.val) : Distance) := by
    have hb := C.bounds label.val label.property
    have he := (Q.intervalPath (C.interval label.val)).endpoints
    have hn := Q.interval_endpoints (C.interval label.val) hb.1
    have ht := Option.some.inj (he.2.symm.trans hn.2)
    exact ⟨⟨(runs label).endpoints.1, (runs label).endpoints.2.trans (congrArg some ht)⟩,
      (runs label).cost_le⟩
  obtain ⟨T, hT⟩ := VertexCover.route_subtype Q C hF (fun label => (runs label).vertices) hw
  have hr (label : B.Label) :
      (runs label).hops ≤ (B.parts label).boundaries +
        ∑ j : Fin (B.parts label).pieces.length,
          (child label ((B.parts label).pieces.get j)).hops := by
    have h := (B.parts label).assemble_hops hF (child label)
    rw [list_sum_indices] at h
    exact h
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset B.Label)) (fun label _ => hr label)
  rw [Finset.sum_add_distrib] at hs
  have hchildren :
      (∑ i : B.ChildIndex, (child i.1 (B.piece i)).hops) =
        ∑ label : B.Label, ∑ j : Fin (B.parts label).pieces.length,
          (child label ((B.parts label).pieces.get j)).hops := by
    simp only [ChildIndex, piece, Fintype.sum_sigma]
  refine ⟨T, ?_⟩
  change T.hops ≤ (type1Labels (Q.shortView A S hS D hshort) P rho Rmax).card +
    B.boundaries + ∑ i : B.ChildIndex, (child i.1 (B.piece i)).hops
  rw [hchildren]
  change T.hops ≤ C.labels.card + (∑ label : B.Label, (B.parts label).boundaries) +
    (∑ label : B.Label, ∑ j : Fin (B.parts label).pieces.length,
      (child label ((B.parts label).pieces.get j)).hops)
  change T.hops ≤ C.labels.card + (∑ label : B.Label, (runs label).hops) at hT
  omega

end Hopset.EarlyPlan

end

end StreamingReachability
