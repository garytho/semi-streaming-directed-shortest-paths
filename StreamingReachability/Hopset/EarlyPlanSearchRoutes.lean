module

public import StreamingReachability.Hopset.EarlyPlanRoutes
public import StreamingReachability.Hopset.PartitionSearchRoutes
public import StreamingReachability.Hopset.CoverSearchRoutes

@[expose] public section

namespace StreamingReachability.Hopset.EarlyPlan

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G F : Graph (Fin n)} {s t : Fin n}
    {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {hS : Q.Inside S}
    {D : ℝ} {hshort : (Q.searchWeight A : ℝ) ≤ D}
    {P : Finset (Fin n)} {rho : Fin n → ℝ} {Rmax d : ℝ}

theorem build_search_route (B : EarlyPlan Q A S hS D hshort P rho Rmax d)
    (hA : 0 < A) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (debt : (label : B.Label) →
      Late.ChildPiece R G (type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val) A d → ℕ)
    (child : (label : B.Label) →
      (C : Late.ChildPiece R G (type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val) A d) →
        Late.Route F C.source C.target (A * (C.path.searchWeight A + debt label C))) :
    ∃ T : Late.Route F s t (A * (Q.searchWeight A + ∑ i : B.ChildIndex, debt i.1 (B.piece i))),
      T.hops ≤ B.overhead + ∑ i : B.ChildIndex, (child i.1 (B.piece i)).hops := by
  let cover := type1VertexCover (Q.shortView A S hS D hshort) P rho Rmax
  let localDebt := fun label : B.Label => ((B.parts label).pieces.map (debt label)).sum
  let runs := fun label : B.Label => (B.parts label).assembleSearch hA hF (debt label) (child label)
  have hw (label : B.Label) :
      Graph.Endpoints (runs label).vertices (Q.vertex (cover.interval label.val).1)
          (Q.vertex ((cover.interval label.val).2 - 1)) ∧
        F.pathCost (runs label).vertices ≤
          ((A * (Q.intervalSearch A (cover.interval label.val) + localDebt label) : ℕ) : Distance) := by
    have hb := cover.bounds label.val label.property
    have he := (Q.intervalPath (cover.interval label.val)).endpoints
    have hn := Q.interval_endpoints (cover.interval label.val) hb.1
    have ht := Option.some.inj (he.2.symm.trans hn.2)
    exact ⟨⟨(runs label).endpoints.1, (runs label).endpoints.2.trans (congrArg some ht)⟩, (runs label).cost_le⟩
  obtain ⟨T, hT⟩ := VertexCover.search_route_subtype Q cover A hA hF localDebt
    (fun label => (runs label).vertices) hw
  have hdebt : (∑ i : B.ChildIndex, debt i.1 (B.piece i)) = ∑ label : B.Label, localDebt label := by
    simp only [ChildIndex, piece, Fintype.sum_sigma, localDebt]
    apply Finset.sum_congr rfl
    intro label _
    exact (list_sum_indices (B.parts label).pieces (debt label)).symm
  have hsumDebt : (∑ label : {label // label ∈ cover.labels}, localDebt label) =
      ∑ i : B.ChildIndex, debt i.1 (B.piece i) := hdebt.symm
  let final : Late.Route F s t (A * (Q.searchWeight A + ∑ i : B.ChildIndex, debt i.1 (B.piece i))) :=
    ⟨T.vertices, T.endpoints,
      T.cost_le.trans_eq (congrArg (fun w : ℕ => ((A * (Q.searchWeight A + w) : ℕ) : Distance)) hsumDebt)⟩
  have hr (label : B.Label) :
      (runs label).hops ≤ (B.parts label).boundaries +
        ∑ j : Fin (B.parts label).pieces.length,
          (child label ((B.parts label).pieces.get j)).hops := by
    have h := (B.parts label).assembleSearch_hops hA hF (debt label) (child label)
    have hs := list_sum_indices (B.parts label).pieces (fun C => (child label C).hops)
    exact h.trans_eq (congrArg ((B.parts label).boundaries + ·) hs)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset B.Label)) (fun label _ => hr label)
  rw [Finset.sum_add_distrib] at hs
  have hchildren : (∑ i : B.ChildIndex, (child i.1 (B.piece i)).hops) =
      ∑ label : B.Label, ∑ j : Fin (B.parts label).pieces.length,
        (child label ((B.parts label).pieces.get j)).hops := by
    simp only [ChildIndex, piece, Fintype.sum_sigma]
  refine ⟨final, ?_⟩
  change T.hops ≤ cover.labels.card + B.boundaries + ∑ i : B.ChildIndex, (child i.1 (B.piece i)).hops
  rw [hchildren]
  change T.hops ≤ cover.labels.card + (∑ label : B.Label, (B.parts label).boundaries) +
    (∑ label : B.Label, ∑ j : Fin (B.parts label).pieces.length,
      (child label ((B.parts label).pieces.get j)).hops)
  change T.hops ≤ cover.labels.card + (∑ label : B.Label, (runs label).hops) at hT
  omega

end

end StreamingReachability.Hopset.EarlyPlan
