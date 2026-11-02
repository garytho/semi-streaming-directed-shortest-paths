module

public import StreamingSSSP.Hopset.EarlyPlanRoutes
public import StreamingSSSP.Hopset.PartitionFacts
public import StreamingSSSP.Late.Plan

@[expose] public section

namespace StreamingSSSP.Hopset.EarlyPlan

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}
    {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {hS : Q.Inside S}
    {D : ℝ} {hshort : (Q.searchWeight A : ℝ) ≤ D}
    {P : Finset (Fin n)} {rho : Fin n → ℝ} {Rmax d : ℝ}

theorem type3_le (B : EarlyPlan Q A S hS D hshort P rho Rmax d)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax) :
    B.type3 ≤ Late.type3Count Q (Late.rounded A (R.restricted G S)) S P rho D Rmax := by
  let view := Q.shortView A S hS D hshort
  let C := type1VertexCover view P rho Rmax
  let w := fun e : Late.Path.PackedEdge R G =>
    if Late.Type3 (Late.rounded A (R.restricted G S)) S P rho D Rmax Q.vertices e.2.2 then 1 else 0
  have hlabel (label : B.Label) :
      (Q.intervalPath (C.interval label.val)).badEdges (type1Target view S P rho Rmax label.val) ≤
        (((Q.intervalPath (C.interval label.val)).edges).map w).sum := by
    apply List.sum_le_sum
    intro e he
    by_cases h : e.2.2.Inside (type1Target view S P rho Rmax label.val)
    · simp [h]
    · have hends := Late.edge_endpoints_vertices (Q.intervalPath (C.interval label.val)) he
      have hv := type1Target_vertices Q A S hS D hshort P rho Rmax hnb hrho label
      have hcut : Late.Type3 (Late.rounded A (R.restricted G S)) S P rho D Rmax Q.vertices e.2.2 :=
        ⟨_, type1Target_admissible view S P rho Rmax hnb label.val label.property,
          hv _ hends.1, hv _ hends.2, h⟩
      simp [h, w, hcut]
  calc
    B.type3 ≤ ∑ label : B.Label, ((Q.intervalPath (C.interval label.val)).edges.map w).sum :=
      Finset.sum_le_sum (fun label _ => hlabel label)
    _ = ∑ label ∈ C.labels, ((Q.intervalPath (C.interval label)).edges.map w).sum := by
      change (∑ label : {label // label ∈ C.labels},
        ((Q.intervalPath (C.interval label.val)).edges.map w).sum) = _
      exact Finset.sum_coe_sort C.labels (fun label => ((Q.intervalPath (C.interval label)).edges.map w).sum)
    _ ≤ (Q.edges.map w).sum := intervalEdges_sum_le Q C w
    _ = _ := rfl

theorem type2_zero (B : EarlyPlan Q A S hS D hshort P rho Rmax D) : B.type2 = 0 := by
  apply Finset.sum_eq_zero
  intro label _
  apply (B.parts label).type2_zero_of_short (B.greedy label)
  let I := type1Interval (Q.shortView A S hS D hshort) P rho Rmax label.val
  have hweight : (Q.intervalPath I).searchWeight A ≤ Q.searchWeight A :=
    ((Q.suffix I.1).searchWeight_take_le A (I.2 - 1 - I.1)).trans (Q.searchWeight_suffix_le A I.1)
  exact (Nat.cast_le.mpr hweight).trans hshort

theorem child_count_le (B : EarlyPlan Q A S hS D hshort P rho Rmax D)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax) :
    Fintype.card B.ChildIndex ≤
      Early.pieceNumber (Q.shortView A S hS D hshort) P rho Rmax +
        Late.type3Count Q (Late.rounded A (R.restricted G S)) S P rho D Rmax := by
  rw [B.child_count, B.boundary_types, B.type2_zero, zero_add]
  have h3 := B.type3_le hnb hrho
  have hstop : ¬ Early.stopped (Q.shortView A S hS D hshort) P Rmax := by
    rintro ⟨p, hp, hb⟩
    exact hnb p hp hb
  have hlabels : (type1Labels (Q.shortView A S hS D hshort) P rho Rmax).card =
      Early.pieceNumber (Q.shortView A S hS D hshort) P rho Rmax := by
    simp [type1Labels, Early.pieceNumber, hstop]
  rw [hlabels]
  exact Nat.add_le_add_left h3 _

end

end StreamingSSSP.Hopset.EarlyPlan
