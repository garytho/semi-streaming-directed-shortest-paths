module

public import StreamingReachability.Hopset.EarlyRelated
public import StreamingReachability.Late.Protocol

@[expose] public section

namespace StreamingReachability.Hopset.EarlyPlan

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}
    {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {hS : Q.Inside S}
    {D : ℝ} {hshort : (Q.searchWeight A : ℝ) ≤ D}
    {P : Finset (Fin n)} {rho : Fin n → ℝ} {Rmax d : ℝ}

def target (B : EarlyPlan Q A S hS D hshort P rho Rmax d) (label : B.Label) : Finset (Fin n) :=
  type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val

def related (B : EarlyPlan Q A S hS D hshort P rho Rmax d)
    (E' : B.Label → Finset (Fin n)) (radius : ℝ) : ℕ :=
  ∑ i : B.ChildIndex,
    (relatedVertices (Late.rounded A (R.restricted G (B.target i.1)))
      (B.piece i).path.vertices (E' i.1) radius).card

theorem related_le (B : EarlyPlan Q A S hS D hshort P rho Rmax d) (hA : 0 < A)
    (E : Finset (Fin n)) (E' : B.Label → Finset (Fin n)) (Rmin radius : ℝ) (b : ℕ)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax) (hradius : radius ≤ Rmin)
    (hbudget : (Q.searchWeight A : ℝ) + radius ≤ Rmax)
    (hin : ∀ v, (Early.searchIn (Late.rounded A (R.restricted G S)) v Rmax).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Late.rounded A (R.restricted G S)) v Rmax).card ≤ b)
    (hEX : ∀ label, E' label ⊆ B.target label) (hE : ∀ label, E' label ⊆ E)
    (hP : ∀ label w, w ∈ E' label → w ∉ P) :
    B.related E' radius ≤
      Early.actualRelatedTotal (Q.shortView A S hS D hshort) E P rho Rmax Rmin +
        2 * b * B.boundaries := by
  classical
  let view := Q.shortView A S hS D hshort
  let H := Late.rounded A (R.restricted G S)
  let cover := type1VertexCover view P rho Rmax
  let F := fun label : B.Label => Late.rounded A (R.restricted G (B.target label))
  have hmono (label : B.Label) : ∀ u v, H u v ≤ F label u v := by
    intro u v
    exact Core.roundDistance_mono hA
      (R.restricted_mono G (type1Target_subset view S P rho Rmax label.val) u v)
  have hlabel (label : B.Label) :
      ((B.parts label).pieces.map fun C => (relatedVertices (F label) C.path.vertices (E' label) radius).card).sum ≤
        (type1Related view E P rho Rmax Rmin label.val).card + 2 * b * (B.parts label).boundaries := by
    have hb := cover.bounds label.val label.property
    have hc : ∀ C ∈ (B.parts label).pieces,
        (relatedVertices (F label) C.path.vertices (E' label) radius).card ≤ 2 * b := by
      intro C hC
      have hvertices : ∀ v ∈ C.path.vertices, v ∈ Q.vertices := by
        intro v hv
        have hi := ((B.parts label).piece_vertices_infix C hC).sublist.subset hv
        exact (Q.interval_vertices_infix (cover.interval label.val) hb.1 hb.2).sublist.subset hi
      apply (Finset.card_le_card
        (relatedVertices_mono H (F label) C.path.vertices Q.vertices (E' label) (E' label) radius radius
          (Graph.dist_mono (hmono label)) hvertices (fun _ h => h) le_rfl)).trans
      exact relatedVertices_card_le Q A hA S hS (E' label) radius Rmax b hbudget (hin t) (hout s)
    have hs := partition_related_total_le (B.parts label) (F label) (E' label) radius (2 * b) hc
    have hbase := Finset.card_le_card
      (type1Related_contains Q A S hS D hshort E P rho Rmax Rmin radius hnb hrho hradius label.val
        label.property (F label) (E' label) (Late.search_induced R G (B.target label) A)
        (hmono label) (hEX label) (hE label) (hP label))
    exact hs.trans (Nat.add_le_add_right hbase _)
  have hstop : ¬ Early.stopped view P Rmax := by
    rintro ⟨p, hp, hb⟩
    exact hnb p hp hb
  have hbase :
      (∑ label : B.Label, (type1Related view E P rho Rmax Rmin label.val).card) =
        Early.actualRelatedTotal view E P rho Rmax Rmin := by
    calc
      _ = ∑ label ∈ cover.labels, (type1Related view E P rho Rmax Rmin label).card := by
        change (∑ label : {label // label ∈ cover.labels},
          (type1Related view E P rho Rmax Rmin label.val).card) = _
        exact Finset.sum_coe_sort cover.labels (fun label => (type1Related view E P rho Rmax Rmin label).card)
      _ = _ := type1Related_sum view E P rho Rmax Rmin hstop
  calc
    _ = ∑ label : B.Label,
        ((B.parts label).pieces.map fun C => (relatedVertices (F label) C.path.vertices (E' label) radius).card).sum := by
      simp only [related, ChildIndex, piece, Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro label _
      exact (list_sum_indices (B.parts label).pieces
        (fun C => (relatedVertices (F label) C.path.vertices (E' label) radius).card)).symm
    _ ≤ ∑ label : B.Label,
        ((type1Related view E P rho Rmax Rmin label.val).card + 2 * b * (B.parts label).boundaries) :=
      Finset.sum_le_sum (fun label _ => hlabel label)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbase]
      rfl

theorem related_type3_le (B : EarlyPlan Q A S hS D hshort P rho Rmax D) (hA : 0 < A)
    (E : Finset (Fin n)) (E' : B.Label → Finset (Fin n)) (Rmin radius : ℝ) (b : ℕ)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax) (hradius : radius ≤ Rmin)
    (hbudget : (Q.searchWeight A : ℝ) + radius ≤ Rmax)
    (hin : ∀ v, (Early.searchIn (Late.rounded A (R.restricted G S)) v Rmax).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Late.rounded A (R.restricted G S)) v Rmax).card ≤ b)
    (hEX : ∀ label, E' label ⊆ B.target label) (hE : ∀ label, E' label ⊆ E)
    (hP : ∀ label w, w ∈ E' label → w ∉ P) :
    B.related E' radius ≤
      Early.actualRelatedTotal (Q.shortView A S hS D hshort) E P rho Rmax Rmin +
        2 * b * Late.type3Count Q (Late.rounded A (R.restricted G S)) S P rho D Rmax := by
  have hs := B.related_le hA E E' Rmin radius b hnb hrho hradius hbudget hin hout hEX hE hP
  rw [B.boundary_types, B.type2_zero, zero_add] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (B.type3_le hnb hrho)) _)

end

end StreamingReachability.Hopset.EarlyPlan
