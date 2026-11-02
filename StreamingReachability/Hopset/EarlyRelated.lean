module

public import StreamingReachability.Hopset.EarlyPlanBounds
public import StreamingReachability.Hopset.PathNeighborhoods
public import StreamingReachability.Hopset.RestrictedDistances
public import StreamingReachability.Early.RelatedMembership

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

def type1Related {V : Type*} [Fintype V] {H : Graph V} {D : ℝ}
    (Q : Early.ShortPath H D) (E P : Finset V) (rho : V → ℝ) (Rmax Rmin : ℝ) :
    ((ℕ × ℕ) ⊕ V) → Finset V
  | .inl I => Early.coreRelated Q E P rho Rmax Rmin I ∪ Early.coreDescRelated Q E P rho Rmax Rmin I
  | .inr p => Early.fringeRelated Q E P rho Rmax Rmin p

theorem mem_type1Related_core {V : Type*} [Fintype V] {H : Graph V} {D : ℝ}
    (Q : Early.ShortPath H D) (E P : Finset V) (rho : V → ℝ) (Rmax Rmin : ℝ) (I : ℕ × ℕ) (w : V) :
    w ∈ type1Related Q E P rho Rmax Rmin (.inl I) ↔
      w ∈ Early.coreRelated Q E P rho Rmax Rmin I ∨
      w ∈ Early.coreDescRelated Q E P rho Rmax Rmin I := by
  unfold type1Related
  exact Finset.mem_union

theorem type1Related_sum {V : Type*} [Fintype V] {H : Graph V} {D : ℝ}
    (Q : Early.ShortPath H D) (E P : Finset V) (rho : V → ℝ) (Rmax Rmin : ℝ)
    (hstop : ¬ Early.stopped Q P Rmax) :
    (∑ label ∈ type1Labels Q P rho Rmax, (type1Related Q E P rho Rmax Rmin label).card) =
      Early.actualRelatedTotal Q E P rho Rmax Rmin := by
  simp only [type1Labels, Finset.sum_disjSum, type1Related, Early.actualRelatedTotal, hstop, ↓reduceIte]

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem type1Related_contains (Q : Late.Path R G s t) (A : ℕ) (S : Finset (Fin n)) (hS : Q.Inside S)
    (D : ℝ) (hshort : (Q.searchWeight A : ℝ) ≤ D) (E P : Finset (Fin n))
    (rho : Fin n → ℝ) (Rmax Rmin radius : ℝ)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax) (hradius : radius ≤ Rmin)
    (label : ((ℕ × ℕ) ⊕ Fin n))
    (hl : label ∈ type1Labels (Q.shortView A S hS D hshort) P rho Rmax)
    (F : Graph (Fin n)) (E' : Finset (Fin n))
    (hF : Implicit.induced F (type1Target (Q.shortView A S hS D hshort) S P rho Rmax label) = F)
    (hmono : ∀ u v, (Late.rounded A (R.restricted G S)) u v ≤ F u v)
    (hEX : E' ⊆ type1Target (Q.shortView A S hS D hshort) S P rho Rmax label)
    (hE : E' ⊆ E) (hP : ∀ w ∈ E', w ∉ P) :
    relatedVertices F (Q.intervalPath (type1Interval (Q.shortView A S hS D hshort) P rho Rmax label)).vertices
        E' radius ⊆
      type1Related (Q.shortView A S hS D hshort) E P rho Rmax Rmin label := by
  classical
  let view := Q.shortView A S hS D hshort
  let H := Late.rounded A (R.restricted G S)
  let X := type1Target view S P rho Rmax label
  let cover := type1VertexCover view P rho Rmax
  have hvertices := type1Target_vertices Q A S hS D hshort P rho Rmax hnb hrho ⟨label, hl⟩
  have hpoint (w v : Fin n) (hw : w ∈ E')
      (hv : v ∈ (Q.intervalPath (cover.interval label)).vertices)
      (hd : Early.Within F w v radius ∨ Early.Within F v w radius) :
      w ∈ type1Related view E P rho Rmax Rmin label := by
    have hb := cover.bounds label hl
    obtain ⟨i, hi, he⟩ := Q.interval_vertices _ hb.1 hb.2 hv
    have he' : view.vertex i = v := he.symm
    have hwX : w ∈ X := hEX hw
    have hvX : v ∈ X := hvertices v hv
    cases label with
    | inl I =>
        let C := Early.coreClass H P rho
          (Early.smoothLabels P (fun p => Early.pivotCut view p (rho p) Rmax) I.1)
        have hXC : ∀ z ∈ X, z ∈ C := by
          intro z hz
          exact ((coreChild_mem H S P rho _ z).mp hz).2
        have hwC : w ∈ C := hXC w hwX
        have hiC : view.vertex i ∈ C := by rw [he']; exact hXC v hvX
        rcases hd with hd | hd
        · apply (mem_type1Related_core view E P rho Rmax Rmin I w).mpr
          left
          apply (Early.mem_coreRelated view E P rho Rmax Rmin I w).mpr
          refine ⟨hE hw, hP w hw, i, hi, hwC, hiC, ?_⟩
          have h := Geometry.within_restrict_of_induced H F X C hXC hF hmono w v hwX hvX Rmin
            (Early.within_mono hd hradius)
          simpa only [he'] using h
        · apply (mem_type1Related_core view E P rho Rmax Rmin I w).mpr
          right
          apply (Early.mem_coreDescRelated view E P rho Rmax Rmin I w).mpr
          refine ⟨hE hw, hP w hw, i, hi, hwC, hiC, ?_⟩
          have h := Geometry.within_restrict_of_induced H F X C hXC hF hmono v w hvX hwX Rmin
            (Early.within_mono hd hradius)
          simpa only [he'] using h
    | inr p =>
        let C : Set (Fin n) := ↑(Early.fringe H p (rho p) D)
        have hXC : ∀ z ∈ X, z ∈ C := by
          intro z hz
          exact (Finset.mem_inter.mp hz).2
        have hwC : w ∈ C := hXC w hwX
        have hiC : view.vertex i ∈ C := by rw [he']; exact hXC v hvX
        apply (Early.mem_fringeRelated view E P rho Rmax Rmin p w).mpr
        refine ⟨hE hw, hP w hw, i, hi, hwC, hiC, ?_⟩
        rcases hd with hd | hd
        · left
          have h := Geometry.within_restrict_of_induced H F X C hXC hF hmono w v hwX hvX Rmin
            (Early.within_mono hd hradius)
          simpa only [he'] using h
        · right
          have h := Geometry.within_restrict_of_induced H F X C hXC hF hmono v w hvX hwX Rmin
            (Early.within_mono hd hradius)
          simpa only [he'] using h
  intro w hw
  obtain ⟨hwE, hw⟩ := (mem_relatedVertices _ _ _ _ _).mp hw
  rcases hw with ⟨v, hv, hd⟩ | ⟨v, hv, hd⟩
  · exact hpoint w v hwE hv (Or.inl hd)
  · exact hpoint w v hwE hv (Or.inr hd)

end

end StreamingReachability.Hopset
