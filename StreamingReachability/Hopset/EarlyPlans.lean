module

public import StreamingReachability.Hopset.CoverRoutes
public import StreamingReachability.Hopset.Type1Routing
public import StreamingReachability.Hopset.IntervalWeights

@[expose] public section

namespace StreamingReachability

open scoped Classical BigOperators

noncomputable section

namespace Late.Path

def shortView {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}
    (Q : Path R G s t) (A : ℕ) (S : Finset (Fin n)) (hS : Q.Inside S)
    (D : ℝ) (hshort : (Q.searchWeight A : ℝ) ≤ D) :
    Early.ShortPath (rounded A (R.restricted G S)) D :=
  ⟨Q.vertices, Graph.endpoints_nonempty Q.endpoints, Q.searchWeight A, Q.vertices_cost A hS, hshort⟩

end Late.Path

namespace Hopset

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

structure EarlyPlan (Q : Late.Path R G s t) (A : ℕ) (S : Finset (Fin n)) (hS : Q.Inside S)
    (D : ℝ) (hshort : (Q.searchWeight A : ℝ) ≤ D)
    (P : Finset (Fin n)) (rho : Fin n → ℝ) (Rmax d : ℝ) where
  parts : (label : {label // label ∈ type1Labels (Q.shortView A S hS D hshort) P rho Rmax}) →
    Late.Partition R G (type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val) A d
      (Q.intervalPath (type1Interval (Q.shortView A S hS D hshort) P rho Rmax label.val))
  greedy : ∀ label, (parts label).Greedy

theorem type1Target_vertices (Q : Late.Path R G s t) (A : ℕ) (S : Finset (Fin n)) (hS : Q.Inside S)
    (D : ℝ) (hshort : (Q.searchWeight A : ℝ) ≤ D)
    (P : Finset (Fin n)) (rho : Fin n → ℝ) (Rmax : ℝ)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax)
    (label : {label // label ∈ type1Labels (Q.shortView A S hS D hshort) P rho Rmax}) :
    ∀ v ∈ (Q.intervalPath (type1Interval (Q.shortView A S hS D hshort) P rho Rmax label.val)).vertices,
      v ∈ type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val := by
  intro v hv
  let view := Q.shortView A S hS D hshort
  let C := type1VertexCover view P rho Rmax
  have hb := C.bounds label.val label.property
  obtain ⟨i, hi, he⟩ := Q.interval_vertices _ hb.1 hb.2 hv
  have hinside := type1Target_contains view S P rho Rmax
    (fun i => Q.vertices_inside hS _ (List.get_mem Q.vertices i)) hnb hrho
    label.val label.property i hi
  exact he.symm ▸ hinside

theorem exists_early_plan (Q : Late.Path R G s t) (A : ℕ) (S : Finset (Fin n)) (hS : Q.Inside S)
    (D : ℝ) (hshort : (Q.searchWeight A : ℝ) ≤ D)
    (P : Finset (Fin n)) (rho : Fin n → ℝ) (Rmax d : ℝ) (hd : 0 ≤ d)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge (Q.shortView A S hS D hshort) p Rmax)
    (hrho : ∀ p ∈ P, rho p ≤ Rmax) :
    Nonempty (EarlyPlan Q A S hS D hshort P rho Rmax d) := by
  let view := Q.shortView A S hS D hshort
  have hvertices (label : {label // label ∈ type1Labels view P rho Rmax}) :
      ∀ v ∈ (Q.intervalPath (type1Interval view P rho Rmax label.val)).vertices,
        v ∈ type1Target view S P rho Rmax label.val :=
    type1Target_vertices Q A S hS D hshort P rho Rmax hnb hrho label
  let parts := fun label : {label // label ∈ type1Labels view P rho Rmax} =>
    Classical.choose (Late.Partition.exists_greedy
      (Q.intervalPath (type1Interval view P rho Rmax label.val))
      (type1Target view S P rho Rmax label.val) A d hd (hvertices label))
  exact ⟨⟨parts, fun label => Classical.choose_spec (Late.Partition.exists_greedy
    (Q.intervalPath (type1Interval view P rho Rmax label.val))
    (type1Target view S P rho Rmax label.val) A d hd (hvertices label))⟩⟩

namespace EarlyPlan

variable {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {hS : Q.Inside S}
    {D : ℝ} {hshort : (Q.searchWeight A : ℝ) ≤ D}
    {P : Finset (Fin n)} {rho : Fin n → ℝ} {Rmax d : ℝ}

abbrev Label (_B : EarlyPlan Q A S hS D hshort P rho Rmax d) :=
  {label // label ∈ type1Labels (Q.shortView A S hS D hshort) P rho Rmax}

abbrev ChildIndex (B : EarlyPlan Q A S hS D hshort P rho Rmax d) :=
  Sigma fun label : B.Label => Fin (B.parts label).pieces.length

def piece (B : EarlyPlan Q A S hS D hshort P rho Rmax d) (i : B.ChildIndex) :
    Late.ChildPiece R G (type1Target (Q.shortView A S hS D hshort) S P rho Rmax i.1.val) A d :=
  (B.parts i.1).pieces.get i.2

def boundaries (B : EarlyPlan Q A S hS D hshort P rho Rmax d) : ℕ :=
  ∑ label : B.Label, (B.parts label).boundaries

def type2 (B : EarlyPlan Q A S hS D hshort P rho Rmax d) : ℕ :=
  ∑ label : B.Label, (B.parts label).type2

def type3 (B : EarlyPlan Q A S hS D hshort P rho Rmax d) : ℕ :=
  ∑ label : B.Label,
    (Q.intervalPath (type1Interval (Q.shortView A S hS D hshort) P rho Rmax label.val)).badEdges
      (type1Target (Q.shortView A S hS D hshort) S P rho Rmax label.val)

def overhead (B : EarlyPlan Q A S hS D hshort P rho Rmax d) : ℕ :=
  (type1Labels (Q.shortView A S hS D hshort) P rho Rmax).card + B.boundaries

theorem child_count (B : EarlyPlan Q A S hS D hshort P rho Rmax d) :
    Fintype.card B.ChildIndex =
      (type1Labels (Q.shortView A S hS D hshort) P rho Rmax).card + B.boundaries := by
  simp only [ChildIndex, Fintype.card_sigma, Fintype.card_fin]
  simp_rw [Late.Partition.piece_count]
  rw [Finset.sum_add_distrib]
  simp only [boundaries, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, Nat.cast_id, mul_one]
  omega

theorem boundary_types (B : EarlyPlan Q A S hS D hshort P rho Rmax d) :
    B.boundaries = B.type2 + B.type3 := by
  simp only [boundaries, type2, type3]
  simp_rw [Late.Partition.boundary_count]
  rw [Finset.sum_add_distrib]

theorem type2_credit (B : EarlyPlan Q A S hS D hshort P rho Rmax d) (hd : 0 ≤ d) :
    (B.type2 : ℝ) * d ≤ Q.searchWeight A := by
  let C := type1VertexCover (Q.shortView A S hS D hshort) P rho Rmax
  have hc : ∀ label : B.Label, ((B.parts label).type2 : ℝ) * d ≤
      ((Q.intervalPath (C.interval label.val)).searchWeight A : ℝ) := by
    intro label
    have h := (B.parts label).type2_credit (B.greedy label) hd
    change ((B.parts label).type2 : ℝ) * d + (B.parts label).firstWeight ≤
      ((Q.intervalPath (C.interval label.val)).searchWeight A : ℝ) at h
    have hp : (0 : ℝ) ≤ (B.parts label).firstWeight := Nat.cast_nonneg _
    linarith
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset B.Label)) (fun label _ => hc label)
  have hw := intervalSearch_sum_le Q C A
  have hwR : ((∑ label : B.Label, (Q.intervalPath (C.interval label.val)).searchWeight A : ℕ) : ℝ) ≤
      (Q.searchWeight A : ℝ) := by
    have hsum := Finset.sum_coe_sort C.labels (fun label => Q.intervalSearch A (C.interval label))
    have hN : (∑ label : B.Label, Q.intervalSearch A (C.interval label.val)) ≤ Q.searchWeight A := by
      change (∑ label : {label // label ∈ C.labels}, Q.intervalSearch A (C.interval label.val)) ≤ _
      rw [hsum]
      exact hw
    change (∑ label : B.Label, (Q.intervalPath (C.interval label.val)).searchWeight A) ≤ _ at hN
    exact_mod_cast hN
  change (∑ label : B.Label, ((B.parts label).type2 : ℝ) * d) ≤ _ at hs
  simp only [← Finset.sum_mul, ← Nat.cast_sum] at hs
  exact hs.trans hwR

end EarlyPlan

end Hopset

end

end StreamingReachability
