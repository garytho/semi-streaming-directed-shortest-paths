module

public import StreamingSSSP.Hopset.Type1Cover
public import StreamingSSSP.Late.Boundary

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ} {G : Graph (Fin n)} {D : ℝ}

namespace Geometry

theorem coreChild_member (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ)
    (L : Finset (Fin n) × Finset (Fin n)) (v : Fin n)
    (hvS : v ∈ S) (hvC : v ∈ Early.coreClass G P rho L) :
    Late.coreChild G S P rho L ∈ core G S P rho := by
  let key := labels G P rho v
  have hk : key ∈ groupKeys S (fun w => decide (Early.remaining G P rho w)) (labels G P rho) :=
    (groupKeys_mem S _ _ key).mpr ⟨v, hvS, by simpa only [decide_eq_true_eq] using hvC.1, rfl⟩
  apply List.mem_map.mpr
  refine ⟨key, hk, ?_⟩
  ext w
  have hl : labels G P rho w = key ↔ Early.labels G P rho w = L := by
    change labels G P rho w = labels G P rho v ↔ _
    rw [labels_equal_iff, hvC.2]
  rw [Finset.mem_filter, coreChild_mem]
  simp only [decide_eq_true_eq, hl]

end Geometry

def type1Target (Q : Early.ShortPath G D) (S P : Finset (Fin n)) (rho : Fin n → ℝ) (R : ℝ) :
    ((ℕ × ℕ) ⊕ Fin n) → Finset (Fin n)
  | .inl I => Late.coreChild G S P rho
      (Early.smoothLabels P (fun p => Early.pivotCut Q p (rho p) R) I.1)
  | .inr p => S ∩ Early.fringe G p (rho p) D

theorem type1Target_subset (Q : Early.ShortPath G D) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (R : ℝ) (label : (ℕ × ℕ) ⊕ Fin n) :
    type1Target Q S P rho R label ⊆ S := by
  cases label with
  | inl I => exact Finset.filter_subset _ _
  | inr p => exact Finset.inter_subset_left

theorem type1Target_contains (Q : Early.ShortPath G D) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (R : ℝ)
    (hS : ∀ i : Fin Q.size, Q.vertex i ∈ S)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge Q p R) (hrho : ∀ p ∈ P, rho p ≤ R)
    (label : (ℕ × ℕ) ⊕ Fin n) (hl : label ∈ type1Labels Q P rho R)
    (i : Fin Q.size) (hi : Early.Cells.Contains (type1Interval Q P rho R label) i.val) :
    Q.vertex i ∈ type1Target Q S P rho R label := by
  cases label with
  | inl I =>
      have hI : I ∈ Early.corePieces Q P rho R := by simpa [type1Labels] using hl
      exact Finset.mem_filter.mpr ⟨hS i, Early.core_piece_contained Q P rho R hnb hrho hI hi⟩
  | inr p =>
      have hp : p ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using hl
      have hminus : ∀ p ∈ P, rho p - D ≤ R := by
        intro p hp
        have hD := Q.scale_nonneg
        linarith [hrho p hp]
      exact Finset.mem_inter.mpr ⟨hS i, Early.grouped_fringe_contained Q P rho R hnb hminus hp hi⟩

theorem noBridge_list (Q : Early.ShortPath G D) (p : Fin n) (R : ℝ)
    (hnb : ¬ Early.Bridge Q p R) : Late.NoBridge G Q.vertices p R := by
  rintro ⟨⟨u, hu, hout⟩, ⟨v, hv, hin⟩⟩
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hu
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  exact hnb ⟨⟨i, by simpa only [Early.ShortPath.vertex, hi] using hout⟩,
    j, by simpa only [Early.ShortPath.vertex, hj] using hin⟩

theorem type1Target_admissible (Q : Early.ShortPath G D) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (R : ℝ) (hnb : ∀ p ∈ P, ¬ Early.Bridge Q p R)
    (label : (ℕ × ℕ) ⊕ Fin n) (hl : label ∈ type1Labels Q P rho R) :
    Late.AdmissibleChild G S P rho D R Q.vertices (type1Target Q S P rho R label) := by
  cases label with
  | inl I => exact Or.inl ⟨_, rfl⟩
  | inr p =>
      have hp : p ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using hl
      have hpP : p ∈ P := type1_fringe_pivot Q P rho R hp
      refine Or.inr ⟨p, hpP, ?_, noBridge_list Q p R (hnb p hpP)⟩
      ext v
      simp only [type1Target, Finset.mem_inter]

theorem type1Target_member (Q : Early.ShortPath G D) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (R : ℝ)
    (hS : ∀ i : Fin Q.size, Q.vertex i ∈ S)
    (hnb : ∀ p ∈ P, ¬ Early.Bridge Q p R) (hrho : ∀ p ∈ P, rho p ≤ R)
    (label : (ℕ × ℕ) ⊕ Fin n) (hl : label ∈ type1Labels Q P rho R) :
    type1Target Q S P rho R label ∈ Geometry.fringes G S P rho D ++ Geometry.core G S P rho := by
  cases label with
  | inl I =>
      have hI : I ∈ Early.corePieces Q P rho R := by simpa [type1Labels] using hl
      have hb := type1_core_bounds Q P rho R hI
      let i : Fin Q.size := ⟨I.1, by omega⟩
      have hi : Early.Cells.Contains I i.val := ⟨le_rfl, hb.1⟩
      have hvC := Early.core_piece_contained Q P rho R hnb hrho hI hi
      exact List.mem_append.mpr (Or.inr (Geometry.coreChild_member G S P rho _ _ (hS i) hvC))
  | inr p =>
      have hp : p ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using hl
      have hpP : p ∈ P := type1_fringe_pivot Q P rho R hp
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨p, (mem_members P p).mpr hpP, rfl⟩))

end

end StreamingSSSP.Hopset
