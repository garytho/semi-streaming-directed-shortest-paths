module

public import StreamingReachability.Early.Recurrence

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

theorem mem_coreRelated (Q : ShortPath G D) (E P : Finset V) (rho : V → ℝ)
    (R Rmin : ℝ) (I : ℕ × ℕ) (w : V) :
    let C := coreClass G P rho (smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1)
    w ∈ coreRelated Q E P rho R Rmin I ↔
      w ∈ E ∧ w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
        ∃ hw : w ∈ C, ∃ hi : Q.vertex i ∈ C,
          Within (G.restrict C) ⟨w, hw⟩ ⟨Q.vertex i, hi⟩ Rmin := by
  unfold coreRelated
  exact Finset.mem_filter

theorem mem_coreDescRelated (Q : ShortPath G D) (E P : Finset V) (rho : V → ℝ)
    (R Rmin : ℝ) (I : ℕ × ℕ) (w : V) :
    let C := coreClass G P rho (smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1)
    w ∈ coreDescRelated Q E P rho R Rmin I ↔
      w ∈ E ∧ w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
        ∃ hw : w ∈ C, ∃ hi : Q.vertex i ∈ C,
          Within (G.restrict C) ⟨Q.vertex i, hi⟩ ⟨w, hw⟩ Rmin := by
  unfold coreDescRelated
  exact Finset.mem_filter

theorem mem_fringeRelated (Q : ShortPath G D) (E P : Finset V) (rho : V → ℝ)
    (R Rmin : ℝ) (p w : V) :
    let C : Set V := ↑(fringe G p (rho p) D)
    w ∈ fringeRelated Q E P rho R Rmin p ↔
      w ∈ E ∧ w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains (fringeInterval Q P rho R p) i.val ∧
        ∃ hw : w ∈ C, ∃ hi : Q.vertex i ∈ C,
          Within (G.restrict C) ⟨w, hw⟩ ⟨Q.vertex i, hi⟩ Rmin ∨
          Within (G.restrict C) ⟨Q.vertex i, hi⟩ ⟨w, hw⟩ Rmin := by
  unfold fringeRelated
  exact Finset.mem_filter

end

end StreamingReachability.Early
