module

public import StreamingReachability.Hopset.IntervalCover
public import StreamingReachability.Hopset.NodeGeometry

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

theorem type1_core_bounds (Q : Early.ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ)
    {I : ℕ × ℕ} (hI : I ∈ Early.corePieces Q P rho R) :
    I.1 < I.2 ∧ I.2 ≤ Q.size := by
  have h := Early.Cells.bounds (Finset.mem_filter.mp hI).1
  exact ⟨h.1, h.2.1⟩

theorem type1_fringe_pivot (Q : Early.ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ)
    {p : V} (hp : p ∈ Early.fringeOwners Q P rho R) : p ∈ P :=
  (Finset.mem_filter.mp hp).1

theorem coreChild_mem (G : Graph V) (S P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) (v : V) :
    v ∈ Late.coreChild G S P rho L ↔
      v ∈ S ∧ Early.remaining G P rho v ∧ Early.labels G P rho v = L := by
  unfold Late.coreChild
  rw [Finset.mem_filter]
  rfl

def type1Labels (Q : Early.ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    Finset ((ℕ × ℕ) ⊕ V) :=
  (Early.corePieces Q P rho R).disjSum (Early.fringeOwners Q P rho R)

def type1Interval (Q : Early.ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    ((ℕ × ℕ) ⊕ V) → ℕ × ℕ
  | .inl I => I
  | .inr p => Early.fringeInterval Q P rho R p

def type1VertexCover (Q : Early.ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    VertexCover Q.size ((ℕ × ℕ) ⊕ V) where
  labels := type1Labels Q P rho R
  interval := type1Interval Q P rho R
  bounds := by
    intro label hl
    cases label with
    | inl I =>
        have hI : I ∈ Early.corePieces Q P rho R := by simpa [type1Labels] using hl
        have hb := Early.Cells.bounds (Finset.mem_filter.mp hI).1
        exact ⟨hb.1, hb.2.1⟩
    | inr p =>
        have hp : p ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using hl
        exact Early.Cover.interval_bounds hp
  covers := by
    intro i
    rcases Early.grouped_type1_cover Q P rho R i with ⟨I, hI, hi⟩ | ⟨p, hp, hi⟩
    · exact ⟨.inl I, by simpa [type1Labels] using hI, hi⟩
    · exact ⟨.inr p, by simpa [type1Labels] using hp, hi⟩
  unique := by
    intro a ha b hb i hia hib
    cases a with
    | inl I =>
        have hI : I ∈ Early.corePieces Q P rho R := by simpa [type1Labels] using ha
        cases b with
        | inl J =>
            have hJ : J ∈ Early.corePieces Q P rho R := by simpa [type1Labels] using hb
            exact congrArg Sum.inl (Early.Cells.overlap_eq
              (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hia hib)
        | inr p =>
            have hp : p ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using hb
            exact False.elim (Early.Cover.core_fringe_disjoint (P := P)
              (C := fun p => Early.pivotCut Q p (rho p) R) hI hp i ⟨hia, hib⟩)
    | inr p =>
        have hp : p ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using ha
        cases b with
        | inl I =>
            have hI : I ∈ Early.corePieces Q P rho R := by simpa [type1Labels] using hb
            exact False.elim (Early.Cover.core_fringe_disjoint (P := P)
              (C := fun p => Early.pivotCut Q p (rho p) R) hI hp i ⟨hib, hia⟩)
        | inr q =>
            have hq : q ∈ Early.fringeOwners Q P rho R := by simpa [type1Labels] using hb
            by_cases he : p = q
            · exact congrArg Sum.inr he
            · exact False.elim (Early.Cover.fringe_disjoint hp hq he i ⟨hia, hib⟩)

theorem type1VertexCover_card (Q : Early.ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    (type1VertexCover Q P rho R).labels.card =
      (Early.corePieces Q P rho R).card + (Early.fringeOwners Q P rho R).card := by
  simp [type1VertexCover, type1Labels]

end

end StreamingReachability.Hopset
