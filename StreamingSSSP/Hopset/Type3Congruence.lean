module

public import StreamingSSSP.Early.Congruence
public import StreamingSSSP.Late.Boundary

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem admissibleChild_congr_on (H : Graph (Fin n)) (S P : Finset (Fin n))
    (left right : Fin n → ℝ) (D Rmax : ℝ) (xs : List (Fin n)) (X : Finset (Fin n))
    (h : ∀ p ∈ P, left p = right p) :
    AdmissibleChild H S P left D Rmax xs X ↔ AdmissibleChild H S P right D Rmax xs X := by
  have hc (L) : coreChild H S P left L = coreChild H S P right L := by
    ext v
    simp only [coreChild, Finset.mem_filter, Early.coreClass_congr_on H P left right h]
  simp only [AdmissibleChild, hc]
  apply or_congr Iff.rfl
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  rw [h p hp]

theorem type3_congr_on {R : Implicit.Representation n} {G : Graph (Fin n)} {u v : Fin n}
    (H : Graph (Fin n)) (S P : Finset (Fin n)) (left right : Fin n → ℝ)
    (D Rmax : ℝ) (xs : List (Fin n)) (e : Edge R G u v)
    (h : ∀ p ∈ P, left p = right p) :
    Type3 H S P left D Rmax xs e ↔ Type3 H S P right D Rmax xs e := by
  simp only [Type3, admissibleChild_congr_on H S P left right D Rmax xs _ h]

theorem type3Count_congr_on {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}
    (Q : Path R G s t) (H : Graph (Fin n)) (S P : Finset (Fin n)) (left right : Fin n → ℝ)
    (D Rmax : ℝ) (h : ∀ p ∈ P, left p = right p) :
    type3Count Q H S P left D Rmax = type3Count Q H S P right D Rmax := by
  simp only [type3Count, type3_congr_on H S P left right D Rmax Q.vertices _ h]

end

end StreamingSSSP.Late
