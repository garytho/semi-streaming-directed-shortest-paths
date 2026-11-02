module

public import StreamingReachability.Early.Recurrence

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

theorem labels_congr_on (G : Graph V) (P : Finset V) (left right : V → ℝ)
    (h : ∀ p ∈ P, left p = right p) : labels G P left = labels G P right := by
  funext v
  apply Prod.ext <;> ext p <;> simp only [labels, Finset.mem_filter]
  · exact and_congr_right (fun hp => by rw [h p hp])
  · exact and_congr_right (fun hp => by rw [h p hp])

theorem remaining_congr_on (G : Graph V) (P : Finset V) (left right : V → ℝ)
    (h : ∀ p ∈ P, left p = right p) (v : V) :
    remaining G P left v ↔ remaining G P right v := by
  unfold remaining
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [h p hp]

theorem coreClass_congr_on (G : Graph V) (P : Finset V) (left right : V → ℝ)
    (h : ∀ p ∈ P, left p = right p) : coreClass G P left = coreClass G P right := by
  funext L
  ext v
  simp only [coreClass, Set.mem_setOf_eq, remaining_congr_on G P left right h,
    labels_congr_on G P left right h]

theorem boundaries_congr_on {m : ℕ} (P : Finset V) (left right : V → Cut m)
    (h : ∀ p ∈ P, left p = right p) : boundaries P left = boundaries P right := by
  have hlo : P.image (fun p => (left p).lo) = P.image (fun p => (right p).lo) :=
    Finset.image_congr (fun p hp => congrArg Cut.lo (h p hp))
  have hhi : P.image (fun p => (left p).hi) = P.image (fun p => (right p).hi) :=
    Finset.image_congr (fun p hp => congrArg Cut.hi (h p hp))
  simp only [boundaries, hlo, hhi]

theorem smoothLabels_congr_on {m : ℕ} (P : Finset V) (left right : V → Cut m)
    (h : ∀ p ∈ P, left p = right p) (i : ℕ) :
    smoothLabels P left i = smoothLabels P right i := by
  apply Prod.ext <;> ext p <;> simp only [smoothLabels, Finset.mem_filter]
  · exact and_congr_right (fun hp => by rw [h p hp])
  · exact and_congr_right (fun hp => by rw [h p hp])

namespace Cover

theorem owner_congr_on {m : ℕ} (P : Finset V) (left right : V → Cut m)
    (h : ∀ p ∈ P, left p = right p) : owner P left = owner P right := by
  funext i
  cases he : owner P left i with
  | none =>
      apply Eq.symm
      apply (owner_none_iff P right i).mpr
      intro p hp hc
      exact (owner_none_iff P left i).mp he p hp (by simpa only [h p hp] using hc)
  | some p =>
      have hp := (owner_some_iff P left i p).mp he
      apply Eq.symm
      apply (owner_some_iff P right i p).mpr
      refine ⟨hp.1, by simpa only [h p hp.1] using hp.2.1, ?_⟩
      intro q hq hqC
      have hmax := hp.2.2 q hq (by simpa only [h q hq] using hqC)
      simpa only [priority, h p hp.1, h q hq] using hmax

theorem owners_congr_on {m : ℕ} (P : Finset V) (left right : V → Cut m)
    (h : ∀ p ∈ P, left p = right p) : owners P left = owners P right := by
  simp only [owners, owner_congr_on P left right h]

theorem interval_congr_on {m : ℕ} (P : Finset V) (left right : V → Cut m)
    (h : ∀ p ∈ P, left p = right p) (p : V) : interval P left p = interval P right p := by
  have hi : indices P left p = indices P right p := by
    simp only [indices, owner_congr_on P left right h]
  unfold interval
  rw [hi]

end Cover

theorem corePieces_congr_on (Q : ShortPath G D) (P : Finset V) (left right : V → ℝ)
    (R : ℝ) (h : ∀ p ∈ P, left p = right p) :
    corePieces Q P left R = corePieces Q P right R := by
  have hc : ∀ p ∈ P, pivotCut Q p (left p) R = pivotCut Q p (right p) R :=
    fun p hp => congrArg (fun rho => pivotCut Q p rho R) (h p hp)
  unfold corePieces type1Pieces
  rw [boundaries_congr_on P _ _ hc]
  apply Finset.filter_congr
  intro I hI
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [h p hp]

theorem fringeOwners_congr_on (Q : ShortPath G D) (P : Finset V) (left right : V → ℝ)
    (R : ℝ) (h : ∀ p ∈ P, left p = right p) :
    fringeOwners Q P left R = fringeOwners Q P right R :=
  Cover.owners_congr_on P _ _ (fun p hp =>
    congrArg (fun rho => pivotCut Q p rho R) (h p hp))

theorem fringeInterval_congr_on (Q : ShortPath G D) (P : Finset V) (left right : V → ℝ)
    (R : ℝ) (h : ∀ p ∈ P, left p = right p) (p : V) :
    fringeInterval Q P left R p = fringeInterval Q P right R p :=
  Cover.interval_congr_on P _ _ (fun p hp =>
    congrArg (fun rho => pivotCut Q p rho R) (h p hp)) p

theorem pieceNumber_congr_on (Q : ShortPath G D) (P : Finset V) (left right : V → ℝ)
    (R : ℝ) (h : ∀ p ∈ P, left p = right p) :
    pieceNumber Q P left R = pieceNumber Q P right R := by
  simp only [pieceNumber, corePieces_congr_on Q P left right R h,
    fringeOwners_congr_on Q P left right R h]

theorem coreRelated_congr_on (Q : ShortPath G D) (E P : Finset V) (left right : V → ℝ)
    (R Rmin : ℝ) (I : ℕ × ℕ) (h : ∀ p ∈ P, left p = right p) :
    coreRelated Q E P left R Rmin I = coreRelated Q E P right R Rmin I := by
  have hc := smoothLabels_congr_on P
    (fun p => pivotCut Q p (left p) R) (fun p => pivotCut Q p (right p) R)
    (fun p hp => congrArg (fun rho => pivotCut Q p rho R) (h p hp)) I.1
  have hs : coreClass G P left (smoothLabels P (fun p => pivotCut Q p (left p) R) I.1) =
      coreClass G P right (smoothLabels P (fun p => pivotCut Q p (right p) R) I.1) := by
    rw [coreClass_congr_on G P left right h, hc]
  let F : Set V → Finset V := fun S =>
    E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
      ∃ hw : w ∈ S, ∃ hi : Q.vertex i ∈ S,
        Within (G.restrict S) ⟨w, hw⟩ ⟨Q.vertex i, hi⟩ Rmin
  exact congrArg F hs

theorem coreDescRelated_congr_on (Q : ShortPath G D) (E P : Finset V) (left right : V → ℝ)
    (R Rmin : ℝ) (I : ℕ × ℕ) (h : ∀ p ∈ P, left p = right p) :
    coreDescRelated Q E P left R Rmin I = coreDescRelated Q E P right R Rmin I := by
  have hc := smoothLabels_congr_on P
    (fun p => pivotCut Q p (left p) R) (fun p => pivotCut Q p (right p) R)
    (fun p hp => congrArg (fun rho => pivotCut Q p rho R) (h p hp)) I.1
  have hs : coreClass G P left (smoothLabels P (fun p => pivotCut Q p (left p) R) I.1) =
      coreClass G P right (smoothLabels P (fun p => pivotCut Q p (right p) R) I.1) := by
    rw [coreClass_congr_on G P left right h, hc]
  let F : Set V → Finset V := fun S =>
    E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
      ∃ hw : w ∈ S, ∃ hi : Q.vertex i ∈ S,
        Within (G.restrict S) ⟨Q.vertex i, hi⟩ ⟨w, hw⟩ Rmin
  exact congrArg F hs

theorem fringeRelated_congr_on (Q : ShortPath G D) (E P : Finset V) (left right : V → ℝ)
    (R Rmin : ℝ) (p : V) (hp : p ∈ P) (h : ∀ p ∈ P, left p = right p) :
    fringeRelated Q E P left R Rmin p = fringeRelated Q E P right R Rmin p := by
  let F : Finset V → (ℕ × ℕ) → Finset V := fun S I =>
    E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
      ∃ hw : w ∈ S, ∃ hi : Q.vertex i ∈ S,
        Within (G.restrict (↑S : Set V)) ⟨w, hw⟩ ⟨Q.vertex i, hi⟩ Rmin ∨
        Within (G.restrict (↑S : Set V)) ⟨Q.vertex i, hi⟩ ⟨w, hw⟩ Rmin
  exact congrArg₂ F (congrArg (fun rho => fringe G p rho D) (h p hp))
    (fringeInterval_congr_on Q P left right R h p)

theorem actualRelatedTotal_congr_on (Q : ShortPath G D) (E P : Finset V) (left right : V → ℝ)
    (R Rmin : ℝ) (h : ∀ p ∈ P, left p = right p) :
    actualRelatedTotal Q E P left R Rmin = actualRelatedTotal Q E P right R Rmin := by
  by_cases hs : stopped Q P R
  · simp only [actualRelatedTotal, hs, ↓reduceIte]
  · simp only [actualRelatedTotal, hs, ↓reduceIte, corePieces_congr_on Q P left right R h,
      fringeOwners_congr_on Q P left right R h]
    apply congrArg₂ Nat.add
    · apply Finset.sum_congr rfl
      intro I hI
      rw [coreRelated_congr_on Q E P left right R Rmin I h,
        coreDescRelated_congr_on Q E P left right R Rmin I h]
    · apply Finset.sum_congr rfl
      intro p hp
      have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
      rw [fringeRelated_congr_on Q E P left right R Rmin p hpP h]

end

end StreamingReachability.Early
