module

public import StreamingSSSP.Hopset.ReferenceFacts

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

namespace Geometry

theorem labels_congr (G : Graph (Fin n)) (P : Finset (Fin n)) (left right : Fin n → ℝ)
    (h : ∀ p ∈ P, left p = right p) : labels G P left = labels G P right := by
  funext v
  unfold labels
  apply List.flatMap_congr
  intro p hp
  rw [h p ((mem_members P p).mp hp)]

theorem remaining_congr (G : Graph (Fin n)) (P : Finset (Fin n)) (left right : Fin n → ℝ)
    (h : ∀ p ∈ P, left p = right p) (v : Fin n) :
    Early.remaining G P left v ↔ Early.remaining G P right v := by
  unfold Early.remaining
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [h p hp]

theorem core_congr (G : Graph (Fin n)) (S P : Finset (Fin n)) (left right : Fin n → ℝ)
    (h : ∀ p ∈ P, left p = right p) : core G S P left = core G S P right := by
  have hk : (fun v => decide (Early.remaining G P left v)) =
      fun v => decide (Early.remaining G P right v) := by
    funext v
    simp only [propext (remaining_congr G P left right h v)]
  unfold core
  rw [hk, labels_congr G P left right h]

theorem fringes_congr (G : Graph (Fin n)) (S P : Finset (Fin n)) (left right : Fin n → ℝ)
    (D : ℝ) (h : ∀ p ∈ P, left p = right p) :
    fringes G S P left D = fringes G S P right D := by
  unfold fringes
  apply List.map_congr_left
  intro p hp
  rw [h p ((mem_members P p).mp hp)]

end Geometry

namespace Reference

theorem radii_congr (cfg : Config) (r : ℕ) (G : Graph (Fin n)) (P : Finset (Fin n))
    (left right : Owners n cfg) (h : ∀ p ∈ P, left p = right p) :
    ∀ p ∈ P, radii cfg r G left p = radii cfg r G right p := by
  intro p hp
  unfold radii
  rw [h p hp]

theorem children_owners_congr (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S P : Finset (Fin n))
    (left right : Owners n cfg) (h : ∀ p ∈ P, left p = right p) :
    children cfg stored input r S ⟨P, left⟩ = children cfg stored input r S ⟨P, right⟩ := by
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  have hr := radii_congr cfg r G P left right h
  dsimp only [children]
  split_ifs with he hl
  · rw [Geometry.fringes_congr G S P _ _ (distanceScale cfg r) hr,
      Geometry.core_congr G S P _ _ hr]
  · unfold lateChild
    rw [Geometry.labels_congr G P _ _ hr]
  · rfl

theorem blocks_owners_congr (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S P : Finset (Fin n))
    (left right : Owners n cfg) (h : ∀ p ∈ P, left p = right p) :
    blocks cfg stored input r S ⟨P, left⟩ = blocks cfg stored input r S ⟨P, right⟩ := by
  dsimp only [blocks]
  split_ifs with he
  · rfl
  · apply List.map_congr_left
    intro p hp
    rw [radii_congr cfg r _ P left right h p ((mem_members P p).mp hp)]

end Reference

end

end StreamingSSSP.Hopset
