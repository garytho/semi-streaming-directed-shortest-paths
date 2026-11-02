module

public import StreamingSSSP.Hopset.LateStageSampling
public import StreamingSSSP.Hopset.ReferenceOwners

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem labels_empty_iff (G : Graph (Fin n)) (P : Finset (Fin n)) (rho : Fin n → ℝ) (v : Fin n) :
    Geometry.labels G P rho v = [] ↔
      ∀ p ∈ P, ¬ Early.Within G v p (rho p) ∧ ¬ Early.Within G p v (rho p) := by
  constructor
  · intro he p hp
    constructor
    · intro h
      have hm := (Geometry.label_even G P rho p v).mpr ⟨hp, h⟩
      rw [he] at hm
      exact List.not_mem_nil hm
    · intro h
      have hm := (Geometry.label_odd G P rho p v).mpr ⟨hp, h⟩
      rw [he] at hm
      exact List.not_mem_nil hm
  · intro h
    calc
      _ = (members P).flatMap (fun _ => ([] : List ℕ)) := by
        apply List.flatMap_congr
        intro p hp
        have hh := h p ((mem_members P p).mp hp)
        simp only [hh.1, hh.2, ↓reduceIte, List.nil_append]
      _ = [] := by simp

theorem lateChild_emptyChild (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) :
    Reference.lateChild G S P rho = Late.emptyChild G S P rho := by
  ext v
  simp only [Reference.lateChild, Finset.mem_filter, Late.mem_emptyChild, labels_empty_iff]

theorem emptyChild_congr_on (G : Graph (Fin n)) (S P : Finset (Fin n)) (left right : Fin n → ℝ)
    (h : ∀ p ∈ P, left p = right p) : Late.emptyChild G S P left = Late.emptyChild G S P right := by
  ext v
  rw [Late.mem_emptyChild, Late.mem_emptyChild]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  rw [h p hp]

theorem lateStage_radius (cfg : Config) (hn : 0 < n) (r : ℕ) (H : Graph (Fin n))
    (S : Finset (Fin n)) (choice : Reference.Choice n cfg) (hP : choice.pivots ⊆ S)
    (p : Fin n) (hp : p ∈ choice.pivots) :
    (actualLateConfig n hn cfg).radii H (Reference.distanceScale cfg r) (lateStage cfg S choice) p =
      Reference.radii cfg r H choice.owners p := by
  let fallback : Fin cfg.groups × Fin cfg.shifts := (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  change Late.radius H (Reference.distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos p
    (Early.Sampling.ownerFor fallback (lateStage cfg S choice) p) = _
  rw [lateStage_owner cfg S choice hP p hp fallback]
  rfl

theorem actual_late_child (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n))
    (choice : Reference.Choice n cfg) (hP : choice.pivots ⊆ S) :
    (actualLateConfig n hn cfg).child stored (StoredEdges.graphOfEdges input) S
        (Reference.distanceScale cfg r) (lateStage cfg S choice) =
      Reference.lateChild (Backend.roundedRestricted stored input S cfg.inputScale) S choice.pivots
        (Reference.radii cfg r (Backend.roundedRestricted stored input S cfg.inputScale) choice.owners) := by
  dsimp only [actualLateConfig, Late.Config.child, Late.Config.search]
  rw [lateStage_pivots cfg S choice hP]
  have hsearch : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) S) =
      Backend.roundedRestricted stored input S cfg.inputScale := rfl
  rw [hsearch, lateChild_emptyChild]
  apply emptyChild_congr_on _ S choice.pivots
  intro p hp
  simpa only [actualLateConfig] using lateStage_radius cfg hn r
    (Backend.roundedRestricted stored input S cfg.inputScale) S choice hP p hp

end

end StreamingSSSP.Hopset
