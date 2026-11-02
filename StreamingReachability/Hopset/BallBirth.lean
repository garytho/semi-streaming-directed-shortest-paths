module

public import StreamingReachability.Hopset.ScaleSeparation
public import StreamingReachability.Hopset.FreshBalls
public import StreamingReachability.Hopset.BlockBudget

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical

noncomputable section

variable {n : ℕ}

def ParentHits (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S P : Finset (Fin n)) : Prop :=
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let t := Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1))
  ∀ v ∈ S,
    Hits (Early.searchIn G v t) (Early.inComparison G) (Parameters.ballSize n (r + 1)) P ∧
      Hits (Early.searchOut G v t) (Early.outComparison G) (Parameters.ballSize n (r + 1)) P

def BadBirth (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) : Prop :=
  ∃ T ∈ children cfg stored input r S choice, ¬ BallsGood cfg stored input (r + 1) T

theorem core_birth_good (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (S P T : Finset (Fin n)) (owners : Owners n cfg)
    (hTS : T ⊆ S)
    (L : Finset (Fin n) × Finset (Fin n))
    (hclass : ∀ v ∈ T, v ∈ Early.coreClass
      (Backend.roundedRestricted stored input S cfg.inputScale) P
      (radii cfg r (Backend.roundedRestricted stored input S cfg.inputScale) owners) L)
    (hhits : ParentHits cfg stored input r S P) :
    BallsGood cfg stored input (r + 1) T := by
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let F := Backend.roundedRestricted stored input T cfg.inputScale
  let rho := radii cfg r G owners
  let t := Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1))
  have hF : Implicit.induced F T = F :=
    Late.search_induced stored (StoredEdges.graphOfEdges input) T cfg.inputScale
  have hmono (u v : Fin n) : G.dist u v ≤ F.dist u v :=
    Geometry.child_distance_mono cfg stored input hTS u v
  have hsmall (p : Fin n) (_hp : p ∈ P) : t ≤ rho p :=
    radii_above_next_search cfg hnum r G owners p
  intro v hv
  have hs := hhits v (hTS hv)
  exact ⟨Geometry.core_inball_shrink G F T P rho L hclass hF hmono v hv t hsmall _ hs.1,
    Geometry.core_outball_shrink G F T P rho L hclass hF hmono v hv t hsmall _ hs.2⟩

theorem fringe_birth_good (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (hk : cfg.k = Parameters.k n) (r : ℕ) (S : Finset (Fin n)) (p : Fin n)
    (owners : Owners n cfg) (hp : p ∈ S) (hballs : BallsGood cfg stored input r S) :
    BallsGood cfg stored input (r + 1)
      (S ∩ Early.fringe (Backend.roundedRestricted stored input S cfg.inputScale) p
        (radii cfg r (Backend.roundedRestricted stored input S cfg.inputScale) owners p)
        (distanceScale cfg r)) := by
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let T := S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
  let F := Backend.roundedRestricted stored input T cfg.inputScale
  have hcard : T.card ≤ Parameters.ballSize n (r + 1) := by
    have h := Geometry.runtime_fringe_size G S p (distanceScale cfg r) cfg.k cfg.groups cfg.shifts
      (Parameters.ballSize n r) cfg.k_pos (distanceScale_pos cfg hnum r) (owners p)
      (hballs p hp).1 (hballs p hp).2
    have he : Parameters.ballSize n r / cfg.k = Parameters.ballSize n (r + 1) := by
      rw [hk, Parameters.ballSize_succ]
    exact h.trans_eq he
  have hF : Implicit.induced F T = F :=
    Late.search_induced stored (StoredEdges.graphOfEdges input) T cfg.inputScale
  intro v hv
  exact ⟨(Finset.card_le_card (Geometry.inball_subset F T hF v hv _)).trans hcard,
    (Finset.card_le_card (Geometry.outball_subset F T hF v hv _)).trans hcard⟩

theorem no_bad_birth_of_hits (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (hk : cfg.k = Parameters.k n) (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg)
    (hP : r < cfg.earlyLevel → choice.pivots ⊆ S) (hballs : BallsGood cfg stored input r S)
    (hhits : ParentHits cfg stored input r S choice.pivots) :
    ¬ BadBirth cfg stored input r S choice := by
  rintro ⟨T, hT, hbad⟩
  have hgood : BallsGood cfg stored input (r + 1) T := by
    dsimp only [children] at hT
    split_ifs at hT with he hl
    · rcases List.mem_append.mp hT with hfringe | hcore
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hfringe
        exact fringe_birth_good cfg stored input hnum hk r S p choice.owners
          (hP he ((mem_members _ _).mp hp)) hballs
      · obtain ⟨L, hL⟩ := Geometry.core_class _ S choice.pivots _ T hcore
        exact core_birth_good cfg stored input hnum r S choice.pivots T choice.owners
          (Geometry.core_subset _ S choice.pivots _ T hcore) L hL hhits
    · have hte := List.mem_singleton.mp hT
      subst T
      exact core_birth_good cfg stored input hnum r S choice.pivots _ choice.owners
        (lateChild_subset _ S choice.pivots _) (∅, ∅) (lateChild_class _ S choice.pivots _) hhits
    · simp at hT
  exact hbad hgood

theorem rank_hits_set (S A : Finset (Fin n)) (hAS : A ⊆ S)
    (R : Fin n → Fin n → Prop) (b r : ℕ) (ranks : Fin n → ℕ) :
    CopyHistory.Hits A R b r ranks ↔ Hits A R b (CopyHistory.pivots S r ranks) := by
  constructor
  · intro h u hu hb
    obtain ⟨p, hp, hr⟩ := h u hu hb
    have hpA := (Finset.mem_filter.mp hp).1
    have hRp := (Finset.mem_filter.mp hp).2
    exact ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hAS hpA, hr⟩, hpA⟩, hRp⟩
  · intro h u hu hb
    obtain ⟨p, hp, hRp⟩ := h u hu hb
    obtain ⟨hpP, hpA⟩ := Finset.mem_inter.mp hp
    exact ⟨p, Finset.mem_filter.mpr ⟨hpA, hRp⟩, (Finset.mem_filter.mp hpP).2⟩

theorem owner_bad_birth_bound (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (hk : cfg.k = Parameters.k n) (r : ℕ) (S P : Finset (Fin n))
    (hP : r < cfg.earlyLevel → P ⊆ S) (hballs : BallsGood cfg stored input r S) :
    (ownerLaw n cfg).prob (fun owners => BadBirth cfg stored input r S ⟨P, owners⟩) ≤
      if ParentHits cfg stored input r S P then 0 else 1 := by
  by_cases hh : ParentHits cfg stored input r S P
  · simp only [hh, ↓reduceIte]
    have hz : (ownerLaw n cfg).prob (fun owners => BadBirth cfg stored input r S ⟨P, owners⟩) = 0 := by
      apply (Law.prob_congr _ _ (fun _ => False) ?_).trans (Law.prob_false _)
      intro owners
      exact iff_false_intro (no_bad_birth_of_hits cfg stored input hnum hk r S ⟨P, owners⟩ hP hballs hh)
    exact hz.le
  · simp only [hh, ↓reduceIte]
    exact Law.prob_le_one _ _

theorem parent_ball_subsets (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) :
    (∀ v ∈ S, Early.searchIn (Backend.roundedRestricted stored input S cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1))) ⊆ S) ∧
      (∀ v ∈ S, Early.searchOut (Backend.roundedRestricted stored input S cfg.inputScale) v
        (Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1))) ⊆ S) := by
  have hG : Implicit.induced (Backend.roundedRestricted stored input S cfg.inputScale) S =
      Backend.roundedRestricted stored input S cfg.inputScale :=
    Late.search_induced stored (StoredEdges.graphOfEdges input) S cfg.inputScale
  exact ⟨fun v hv => Geometry.inball_subset _ S hG v hv _,
    fun v hv => Geometry.outball_subset _ S hG v hv _⟩

theorem early_parent_hit_failure (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (r : ℕ) (S : Finset (Fin n)) (history : List (CopyHistory.Observation n))
    (he : r < (Parameters.configuration n accuracy x delta blockVolume ha hd).earlyLevel)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r) :
    (CopyHistory.law (earlyRates n hn x) history).prob (fun ranks =>
        ¬ ParentHits (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input r S
          (CopyHistory.pivots S r ranks)) ≤
      2 * (S.card : ℝ) ^ 2 * Real.exp (-25 * Parameters.ell n) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let t := Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1))
  let Ain := fun v => Early.searchIn G v t
  let Aout := fun v => Early.searchOut G v t
  have hsub := parent_ball_subsets cfg stored input r S
  have h := Parameters.early_ball_failure n hn x r he history S Ain Aout
    (Early.inComparison G) (Early.outComparison G) hsub.1 hsub.2 hc hp
  apply (Law.prob_mono _ ?_).trans h
  intro ranks hbad
  by_contra hnone
  push Not at hnone
  apply hbad
  intro v hv
  have hh := hnone v hv
  exact ⟨(rank_hits_set S (Ain v) (hsub.1 v hv) _ _ _ ranks).mp hh.1,
    (rank_hits_set S (Aout v) (hsub.2 v hv) _ _ _ ranks).mp hh.2⟩

theorem fresh_parent_hit_failure (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (r : ℕ) (S : Finset (Fin n)) (hr : r < Parameters.maximumLevel n) :
    (Law.subset
      (fun _ : Fin n => (PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r).value)
      (fun _ => (PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r).value_nonneg)
      (fun _ => (PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r).value_le_one)
      (members S)).prob (fun P =>
        ¬ ParentHits (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input r S P) ≤
      2 * (S.card : ℝ) ^ 2 * Real.exp (-25 * Parameters.ell n) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let t := Early.searchRadius cfg.k cfg.groups (distanceScale cfg (r + 1))
  let Ain := fun v => Early.searchIn G v t
  let Aout := fun v => Early.searchOut G v t
  let rate := PivotProfile.rate n hn (Parameters.k n) (Parameters.ell n) r
  have hsub := parent_ball_subsets cfg stored input r S
  have h := fresh_two_direction_failure rate.value rate.value_nonneg rate.value_le_one S Ain Aout
    (Early.inComparison G) (Early.outComparison G) (Parameters.ballSize n (r + 1)) hsub.1 hsub.2
  apply (Law.prob_mono _ ?_).trans (h.trans ?_)
  · intro P hbad
    by_contra hnone
    push Not at hnone
    exact hbad hnone
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hlow := Parameters.ball_rate_lower_next n hn r hr
    nlinarith

theorem calibrated_bad_birth_probability (n : ℕ) (hn : 0 < n)
    (accuracy x delta blockVolume : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (r : ℕ) (S : Finset (Fin n)) (history : List (CopyHistory.Observation n))
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hballs : BallsGood (Parameters.configuration n accuracy x delta blockVolume ha hd) stored input r S) :
    ((CopyHistory.law (earlyRates n hn x) history).bind fun ranks =>
        kernel (Parameters.configuration n accuracy x delta blockVolume ha hd) hn stored input ranks r S).prob
        (fun step => BadBirth (Parameters.configuration n accuracy x delta blockVolume ha hd)
          stored input r S step.value) ≤
      2 * (S.card : ℝ) ^ 2 * Real.exp (-25 * Parameters.ell n) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let mu := CopyHistory.law (earlyRates n hn x) history
  have hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  have hk : cfg.k = Parameters.k n := rfl
  change (mu.bind fun ranks => kernel cfg hn stored input ranks r S).prob
    (fun step => BadBirth cfg stored input r S step.value) ≤ _
  rw [Law.prob_bind]
  by_cases he : r < cfg.earlyLevel
  · have hkernel (ranks : Fin n → ℕ) :
        (kernel cfg hn stored input ranks r S).prob (fun step => BadBirth cfg stored input r S step.value) =
          (ownerLaw n cfg).prob (fun owners => BadBirth cfg stored input r S ⟨CopyHistory.pivots S r ranks, owners⟩) := by
      simp only [kernel, Law.prob_map, choices, pivotLaw, he, ↓reduceIte,
        Law.prob_bind, Law.expect_pure]
    simp_rw [hkernel]
    have hbound :
        mu.expect (fun ranks => (ownerLaw n cfg).prob (fun owners =>
          BadBirth cfg stored input r S ⟨CopyHistory.pivots S r ranks, owners⟩)) ≤
          mu.expect (fun ranks => if ¬ ParentHits cfg stored input r S (CopyHistory.pivots S r ranks)
            then (1 : ℝ) else 0) := by
      apply Law.expect_mono
      intro ranks
      have h := owner_bad_birth_bound cfg stored input hnum hk r S (CopyHistory.pivots S r ranks)
        (fun _ => Finset.filter_subset _ _) hballs
      by_cases hh : ParentHits cfg stored input r S (CopyHistory.pivots S r ranks) <;>
        simpa only [hh, not_true_eq_false, not_false_eq_true, ↓reduceIte] using h
    apply hbound.trans
    rw [Law.expect_indicator mu (fun ranks => ¬ ParentHits cfg stored input r S (CopyHistory.pivots S r ranks))]
    exact early_parent_hit_failure n hn accuracy x delta blockVolume ha hd stored input r S history he hc hp
  · by_cases hl : r < cfg.maximumLevel
    · let rate := PivotProfile.rate n hn cfg.k cfg.logarithm r
      let fresh := Law.subset (fun _ : Fin n => rate.value) (fun _ => rate.value_nonneg)
        (fun _ => rate.value_le_one) (members S)
      have hkernel (ranks : Fin n → ℕ) :
          (kernel cfg hn stored input ranks r S).prob (fun step => BadBirth cfg stored input r S step.value) =
            fresh.expect (fun P => (ownerLaw n cfg).prob (fun owners => BadBirth cfg stored input r S ⟨P, owners⟩)) := by
        simp only [kernel, Law.prob_map, choices, pivotLaw, he, hl, ↓reduceIte, Law.prob_bind]
        rfl
      simp_rw [hkernel]
      rw [Law.expect_const]
      have hbound :
          fresh.expect (fun P => (ownerLaw n cfg).prob (fun owners => BadBirth cfg stored input r S ⟨P, owners⟩)) ≤
            fresh.expect (fun P => if ¬ ParentHits cfg stored input r S P then (1 : ℝ) else 0) := by
        apply Law.expect_mono
        intro P
        have h := owner_bad_birth_bound cfg stored input hnum hk r S P (by intro h; exact False.elim (he h)) hballs
        by_cases hh : ParentHits cfg stored input r S P <;>
          simpa only [hh, not_true_eq_false, not_false_eq_true, ↓reduceIte] using h
      apply hbound.trans
      rw [Law.expect_indicator fresh (fun P => ¬ ParentHits cfg stored input r S P)]
      exact fresh_parent_hit_failure n hn accuracy x delta blockVolume ha hd stored input r S hl
    · have hkernel (ranks : Fin n → ℕ) :
          (kernel cfg hn stored input ranks r S).prob (fun step => BadBirth cfg stored input r S step.value) = 0 := by
        have hevent : (fun step : Branching.Step (Finset (Fin n)) (Choice n cfg) =>
            BadBirth cfg stored input r S step.value) =
            fun _ => False := by
          funext step
          apply propext
          simp [BadBirth, children, he, hl]
        rw [hevent, Law.prob_false]
      simp_rw [hkernel]
      rw [Law.expect_const]
      positivity

end

end StreamingReachability.Hopset.Reference
