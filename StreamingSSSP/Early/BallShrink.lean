module

public import StreamingSSSP.Early.Recurrence

@[expose] public section

namespace StreamingSSSP.Early

open scoped Classical BigOperators

noncomputable section

theorem mem_tournament_survivors {A : Type*} (S P : Finset A) (R : A → A → Prop) (u : A) :
    u ∈ Tournament.survivors S P R ↔ u ∈ S ∧ ∀ p ∈ P, ¬ R u p := by
  simp only [Tournament.survivors, Finset.mem_filter]

variable {V U : Type*} [Fintype V] [Fintype U] {D : ℝ}

def inComparison (G : Graph V) (u p : V) : Prop :=
  G.dist u p ≤ G.dist p u

def outComparison (G : Graph V) (u p : V) : Prop :=
  G.dist p u ≤ G.dist u p

theorem inComparison_total (G : Graph V) (u p : V) :
    inComparison G u p ∨ inComparison G p u :=
  le_total _ _

theorem outComparison_total (G : Graph V) (u p : V) :
    outComparison G u p ∨ outComparison G p u :=
  le_total _ _

theorem inComparison_reverse (G : Graph V) (u p : V) :
    inComparison G.reverse u p ↔ outComparison G u p := by
  simp only [inComparison, outComparison, Graph.dist_reverse]

/-- A sampled ancestor of the center forces its out-label on the whole
surviving class. A vertex ordered before that pivot would then be in both
balls, contradicting the actual core deletion rule. -/
theorem core_in_knockout (G : Graph V) (P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) {u v p : V}
    (hu : u ∈ coreClass G P rho L) (hv : v ∈ coreClass G P rho L)
    (hp : p ∈ P) (hpv : Within G p v (rho p)) :
    ¬ inComparison G u p := by
  intro hcmp
  have he := Finset.ext_iff.mp
    (congrArg Prod.snd (hu.2.trans hv.2.symm)) p
  have hpu : Within G p u (rho p) := by
    have hvlabel : p ∈ (labels G P rho v).2 := by simp [labels, hp, hpv]
    have hulabel := he.mpr hvlabel
    exact (Finset.mem_filter.mp hulabel).2
  exact hu.1 p hp ⟨bounded_mono_distance hcmp hpu, hpu⟩

theorem core_out_knockout (G : Graph V) (P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) {u v p : V}
    (hu : u ∈ coreClass G P rho L) (hv : v ∈ coreClass G P rho L)
    (hp : p ∈ P) (hvp : Within G v p (rho p)) :
    ¬ outComparison G u p := by
  intro hcmp
  have he := Finset.ext_iff.mp
    (congrArg Prod.fst (hu.2.trans hv.2.symm)) p
  have hup : Within G u p (rho p) := by
    have hvlabel : p ∈ (labels G P rho v).1 := by simp [labels, hp, hvp]
    have hulabel := he.mpr hvlabel
    exact (Finset.mem_filter.mp hulabel).2
  exact hu.1 p hp ⟨hup, bounded_mono_distance hcmp hup⟩

/-- The child may have larger edge weights and larger distances than the
induced parent graph. Only distance monotonicity and actual core membership
are used; no ball-shrink certificate is supplied. -/
theorem core_child_inball_subset (G : Graph V) (F : Graph U)
    (embedding : U → V) (P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) (v : U) (t : ℝ)
    (hcore : ∀ u, embedding u ∈ coreClass G P rho L)
    (hmono : ∀ u w, G.dist (embedding u) (embedding w) ≤ F.dist u w)
    (hsmall : ∀ p ∈ P, t ≤ rho p) :
    (searchIn F v t).image embedding ⊆
      Tournament.survivors (searchIn G (embedding v) t)
        (P ∩ searchIn G (embedding v) t) (inComparison G) := by
  classical
  intro u hu
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
  have hwv : Within G (embedding w) (embedding v) t :=
    bounded_mono_distance (hmono w v) (Finset.mem_filter.mp hw).2
  apply (mem_tournament_survivors _ _ _ _).mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwv⟩, ?_⟩
  intro p hp
  obtain ⟨hpP, hpA⟩ := Finset.mem_inter.mp hp
  exact core_in_knockout G P rho L (hcore w) (hcore v) hpP
    (within_mono (Finset.mem_filter.mp hpA).2 (hsmall p hpP))

theorem core_child_outball_subset (G : Graph V) (F : Graph U)
    (embedding : U → V) (P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) (v : U) (t : ℝ)
    (hcore : ∀ u, embedding u ∈ coreClass G P rho L)
    (hmono : ∀ u w, G.dist (embedding u) (embedding w) ≤ F.dist u w)
    (hsmall : ∀ p ∈ P, t ≤ rho p) :
    (searchOut F v t).image embedding ⊆
      Tournament.survivors (searchOut G (embedding v) t)
        (P ∩ searchOut G (embedding v) t) (outComparison G) := by
  classical
  intro u hu
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
  have hvw : Within G (embedding v) (embedding w) t :=
    bounded_mono_distance (hmono v w) (Finset.mem_filter.mp hw).2
  apply (mem_tournament_survivors _ _ _ _).mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩, ?_⟩
  intro p hp
  obtain ⟨hpP, hpA⟩ := Finset.mem_inter.mp hp
  exact core_out_knockout G P rho L (hcore w) (hcore v) hpP
    (within_mono (Finset.mem_filter.mp hpA).2 (hsmall p hpP))

theorem core_child_inball_card_le (G : Graph V) (F : Graph U)
    (embedding : U → V) (hinj : Function.Injective embedding)
    (P : Finset V) (rho : V → ℝ) (L : Finset V × Finset V)
    (v : U) (t : ℝ) (b : ℕ)
    (hcore : ∀ u, embedding u ∈ coreClass G P rho L)
    (hmono : ∀ u w, G.dist (embedding u) (embedding w) ≤ F.dist u w)
    (hsmall : ∀ p ∈ P, t ≤ rho p)
    (hhit : ∀ u ∈ searchIn G (embedding v) t,
      b ≤ 2 * Tournament.degree (searchIn G (embedding v) t) (inComparison G) u →
        ∃ p ∈ P ∩ searchIn G (embedding v) t, inComparison G u p) :
    (searchIn F v t).card ≤ b := by
  rw [← Finset.card_image_of_injective (searchIn F v t) hinj]
  exact (Finset.card_le_card
    (core_child_inball_subset G F embedding P rho L v t hcore hmono hsmall)).trans
      (Tournament.survivors_card_le _ _ _ b
        (fun u _ p _ => inComparison_total G u p) hhit)

theorem core_child_outball_card_le (G : Graph V) (F : Graph U)
    (embedding : U → V) (hinj : Function.Injective embedding)
    (P : Finset V) (rho : V → ℝ) (L : Finset V × Finset V)
    (v : U) (t : ℝ) (b : ℕ)
    (hcore : ∀ u, embedding u ∈ coreClass G P rho L)
    (hmono : ∀ u w, G.dist (embedding u) (embedding w) ≤ F.dist u w)
    (hsmall : ∀ p ∈ P, t ≤ rho p)
    (hhit : ∀ u ∈ searchOut G (embedding v) t,
      b ≤ 2 * Tournament.degree (searchOut G (embedding v) t) (outComparison G) u →
        ∃ p ∈ P ∩ searchOut G (embedding v) t, outComparison G u p) :
    (searchOut F v t).card ≤ b := by
  rw [← Finset.card_image_of_injective (searchOut F v t) hinj]
  exact (Finset.card_le_card
    (core_child_outball_subset G F embedding P rho L v t hcore hmono hsmall)).trans
      (Tournament.survivors_card_le _ _ _ b
        (fun u _ p _ => outComparison_total G u p) hhit)

theorem small_radius_le {lambda D t rho : ℝ}
    (hD : 0 ≤ D) (ht : t ≤ (lambda - 1) * D) (hrho : lambda * D ≤ rho) :
    t ≤ rho := by
  nlinarith

theorem core_child_inball_shrink (G : Graph V) (F : Graph U)
    (embedding : U → V) (hinj : Function.Injective embedding)
    (P : Finset V) (rho : V → ℝ) (L : Finset V × Finset V)
    (v : U) (lambda D t : ℝ) (b : ℕ) (hD : 0 ≤ D)
    (hscale : t ≤ (lambda - 1) * D) (hrho : ∀ p ∈ P, lambda * D ≤ rho p)
    (hcore : ∀ u, embedding u ∈ coreClass G P rho L)
    (hmono : ∀ u w, G.dist (embedding u) (embedding w) ≤ F.dist u w)
    (hhit : ∀ u ∈ searchIn G (embedding v) t,
      b ≤ 2 * Tournament.degree (searchIn G (embedding v) t) (inComparison G) u →
        ∃ p ∈ P ∩ searchIn G (embedding v) t, inComparison G u p) :
    (searchIn F v t).card ≤ b :=
  core_child_inball_card_le G F embedding hinj P rho L v t b hcore hmono
    (fun p hp => small_radius_le hD hscale (hrho p hp)) hhit

theorem core_child_outball_shrink (G : Graph V) (F : Graph U)
    (embedding : U → V) (hinj : Function.Injective embedding)
    (P : Finset V) (rho : V → ℝ) (L : Finset V × Finset V)
    (v : U) (lambda D t : ℝ) (b : ℕ) (hD : 0 ≤ D)
    (hscale : t ≤ (lambda - 1) * D) (hrho : ∀ p ∈ P, lambda * D ≤ rho p)
    (hcore : ∀ u, embedding u ∈ coreClass G P rho L)
    (hmono : ∀ u w, G.dist (embedding u) (embedding w) ≤ F.dist u w)
    (hhit : ∀ u ∈ searchOut G (embedding v) t,
      b ≤ 2 * Tournament.degree (searchOut G (embedding v) t) (outComparison G) u →
        ∃ p ∈ P ∩ searchOut G (embedding v) t, outComparison G u p) :
    (searchOut F v t).card ≤ b :=
  core_child_outball_card_le G F embedding hinj P rho L v t b hcore hmono
    (fun p hp => small_radius_le hD hscale (hrho p hp)) hhit

theorem minimum_shell_size (G : Graph V) (p : V) (base D shift R : ℝ)
    (width : ℕ) (hw : 0 < width) (hD : 0 < D) {M : ℕ} (sigma : Fin M)
    (hR : ∀ j : Fin width, candidateRadius base width sigma j shift D + D ≤ R) :
    width * (minimumShell G p base D shift width hw sigma).card ≤
      2 * (bothBall G p R).card := by
  have hall := total_shell_size (Finset.univ : Finset (Fin width)) Fin.val
    (fun _ _ _ _ h => Fin.ext h) G p (base + (width : ℝ) * sigma.val) shift D R hD
    (by intro j _; exact hR j)
  calc
    _ = ∑ _j : Fin width, (minimumShell G p base D shift width hw sigma).card := by simp
    _ ≤ ∑ j : Fin width, (fringe G p (candidateRadius base width sigma j shift D) D).card := by
      apply Finset.sum_le_sum
      intro j _
      exact minimumIndex_le hw
        (fun j => (fringe G p (candidateRadius base width sigma j shift D) D).card) j
    _ ≤ _ := hall

theorem minimum_shell_card_le (G : Graph V) (p : V) (base D shift R : ℝ)
    (k b : ℕ) (hk : 0 < k) (hD : 0 < D) {M : ℕ} (sigma : Fin M)
    (hR : ∀ j : Fin (4 * k), candidateRadius base (4 * k) sigma j shift D + D ≤ R)
    (hb : (bothBall G p R).card ≤ 2 * b) :
    (minimumShell G p base D shift (4 * k) (by omega) sigma).card ≤ b / k := by
  have hs := minimum_shell_size G p base D shift R (4 * k) (by omega) hD sigma hR
  have hmul :
      (minimumShell G p base D shift (4 * k) (by omega) sigma).card * k ≤ b := by
    nlinarith
  exact (Nat.le_div_iff_mul_le hk).mpr hmul

theorem early_fringe_card_le (G : Graph V) (p : V)
    (k M N b : ℕ) (hk : 0 < k) (hD : 0 < D) (z : Fin M × Fin N)
    (hin : (searchIn G p (searchRadius k M D)).card ≤ b)
    (hout : (searchOut G p (searchRadius k M D)).card ≤ b) :
    (fringe G p (earlyRadius G D k M N hk p z) D).card ≤ b / k := by
  apply minimum_shell_card_le G p (lambda k M) D (shiftValue z.2)
    (searchRadius k M D) k b hk hD z.1
  · intro j
    have h := (early_candidate_bounds k M N hk hD z.1 z.2 j).2
    unfold nearRadius searchRadius at *
    linarith
  · exact (bothBall_card_le G p _).trans (by omega)

end

end StreamingSSSP.Early
