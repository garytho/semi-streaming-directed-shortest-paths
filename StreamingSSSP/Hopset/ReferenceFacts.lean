module

public import StreamingSSSP.Hopset.Reference

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical
open Early

noncomputable section

variable {n : ℕ}

theorem holds_bind_on {A B : Type*} (mu : Law A) (f : A → Law B) (P : A → Prop) (Q : B → Prop)
    (hmu : Sampling.Holds mu P) (hf : ∀ a, P a → Sampling.Holds (f a) Q) :
    Sampling.Holds (mu.bind f) Q := by
  intro z hz
  obtain ⟨a, ha, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
  exact hf a.1 (hmu a ha) b hb

theorem family_holds {A : Type*} (m : ℕ) (mu : Fin m → Law A) (P : Fin m → A → Prop)
    (h : ∀ i, Sampling.Holds (mu i) (P i)) :
    Sampling.Holds (Law.family m mu) (fun xs => ∀ i, P i (xs i)) := by
  induction m with
  | zero =>
      apply Sampling.holds_pure
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      rw [Law.family]
      refine holds_bind_on (mu 0)
        (fun a => (Law.family m (fun i => mu i.succ)).map
          (fun xs : Fin m → A => fun i : Fin (m + 1) => Fin.cases a xs i))
        (P 0) (fun xs : Fin (m + 1) → A => ∀ i, P i (xs i)) (h 0) ?_
      intro a ha
      refine Sampling.holds_map
        (ih (fun i => mu i.succ) (fun i => P i.succ) (fun i => h i.succ))
        (fun xs : Fin m → A => fun i : Fin (m + 1) => Fin.cases a xs i)
        (fun xs : Fin (m + 1) → A => ∀ i, P i (xs i)) ?_
      intro xs hxs i
      exact Fin.cases ha (fun j => hxs j) i

theorem expect_congr_on {A : Type*} (mu : Law A) (f g : A → ℝ)
    (h : Sampling.Holds mu (fun a => f a = g a)) : mu.expect f = mu.expect g := by
  apply le_antisymm
  · apply Sampling.expect_mono_on
    intro z hz
    exact (h z hz).le
  · apply Sampling.expect_mono_on
    intro z hz
    exact (h z hz).ge

theorem subset_holds (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (vertices : List (Fin n)) :
    Sampling.Holds (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) vertices)
      (fun P => P ⊆ vertices.toFinset) := by
  induction vertices with
  | nil => exact Sampling.holds_pure _ _ (by simp)
  | cons v vertices ih =>
      unfold Law.subset
      apply Sampling.holds_bind
      intro hit
      cases hit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, List.toFinset_cons]
          refine Sampling.holds_mono ih ?_
          intro P hP w hw
          exact Finset.mem_insert_of_mem (hP hw)
      | true =>
          simp only [↓reduceIte, List.toFinset_cons]
          refine Sampling.holds_map ih
            (@insert (Fin n) (Finset (Fin n))
              (@Finset.instInsert _ (fun a b => Classical.propDecidable (a = b))) v)
            (fun P => P ⊆ insert v vertices.toFinset) ?_
          intro P hP w hw
          simp only [Finset.mem_insert] at hw
          rcases hw with rfl | hw
          · simp
          · exact Finset.mem_insert_of_mem (hP hw)

theorem pivotLaw_subset (cfg : Config) (hn : 0 < n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) :
    Sampling.Holds (pivotLaw cfg hn r S ranks) (fun P => P ⊆ S) := by
  unfold pivotLaw
  split_ifs
  · exact Sampling.holds_pure _ _ (Finset.filter_subset _ _)
  · have h := subset_holds (PivotProfile.rate n hn cfg.k cfg.logarithm r).value
      (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg
      (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one (members S)
    simpa only [members_toFinset] using h
  · exact Sampling.holds_pure _ _ (Finset.Subset.refl _)

theorem choices_subset (cfg : Config) (hn : 0 < n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) :
    Sampling.Holds (choices cfg hn r S ranks) (fun choice => choice.pivots ⊆ S) := by
  unfold choices
  refine holds_bind_on _ _ _ _ (pivotLaw_subset cfg hn r S ranks) ?_
  intro P hP
  apply Sampling.holds_map (mu := ownerLaw n cfg) (P := fun _ => True)
    (by intro _ _; trivial) (fun owners => (⟨P, owners⟩ : Choice n cfg))
  intro owners _
  exact hP

theorem kernel_pivots_subset (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (r : ℕ) (S : Finset (Fin n)) :
    Sampling.Holds (kernel cfg hn stored input ranks r S)
      (fun step => step.value.pivots ⊆ S) :=
  Sampling.holds_map (choices_subset cfg hn r S ranks)
    (fun choice => (⟨choice, children cfg stored input r S choice⟩ :
      Branching.Step (Finset (Fin n)) (Choice n cfg))) _ (fun _ h => h)

theorem distanceScale_pos (cfg : Config) (hnum : 0 < cfg.initialNumerator) (r : ℕ) :
    0 < distanceScale cfg r := by
  have hd := cfg.denominatorAt_pos r
  unfold distanceScale
  positivity

theorem radii_lower_scale (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (G : Graph (Fin n)) (owners : Owners n cfg) (p : Fin n) :
    distanceScale cfg r ≤ radii cfg r G owners p := by
  have hD := distanceScale_pos cfg hnum r
  have hk : (1 : ℝ) ≤ cfg.k := by exact_mod_cast cfg.k_pos
  have hM : (1 : ℝ) ≤ cfg.groups := by exact_mod_cast cfg.groups_pos
  have hl : 1 ≤ Early.lambda cfg.k cfg.groups := by
    unfold Early.lambda
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hM)]
  have hr := (Late.radius_bounds G (distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos
    hD p (owners p)).1
  have hmul := mul_nonneg (sub_nonneg.mpr hl) hD.le
  exact (by nlinarith : distanceScale cfg r ≤ Early.lambda cfg.k cfg.groups * distanceScale cfg r).trans hr

theorem radii_nonneg (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (G : Graph (Fin n)) (owners : Owners n cfg) (p : Fin n) :
    0 ≤ radii cfg r G owners p :=
  (distanceScale_pos cfg hnum r).le.trans (radii_lower_scale cfg hnum r G owners p)

theorem lateChild_class (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) :
    ∀ v ∈ lateChild G S P rho, v ∈ Early.coreClass G P rho (∅, ∅) := by
  intro v hv
  have hlabels := (Finset.mem_filter.mp hv).2
  have hin (p : Fin n) (hp : p ∈ P) : ¬ Early.Within G v p (rho p) := by
    intro h
    have ht := (Geometry.label_even G P rho p v).mpr ⟨hp, h⟩
    rw [hlabels] at ht
    simp at ht
  have hout (p : Fin n) (hp : p ∈ P) : ¬ Early.Within G p v (rho p) := by
    intro h
    have ht := (Geometry.label_odd G P rho p v).mpr ⟨hp, h⟩
    rw [hlabels] at ht
    simp at ht
  refine ⟨?_, ?_⟩
  · intro p hp h
    exact hin p hp h.1
  · apply Prod.ext <;> ext p
    · simp [Early.labels]
      exact hin p
    · simp [Early.labels]
      exact hout p

end

end StreamingSSSP.Hopset.Reference
