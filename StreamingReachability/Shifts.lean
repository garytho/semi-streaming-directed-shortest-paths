module

public import StreamingReachability.Probability.Uniform

@[expose] public section

namespace StreamingReachability.Shifts

open scoped Classical BigOperators

theorem grid_card_bound (A : Finset ℕ) (base gap lo hi : ℝ)
    (hgap : 0 < gap) (hrange : lo ≤ hi)
    (hA : ∀ i ∈ A, lo ≤ base + gap * i ∧ base + gap * i ≤ hi) :
    (A.card : ℝ) ≤ (hi - lo) / gap + 1 := by
  by_cases he : A.Nonempty
  · let a := A.min' he
    let b := A.max' he
    have ha : a ∈ A := Finset.min'_mem _ _
    have hb : b ∈ A := Finset.max'_mem _ _
    have hab : a ≤ b := Finset.min'_le _ _ hb
    have hsub : A ⊆ Finset.Icc a b := by
      intro i hiA
      exact Finset.mem_Icc.mpr
        ⟨Finset.min'_le _ _ hiA, Finset.le_max' _ _ hiA⟩
    have hc : A.card ≤ b - a + 1 := by
      have hh := Finset.card_le_card hsub
      rw [Nat.card_Icc] at hh
      omega
    have hc' : (A.card : ℝ) ≤ (b : ℝ) - a + 1 := by
      have hh : (A.card : ℝ) ≤ ((b - a + 1 : ℕ) : ℝ) := by exact_mod_cast hc
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hab] using hh
    have hwidth : ((b : ℝ) - a) * gap ≤ hi - lo := by
      have hla := (hA a ha).1
      have hhb := (hA b hb).2
      nlinarith
    have hprod : ((A.card : ℝ) - 1) * gap ≤ hi - lo :=
      (mul_le_mul_of_nonneg_right (by linarith : (A.card : ℝ) - 1 ≤ b - a)
        hgap.le).trans hwidth
    have hh := (le_div_iff₀ hgap).mpr hprod
    linarith
  · have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

theorem mapped_grid_card_bound {A : Type*} (S : Finset A) (f : A → ℕ)
    (hf : Set.InjOn f S) (base gap lo hi : ℝ)
    (hgap : 0 < gap) (hrange : lo ≤ hi)
    (hS : ∀ i ∈ S, lo ≤ base + gap * f i ∧ base + gap * f i ≤ hi) :
    (S.card : ℝ) ≤ (hi - lo) / gap + 1 := by
  have h := grid_card_bound (S.image f) base gap lo hi hgap hrange (by
    intro j hj
    obtain ⟨i, hiS, rfl⟩ := Finset.mem_image.mp hj
    exact hS i hiS)
  simpa only [Finset.card_image_of_injOn hf] using h

theorem uniform_window_bound {n : ℕ} (hn : 0 < n) (f : Fin n → ℕ)
    (hf : Function.Injective f) (base gap lo hi : ℝ)
    (hgap : 0 < gap) (hrange : lo ≤ hi) :
    (Law.uniform n hn).prob (fun i =>
        lo ≤ base + gap * f i ∧ base + gap * f i ≤ hi) ≤
      ((hi - lo) / gap + 1) / (n : ℝ) := by
  rw [Law.prob_uniform]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mapped_grid_card_bound _ f (fun _ _ _ _ h => hf h)
    base gap lo hi hgap hrange (by
      intro i hiS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiS
      exact hiS)

def pointIndex (width groups shifts : ℕ) (candidate : Fin groups → Fin shifts → Fin width)
    (σ : Fin groups) (φ : Fin shifts) : ℕ :=
  (width * σ.val + (candidate σ φ).val) * shifts + φ.val

theorem pointIndex_injective (width groups shifts : ℕ)
    (hw : 0 < width) (hs : 0 < shifts)
    (candidate : Fin groups → Fin shifts → Fin width) :
    Function.Injective (fun z : Fin groups × Fin shifts =>
      pointIndex width groups shifts candidate z.1 z.2) := by
  intro z z' he
  rcases z with ⟨σ, φ⟩
  rcases z' with ⟨σ', φ'⟩
  have hrem (a : ℕ) (i : Fin shifts) : (a * shifts + i.val) % shifts = i.val := by
    rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt i.isLt]
  have hmod := congrArg (fun q => q % shifts) he
  dsimp only [pointIndex] at hmod
  rw [hrem, hrem] at hmod
  have hφ : φ = φ' := Fin.ext hmod
  subst φ'
  have hq : width * σ.val + (candidate σ φ).val =
      width * σ'.val + (candidate σ' φ).val := by
    have hh : (width * σ.val + (candidate σ φ).val) * shifts =
        (width * σ'.val + (candidate σ' φ).val) * shifts :=
      Nat.add_right_cancel he
    exact Nat.eq_of_mul_eq_mul_right hs hh
  have hσ : σ = σ' := by
    apply Fin.ext
    have hdiv := congrArg (fun q => q / width) hq
    simpa only [Nat.mul_add_div hw, Nat.div_eq_of_lt (candidate σ φ).isLt,
      Nat.div_eq_of_lt (candidate σ' φ).isLt, Nat.add_zero] using hdiv
  subst σ'
  rfl

theorem chosen_window_bound (width groups shifts : ℕ)
    (hw : 0 < width) (hg : 0 < groups) (hs : 0 < shifts)
    (candidate : Fin groups → Fin shifts → Fin width) (base D lo hi : ℝ)
    (hD : 0 < D) (hrange : lo ≤ hi) :
    (Law.uniformPair groups shifts hg hs).prob (fun z =>
      lo ≤ base + (D / shifts) * pointIndex width groups shifts candidate z.1 z.2 ∧
        base + (D / shifts) * pointIndex width groups shifts candidate z.1 z.2 ≤ hi) ≤
      ((hi - lo) * shifts / D + 1) / ((groups : ℝ) * shifts) := by
  rw [Law.prob_uniformPair]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (hi - lo) / (D / shifts) + 1 :=
      mapped_grid_card_bound _
        (fun z => pointIndex width groups shifts candidate z.1 z.2)
        (fun _ _ _ _ he => pointIndex_injective width groups shifts hw hs candidate he)
        base (D / shifts) lo hi (by positivity) hrange (by
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          exact hz)
    _ = _ := by rw [div_div_eq_mul_div]

theorem window_charge (width groups shifts : ℕ)
    (hw : 0 < width) (hg : 0 < groups) (hs : 0 < shifts)
    (candidate : Fin groups → Fin shifts → Fin width) (base D lo hi : ℝ)
    (hD : 0 < D) (hwide : D / shifts ≤ hi - lo) :
    (Law.uniformPair groups shifts hg hs).prob (fun z =>
      lo ≤ base + (D / shifts) * pointIndex width groups shifts candidate z.1 z.2 ∧
        base + (D / shifts) * pointIndex width groups shifts candidate z.1 z.2 ≤ hi) ≤
      2 * (hi - lo) / ((groups : ℝ) * D) := by
  have hs' : (0 : ℝ) < shifts := by exact_mod_cast hs
  have hg' : (0 : ℝ) < groups := by exact_mod_cast hg
  have hlen : 0 ≤ hi - lo := (le_of_lt (div_pos hD hs')).trans hwide
  have hcount := chosen_window_bound width groups shifts hw hg hs candidate
    base D lo hi hD (by linarith)
  apply hcount.trans
  have hone : 1 ≤ (hi - lo) * shifts / D := by
    apply (le_div_iff₀ hD).mpr
    have hh := (div_le_iff₀ hs').mp hwide
    linarith
  apply (div_le_iff₀ (mul_pos hg' hs')).mpr
  have he : 2 * (hi - lo) / ((groups : ℝ) * D) * ((groups : ℝ) * shifts) =
      2 * ((hi - lo) * shifts / D) := by field_simp [ne_of_gt hg', ne_of_gt hD]
  rw [he]
  linarith

end StreamingReachability.Shifts
