module

public import StreamingSSSP.Probability.Conditioning

@[expose] public section

namespace StreamingSSSP.Law

open scoped Classical BigOperators

variable {A : Type*}

noncomputable def family : (n : ℕ) → (Fin n → Law A) → Law (Fin n → A)
  | 0, _ => pure Fin.elim0
  | n + 1, μ =>
      (μ 0).bind fun a => (family n (fun i => μ i.succ)).map (Fin.cases a)

theorem expect_family_succ (n : ℕ) (μ : Fin (n + 1) → Law A)
    (f : (Fin (n + 1) → A) → ℝ) :
    (family (n + 1) μ).expect f =
      (μ 0).expect (fun a => (family n (fun i => μ i.succ)).expect
        (fun xs => f (Fin.cases a xs))) := by
  rw [family, expect_bind]
  simp_rw [expect_map]

theorem family_mask_factor (n : ℕ) (μ : Fin n → Law A) (P : Fin n → A → Prop)
    (f : (Fin n → A) → ℝ) :
    (family n μ).expect (masked (fun xs => ∀ i, P i (xs i)) f) =
      (∏ i, (μ i).prob (P i)) * (family n (fun i => (μ i).given (P i))).expect f := by
  induction n with
  | zero => simp [family, masked]
  | succ n ih =>
      let μt : Fin n → Law A := fun i => μ i.succ
      let Pt : Fin n → A → Prop := fun i => P i.succ
      let νt : Fin n → Law A := fun i => (μ i.succ).given (P i.succ)
      let Z : ℝ := ∏ i : Fin n, (μ i.succ).prob (P i.succ)
      let g : A → ℝ := fun a => (family n νt).expect (fun xs => f (Fin.cases a xs))
      rw [expect_family_succ]
      have he :
          (fun a => (family n μt).expect
            (fun xs => masked (fun ys => ∀ i, P i (ys i)) f (Fin.cases a xs))) =
              masked (P 0) (fun a => Z * g a) := by
        funext a
        by_cases ha : P 0 a
        · have hf : (fun xs : Fin n → A =>
              masked (fun ys => ∀ i, P i (ys i)) f (Fin.cases a xs)) =
                masked (fun xs => ∀ i : Fin n, Pt i (xs i))
                  (fun xs => f (Fin.cases a xs)) := by
            funext xs
            simp [masked, Fin.forall_fin_succ, Pt, ha]
          rw [hf]
          have hh := ih μt Pt (fun xs => f (Fin.cases a xs))
          simpa only [masked, ha, ↓reduceIte] using hh
        · have hf : (fun xs : Fin n → A =>
              masked (fun ys => ∀ i, P i (ys i)) f (Fin.cases a xs)) = fun _ => 0 := by
            funext xs
            have hn : ¬ ∀ i, P i (Fin.cases a xs i) := by
              intro h
              exact ha (h 0)
            simp [masked, hn]
          rw [hf, expect_const]
          simp [masked, ha]
      change (μ 0).expect
          (fun a => (family n μt).expect
            (fun xs => masked (fun ys => ∀ i, P i (ys i)) f (Fin.cases a xs))) = _
      rw [he, expect_mask_mul, expect_mask_eq]
      rw [Fin.prod_univ_succ, expect_family_succ]
      ring

theorem family_probability (n : ℕ) (μ : Fin n → Law A) (P : Fin n → A → Prop) :
    (family n μ).prob (fun xs => ∀ i, P i (xs i)) = ∏ i, (μ i).prob (P i) := by
  change (family n μ).expect (masked (fun xs => ∀ i, P i (xs i)) (fun _ => 1)) = _
  rw [family_mask_factor, expect_const, mul_one]

theorem family_mask_probability (n : ℕ) (μ : Fin n → Law A)
    (P : Fin n → A → Prop) (Q : (Fin n → A) → Prop) :
    (family n μ).prob (fun xs => (∀ i, P i (xs i)) ∧ Q xs) =
      (∏ i, (μ i).prob (P i)) * (family n (fun i => (μ i).given (P i))).prob Q := by
  simp only [prob_eq_mask]
  rw [← masked_mask, family_mask_factor]
  simp only [← prob_eq_mask]

theorem family_marginal (n : ℕ) (μ : Fin n → Law A) (i : Fin n) (f : A → ℝ) :
    (family n μ).expect (fun xs => f (xs i)) = (μ i).expect f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [expect_family_succ]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp only [Fin.cases_succ]
        rw [ih (fun k => μ k.succ) j, expect_const]

theorem family_marginal_probability (n : ℕ) (μ : Fin n → Law A) (i : Fin n)
    (P : A → Prop) :
    (family n μ).prob (fun xs => P (xs i)) = (μ i).prob P :=
  family_marginal n μ i (fun a => if P a then 1 else 0)

theorem family_avoid (n : ℕ) (μ : Fin n → Law A) (S : Finset (Fin n))
    (P : Fin n → A → Prop) :
    (family n μ).prob (fun xs => ∀ i ∈ S, ¬ P i (xs i)) =
      ∏ i ∈ S, (1 - (μ i).prob (P i)) := by
  let Q : Fin n → A → Prop := fun i a => if i ∈ S then ¬ P i a else True
  have he : (fun xs : Fin n → A => ∀ i, Q i (xs i)) =
      fun xs => ∀ i ∈ S, ¬ P i (xs i) := by
    funext xs
    apply propext
    constructor
    · intro h i hi
      simpa only [Q, hi, ↓reduceIte] using h i
    · intro h i
      by_cases hi : i ∈ S <;> simp [Q, hi, h]
  rw [← he, family_probability]
  have hp (i : Fin n) :
      (μ i).prob (Q i) = if i ∈ S then 1 - (μ i).prob (P i) else 1 := by
    by_cases hi : i ∈ S
    · have hq : Q i = fun a => ¬ P i a := by funext a; simp [Q, hi]
      rw [hq, prob_compl]
      simp [hi]
    · have hq : Q i = fun _ => True := by funext a; simp [Q, hi]
      rw [hq, prob_true]
      simp [hi]
  simp_rw [hp]
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

theorem family_avoid_exp (n : ℕ) (μ : Fin n → Law A) (S : Finset (Fin n))
    (P : Fin n → A → Prop) (q : ℝ)
    (h : ∀ i ∈ S, q ≤ (μ i).prob (P i)) :
    (family n μ).prob (fun xs => ∀ i ∈ S, ¬ P i (xs i)) ≤
      Real.exp (-q * S.card) := by
  rw [family_avoid]
  have hb : 1 - q ≤ Real.exp (-q) := by linarith [Real.add_one_le_exp (-q)]
  calc
    (∏ i ∈ S, (1 - (μ i).prob (P i))) ≤ ∏ _i ∈ S, Real.exp (-q) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact sub_nonneg.mpr ((μ i).prob_le_one (P i))
      · intro i hi
        exact (sub_le_sub_left (h i hi) 1).trans hb
    _ = Real.exp (-q) ^ S.card := by simp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end StreamingSSSP.Law
