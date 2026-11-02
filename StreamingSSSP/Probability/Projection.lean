module

public import StreamingSSSP.Probability.Family

@[expose] public section

namespace StreamingSSSP.Law

open scoped Classical BigOperators

variable {A B : Type*}

theorem expect_finite [Fintype A] (mu : Law A) (f : A → ℝ) :
    mu.expect f = ∑ a, mu.prob (· = a) * f a := by
  have he : f = fun x => ∑ a : A, if x = a then f a else 0 := by
    funext x
    simp
  calc
    _ = mu.expect (fun x => ∑ a : A, if x = a then f a else 0) := congrArg mu.expect he
    _ = ∑ a : A, mu.expect (fun x => if x = a then f a else 0) := expect_finset_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [expect_ite_const mu (fun x => x = a)]
      ring

theorem family_projection_probability (n m : ℕ) (mu : Fin n → Law A)
    (index : Fin m → Fin n) (hinj : Function.Injective index) (target : Fin m → A) :
    (family n mu).prob (fun xs => (fun i => xs (index i)) = target) =
      ∏ i : Fin m, (mu (index i)).prob (· = target i) := by
  let Q : Fin n → A → Prop := fun v a => ∀ i, index i = v → a = target i
  let I := (Finset.univ : Finset (Fin m)).image index
  have he : (family n mu).prob (fun xs => (fun i => xs (index i)) = target) =
      (family n mu).prob (fun xs => ∀ v, Q v (xs v)) := by
    apply prob_congr
    intro xs
    constructor
    · intro h v i hi
      rw [← hi]
      exact congrFun h i
    · intro h
      funext i
      exact h (index i) i rfl
  rw [he, family_probability]
  calc
    _ = ∏ v ∈ I, (mu v).prob (Q v) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ I)
      intro v _ hv
      apply (prob_congr _ _ (fun _ => True) ?_).trans (prob_true _)
      intro a
      constructor
      · intro _; trivial
      · intro _ i hi
        exact False.elim (hv (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
    _ = ∏ i : Fin m, (mu (index i)).prob (Q (index i)) :=
      Finset.prod_image (fun _ _ _ _ h => hinj h)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      apply prob_congr
      intro a
      constructor
      · intro h
        exact h i rfl
      · intro h j hj
        have hji : j = i := hinj hj
        simpa only [hji] using h

theorem family_projection [Fintype A] (n m : ℕ) (mu : Fin n → Law A)
    (index : Fin m → Fin n) (hinj : Function.Injective index)
    (f : (Fin m → A) → ℝ) :
    (family n mu).expect (fun xs => f (fun i => xs (index i))) =
      (family m (fun i => mu (index i))).expect f := by
  rw [← expect_map (family n mu) (fun xs => fun i => xs (index i)) f,
    expect_finite, expect_finite]
  apply Finset.sum_congr rfl
  intro target _
  congr 1
  rw [prob_map, family_projection_probability n m mu index hinj]
  have h := family_projection_probability m m (fun i => mu (index i))
    (fun i => i) Function.injective_id target
  exact h.symm

theorem family_map (n : ℕ) (mu : Fin n → Law A) (g : Fin n → A → B)
    (f : (Fin n → B) → ℝ) :
    (family n mu).expect (fun xs => f (fun i => g i (xs i))) =
      (family n (fun i => (mu i).map (g i))).expect f := by
  induction n with
  | zero =>
      simp only [family, expect_pure]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [expect_family_succ, expect_family_succ, expect_map]
      apply congrArg (mu 0).expect
      funext a
      have he :
          (fun xs : Fin n → A => f (fun i => g i (Fin.cases a xs i))) =
            fun xs => f (Fin.cases (g 0 a) (fun i => g i.succ (xs i))) := by
        funext xs
        congr 1
        funext i
        refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
      rw [he]
      exact ih (fun i => mu i.succ) (fun i => g i.succ) (fun xs => f (Fin.cases (g 0 a) xs))

theorem family_reindex_finite [Fintype A] {I : Type*} [Fintype I] (n m : ℕ)
    (mu : Law A) (left : I → Fin n) (right : I → Fin m)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (f : (I → A) → ℝ) :
    (family n (fun _ => mu)).expect (fun xs => f (fun i => xs (left i))) =
      (family m (fun _ => mu)).expect (fun xs => f (fun i => xs (right i))) := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let g : (Fin (Fintype.card I) → A) → ℝ := fun xs => f (fun i => xs (e.symm i))
  have heL :
      (fun xs : Fin n → A => f (fun i => xs (left i))) =
        fun xs => g (fun j => xs (left (e j))) := by
    simp only [g, Equiv.apply_symm_apply]
  have heR :
      (fun xs : Fin m → A => f (fun i => xs (right i))) =
        fun xs => g (fun j => xs (right (e j))) := by
    simp only [g, Equiv.apply_symm_apply]
  rw [heL, heR, family_projection n (Fintype.card I) (fun _ => mu)
    (fun j => left (e j)) (hl.comp e.injective) g,
    family_projection m (Fintype.card I) (fun _ => mu)
      (fun j => right (e j)) (hr.comp e.injective) g]

theorem family_subset_pullback [Fintype A] (n m : ℕ) (mu : Law A)
    (S : Finset (Fin n)) (index : {v : Fin n // v ∈ S} → Fin m)
    (hinj : Function.Injective index) (fallback : A) (f : (Fin n → A) → ℝ)
    (hdepends : ∀ xs ys, (∀ v ∈ S, xs v = ys v) → f xs = f ys) :
    (family m (fun _ => mu)).expect
        (fun xs => f (fun v => if hv : v ∈ S then xs (index ⟨v, hv⟩) else fallback)) =
      (family n (fun _ => mu)).expect f := by
  have h := family_reindex_finite m n mu index (fun v : {v : Fin n // v ∈ S} => v.val)
    hinj Subtype.val_injective
    (fun xs => f (fun v => if hv : v ∈ S then xs ⟨v, hv⟩ else fallback))
  apply h.trans
  apply congrArg (family n (fun _ => mu)).expect
  funext xs
  apply hdepends
  intro v hv
  simp only [hv, ↓reduceDIte]

end StreamingSSSP.Law
