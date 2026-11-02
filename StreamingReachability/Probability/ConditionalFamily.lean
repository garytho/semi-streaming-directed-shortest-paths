module

public import StreamingReachability.Probability.Family

@[expose] public section

namespace StreamingReachability.Law

open scoped Classical BigOperators

variable {A : Type*}

theorem family_mask_transfer (n : ℕ) (mu nu : Fin n → Law A)
    (P : Fin n → A → Prop) (z : Fin n → ℝ)
    (hcomponent : ∀ i g, (mu i).expect (masked (P i) g) = z i * (nu i).expect g)
    (f : (Fin n → A) → ℝ) :
    (family n mu).expect (masked (fun xs => ∀ i, P i (xs i)) f) =
      (∏ i, z i) * (family n nu).expect f := by
  induction n with
  | zero => simp [family, masked]
  | succ n ih =>
      let muTail : Fin n → Law A := fun i => mu i.succ
      let nuTail : Fin n → Law A := fun i => nu i.succ
      let Pt : Fin n → A → Prop := fun i => P i.succ
      let zt : Fin n → ℝ := fun i => z i.succ
      let Z : ℝ := ∏ i : Fin n, zt i
      let g : A → ℝ := fun a => (family n nuTail).expect (fun xs => f (Fin.cases a xs))
      rw [expect_family_succ]
      have he :
          (fun a => (family n muTail).expect
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
          have hh := ih muTail nuTail Pt zt (fun i => hcomponent i.succ)
            (fun xs => f (Fin.cases a xs))
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
      change (mu 0).expect
          (fun a => (family n muTail).expect
            (fun xs => masked (fun ys => ∀ i, P i (ys i)) f (Fin.cases a xs))) = _
      rw [he, hcomponent 0]
      rw [expect_mul, Fin.prod_univ_succ, expect_family_succ]
      dsimp only [Z, zt, g, nuTail]
      ring

theorem expect_mask_point (mu : Law A) (a : A) (f : A → ℝ) :
    mu.expect (masked (fun x => x = a) f) = mu.prob (· = a) * f a := by
  have he : masked (fun x => x = a) f = fun x => if x = a then f a else 0 := by
    funext x
    by_cases h : x = a <;> simp [masked, h]
  rw [he, expect_ite_const mu (fun x => x = a)]
  ring

theorem family_expect_congr (n : ℕ) (mu nu : Fin n → Law A)
    (h : ∀ i g, (mu i).expect g = (nu i).expect g)
    (f : (Fin n → A) → ℝ) :
    (family n mu).expect f = (family n nu).expect f := by
  have hc : ∀ i g, (mu i).expect (masked (fun _ => True) g) =
      (1 : ℝ) * (nu i).expect g := by
    intro i g
    have hg : masked (fun _ : A => True) g = g := by
      funext a
      simp [masked]
    rw [hg, one_mul]
    exact h i g
  have hf := family_mask_transfer n mu nu (fun _ _ => True) (fun _ => 1) hc f
  have hg : masked (fun _ : Fin n → A => ∀ _i : Fin n, True) f = f := by
    funext a
    simp [masked]
  rw [hg] at hf
  simpa only [Finset.prod_const_one, one_mul] using hf

theorem expect_partition {I : Type*} (mu : Law A) (indices : Finset I)
    (key : A → I) (hkey : ∀ a, key a ∈ indices) (f : I → A → ℝ) :
    mu.expect (fun a => f (key a) a) =
      ∑ i ∈ indices, mu.expect (masked (fun a => key a = i) (f i)) := by
  have he : (fun a => ∑ i ∈ indices, masked (fun a => key a = i) (f i) a) =
      fun a => f (key a) a := by
    funext a
    simp [masked, hkey a, eq_comm]
  rw [← he, expect_finset_sum]

theorem expect_mask_comm {B : Type*} (mu : Law A) (nu : Law B) (P : A → Prop)
    (f : A → B → ℝ) :
    mu.expect (masked P (fun a => nu.expect (f a))) =
      nu.expect (fun b => mu.expect (masked P (fun a => f a b))) := by
  have he : masked P (fun a => nu.expect (f a)) =
      fun a => nu.expect (fun b => masked P (fun a => f a b) a) := by
    funext a
    by_cases h : P a <;> simp [masked, h]
  rw [he, expect_comm]

theorem expect_mask_finset_sum {I : Type*} (mu : Law A) (P : A → Prop)
    (indices : Finset I) (f : I → A → ℝ) :
    mu.expect (masked P (fun a => ∑ i ∈ indices, f i a)) =
      ∑ i ∈ indices, mu.expect (masked P (f i)) := by
  have he : masked P (fun a => ∑ i ∈ indices, f i a) =
      fun a => ∑ i ∈ indices, masked P (f i) a := by
    funext a
    by_cases h : P a <;> simp [masked, h]
  rw [he, expect_finset_sum]

theorem expect_mask_add (mu : Law A) (P : A → Prop) (f g : A → ℝ) :
    mu.expect (masked P (fun a => f a + g a)) =
      mu.expect (masked P f) + mu.expect (masked P g) := by
  have he : masked P (fun a => f a + g a) = fun a => masked P f a + masked P g a := by
    funext a
    by_cases h : P a <;> simp [masked, h]
  rw [he, expect_add]

theorem independent_indicator {B : Type*} (mu : Law A) (nu : Law B)
    (P : A → Prop) (Q : B → Prop) [DecidablePred P] [DecidablePred Q] :
    (mu.bind fun a => nu.map fun b => if P a ∧ Q b then (1 : ℝ) else 0).expect id =
      mu.prob P * nu.prob Q := by
  rw [expect_bind]
  simp_rw [expect_map]
  simp only [id_eq]
  have he : (fun a => nu.expect (fun b => if P a ∧ Q b then (1 : ℝ) else 0)) =
      fun a => if P a then nu.prob Q else 0 := by
    funext a
    by_cases h : P a
    · simp only [h, true_and, ↓reduceIte]
      exact expect_indicator nu Q
    · simp only [h, false_and, ↓reduceIte, expect_const]
  rw [he, expect_ite_const]
  ring

end StreamingReachability.Law
