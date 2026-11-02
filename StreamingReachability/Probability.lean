module

public import Mathlib

@[expose] public section

namespace StreamingReachability

open scoped Classical

def weightedSum {A : Type*} (xs : List (A × ℝ)) (f : A → ℝ) : ℝ :=
  (xs.map fun z => z.2 * f z.1).sum

@[simp] theorem weightedSum_nil {A : Type*} (f : A → ℝ) :
    weightedSum [] f = 0 := rfl

@[simp] theorem weightedSum_cons {A : Type*} (z : A × ℝ)
    (xs : List (A × ℝ)) (f : A → ℝ) :
    weightedSum (z :: xs) f = z.2 * f z.1 + weightedSum xs f := rfl

theorem weightedSum_add {A : Type*} (xs : List (A × ℝ)) (f g : A → ℝ) :
    weightedSum xs (fun a => f a + g a) =
      weightedSum xs f + weightedSum xs g := by
  induction xs with
  | nil => simp
  | cons z xs ih => simp only [weightedSum_cons, mul_add, ih]; ring

theorem weightedSum_sub {A : Type*} (xs : List (A × ℝ)) (f g : A → ℝ) :
    weightedSum xs (fun a => f a - g a) =
      weightedSum xs f - weightedSum xs g := by
  induction xs with
  | nil => simp
  | cons z xs ih => simp only [weightedSum_cons, mul_sub, ih]; ring

theorem weightedSum_mul {A : Type*} (xs : List (A × ℝ)) (f : A → ℝ) (c : ℝ) :
    weightedSum xs (fun a => c * f a) = c * weightedSum xs f := by
  induction xs with
  | nil => simp
  | cons z xs ih => simp only [weightedSum_cons, ih]; ring

theorem weightedSum_nonneg {A : Type*} (xs : List (A × ℝ)) (f : A → ℝ)
    (hw : ∀ z ∈ xs, 0 ≤ z.2) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ weightedSum xs f := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
      exact add_nonneg (mul_nonneg (hw z (by simp)) (hf _))
        (ih (fun a ha => hw a (by simp [ha])))

theorem weightedSum_map {A B : Type*} (xs : List (A × ℝ)) (f : A → B)
    (g : B → ℝ) :
    weightedSum (xs.map fun z => (f z.1, z.2)) g =
      weightedSum xs (fun a => g (f a)) := by
  simp [weightedSum, List.map_map, Function.comp_def]

theorem weightedSum_append {A : Type*} (xs ys : List (A × ℝ)) (f : A → ℝ) :
    weightedSum (xs ++ ys) f = weightedSum xs f + weightedSum ys f := by
  simp [weightedSum]

theorem weightedSum_scale {A : Type*} (xs : List (A × ℝ)) (c : ℝ) (f : A → ℝ) :
    weightedSum (xs.map fun z => (z.1, c * z.2)) f =
      c * weightedSum xs f := by
  induction xs with
  | nil => simp [weightedSum]
  | cons z xs ih => simp only [List.map_cons, weightedSum_cons, ih]; ring

structure Law (A : Type*) where
  atoms : List (A × ℝ)
  nonneg : ∀ z ∈ atoms, 0 ≤ z.2
  total : weightedSum atoms (fun _ => 1) = 1

namespace Law

variable {A B C : Type*}

def expect (μ : Law A) (f : A → ℝ) : ℝ := weightedSum μ.atoms f

noncomputable def prob (μ : Law A) (P : A → Prop) : ℝ :=
  μ.expect fun a => if P a then 1 else 0

def pure (a : A) : Law A where
  atoms := [(a, 1)]
  nonneg := by simp
  total := by simp [weightedSum]

def map (μ : Law A) (f : A → B) : Law B where
  atoms := μ.atoms.map fun z => (f z.1, z.2)
  nonneg := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact μ.nonneg a ha
  total := by simpa only [weightedSum_map] using μ.total

def bind (μ : Law A) (f : A → Law B) : Law B where
  atoms := μ.atoms.flatMap fun z =>
    (f z.1).atoms.map fun a => (a.1, z.2 * a.2)
  nonneg := by
    intro z hz
    obtain ⟨a, ha, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (μ.nonneg a ha) ((f a.1).nonneg b hb)
  total := by
    have h : ∀ xs : List (A × ℝ),
        weightedSum (xs.flatMap fun z =>
          (f z.1).atoms.map fun a => (a.1, z.2 * a.2)) (fun _ => 1) =
            weightedSum xs (fun _ => 1) := by
      intro xs
      induction xs with
      | nil => simp
      | cons z xs ih =>
          simp only [List.flatMap_cons, weightedSum_append, weightedSum_scale,
            (f z.1).total, mul_one, ih, weightedSum_cons]
    exact (h μ.atoms).trans μ.total

@[simp] theorem expect_pure (a : A) (f : A → ℝ) :
    (pure a).expect f = f a := by
  simp [expect, pure, weightedSum]

theorem expect_map (μ : Law A) (f : A → B) (g : B → ℝ) :
    (μ.map f).expect g = μ.expect (fun a => g (f a)) :=
  weightedSum_map _ _ _

theorem expect_bind (μ : Law A) (f : A → Law B) (g : B → ℝ) :
    (μ.bind f).expect g = μ.expect (fun a => (f a).expect g) := by
  change weightedSum (μ.atoms.flatMap _) g = weightedSum μ.atoms _
  induction μ.atoms with
  | nil => simp
  | cons z xs ih =>
      simp only [List.flatMap_cons, weightedSum_append, weightedSum_scale, ih,
        weightedSum_cons, expect]

@[simp] theorem expect_const (μ : Law A) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  have h := weightedSum_mul μ.atoms (fun _ => (1 : ℝ)) c
  simpa only [expect, mul_one, μ.total] using h

theorem expect_add (μ : Law A) (f g : A → ℝ) :
    μ.expect (fun a => f a + g a) = μ.expect f + μ.expect g :=
  weightedSum_add _ _ _

theorem expect_sub (μ : Law A) (f g : A → ℝ) :
    μ.expect (fun a => f a - g a) = μ.expect f - μ.expect g :=
  weightedSum_sub _ _ _

theorem expect_mul (μ : Law A) (c : ℝ) (f : A → ℝ) :
    μ.expect (fun a => c * f a) = c * μ.expect f :=
  weightedSum_mul _ _ _

theorem expect_finset_sum {I : Type*} (μ : Law A) (S : Finset I) (f : I → A → ℝ) :
    μ.expect (fun a => ∑ i ∈ S, f i a) = ∑ i ∈ S, μ.expect (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi, expect_add, ih]

theorem expect_comm (μ : Law A) (ν : Law B) (f : A → B → ℝ) :
    μ.expect (fun a => ν.expect (f a)) =
      ν.expect (fun b => μ.expect (fun a => f a b)) := by
  have h (xs : List (A × ℝ)) :
      weightedSum xs (fun a => ν.expect (f a)) =
        ν.expect (fun b => weightedSum xs (fun a => f a b)) := by
    induction xs with
    | nil => simp
    | cons z xs ih =>
        simp only [weightedSum_cons, expect_add, expect_mul, ih]
  exact h μ.atoms

theorem expect_indicator (μ : Law A) (P : A → Prop) [DecidablePred P] :
    μ.expect (fun a => if P a then (1 : ℝ) else 0) = μ.prob P := by
  unfold prob
  congr 1
  funext a
  by_cases h : P a <;> simp [h]

theorem expect_ite_const (μ : Law A) (P : A → Prop) [DecidablePred P] (c : ℝ) :
    μ.expect (fun a => if P a then c else 0) = c * μ.prob P := by
  have he : (fun a => if P a then c else 0) =
      fun a => c * if P a then (1 : ℝ) else 0 := by
    funext a
    by_cases h : P a <;> simp [h]
  rw [he, expect_mul, expect_indicator]

theorem expect_nonneg (μ : Law A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) :
    0 ≤ μ.expect f :=
  weightedSum_nonneg _ _ μ.nonneg hf

theorem expect_mono (μ : Law A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    μ.expect f ≤ μ.expect g := by
  have hh := μ.expect_nonneg (fun a => g a - f a) (fun a => sub_nonneg.mpr (h a))
  rw [μ.expect_sub] at hh
  linarith

theorem prob_nonneg (μ : Law A) (P : A → Prop) : 0 ≤ μ.prob P :=
  μ.expect_nonneg _ (by intro a; split_ifs <;> norm_num)

theorem prob_mono (μ : Law A) {P Q : A → Prop} (h : ∀ a, P a → Q a) :
    μ.prob P ≤ μ.prob Q := by
  apply μ.expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

@[simp] theorem prob_true (μ : Law A) : μ.prob (fun _ => True) = 1 := by
  simp [prob]

@[simp] theorem prob_false (μ : Law A) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_le_one (μ : Law A) (P : A → Prop) : μ.prob P ≤ 1 := by
  simpa using μ.prob_mono (P := P) (Q := fun _ => True) (by simp)

theorem prob_compl (μ : Law A) (P : A → Prop) :
    μ.prob (fun a => ¬ P a) = 1 - μ.prob P := by
  have h : μ.prob P + μ.prob (fun a => ¬ P a) = 1 := by
    rw [prob, prob, ← expect_add]
    convert μ.expect_const 1 using 1
    congr 1
    funext a
    by_cases hp : P a <;> simp [hp]
  linarith

theorem prob_union (μ : Law A) (P Q : A → Prop) :
    μ.prob (fun a => P a ∨ Q a) ≤ μ.prob P + μ.prob Q := by
  rw [prob, prob, prob, ← expect_add]
  apply μ.expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [hp, hq]

theorem prob_map (μ : Law A) (f : A → B) (P : B → Prop) :
    (μ.map f).prob P = μ.prob (fun a => P (f a)) :=
  expect_map _ _ _

theorem prob_bind (μ : Law A) (f : A → Law B) (P : B → Prop) :
    (μ.bind f).prob P = μ.expect (fun a => (f a).prob P) :=
  expect_bind _ _ _

theorem prob_congr (μ : Law A) (P Q : A → Prop) (h : ∀ a, P a ↔ Q a) :
    μ.prob P = μ.prob Q := by
  have he : P = Q := funext fun a => propext (h a)
  rw [he]

theorem finite_union (μ : Law A) {I : Type*} (S : Finset I) (P : I → A → Prop) :
    μ.prob (fun a => ∃ i ∈ S, P i a) ≤ ∑ i ∈ S, μ.prob (P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [prob]
  | @insert i S hi ih =>
      have he : μ.prob (fun a => ∃ j ∈ insert i S, P j a) =
          μ.prob (fun a => P i a ∨ ∃ j ∈ S, P j a) :=
        μ.prob_congr _ _ (by intro a; simp)
      rw [he, Finset.sum_insert hi]
      exact (μ.prob_union _ _).trans (add_le_add le_rfl ih)

theorem markov (μ : Law A) (f : A → ℝ) (hf : ∀ a, 0 ≤ f a)
    (t : ℝ) (ht : 0 < t) :
    μ.prob (fun a => t ≤ f a) ≤ μ.expect f / t := by
  have h : t * μ.prob (fun a => t ≤ f a) ≤ μ.expect f := by
    rw [prob, ← expect_mul]
    apply μ.expect_mono
    intro a
    by_cases ha : t ≤ f a <;> simp [ha, hf a]
  exact (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using h)

def coin (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) : Law Bool where
  atoms := [(false, 1 - p), (true, p)]
  nonneg := by
    intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact sub_nonneg.mpr hp'
    · have he := List.mem_singleton.mp hz
      subst z
      exact hp
  total := by simp [weightedSum]

theorem expect_coin (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (f : Bool → ℝ) :
    (coin p hp hp').expect f = (1 - p) * f false + p * f true := by
  simp [coin, expect, weightedSum]

theorem prob_coin_true (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (coin p hp hp').prob (fun b => b = true) = p := by
  simp [prob, expect_coin]

theorem prob_coin_false (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (coin p hp hp').prob (fun b => b = false) = 1 - p := by
  simp [prob, expect_coin]

theorem expect_indicator_mul (μ : Law A) (P : A → Prop) (c : ℝ) :
    μ.expect (fun a => if P a then c else 0) = c * μ.prob P := by
  have h : (fun a => if P a then c else 0) =
      fun a => c * if P a then (1 : ℝ) else 0 := by
    funext a
    by_cases hp : P a <;> simp [hp]
  rw [h, μ.expect_mul]
  rfl

theorem bind_failure (μ : Law A) (f : A → Law B) (good : A → Prop)
    (bad : B → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ a, good a → (f a).prob bad ≤ ε) :
    (μ.bind f).prob bad ≤ μ.prob (fun a => ¬ good a) + ε := by
  classical
  rw [prob_bind]
  have hp (a : A) :
      (f a).prob bad ≤ (if ¬ good a then (1 : ℝ) else 0) + ε := by
    by_cases ha : good a
    · simpa only [ha, not_true_eq_false, ↓reduceIte, zero_add] using h a ha
    · simpa only [ha, not_false_eq_true, ↓reduceIte] using
        ((f a).prob_le_one bad).trans (by linarith : (1 : ℝ) ≤ 1 + ε)
  have hh := μ.expect_mono hp
  rw [expect_add, expect_const] at hh
  have he : (μ.expect fun a => if ¬ good a then (1 : ℝ) else 0) =
      μ.prob (fun a => ¬ good a) := by
    unfold prob
    congr 1
    funext a
    by_cases ha : good a <;> simp [ha]
  rw [he] at hh
  exact hh

def repeats (μ : Law A) : ℕ → Law (List A)
  | 0 => pure []
  | n + 1 => μ.bind fun a => (repeats μ n).map (List.cons a)

theorem repeats_all_probability (μ : Law A) (P : A → Prop) (n : ℕ) :
    (μ.repeats n).prob (fun xs => ∀ a ∈ xs, P a) = (μ.prob P) ^ n := by
  induction n with
  | zero => simp [repeats, prob]
  | succ n ih =>
      rw [repeats, prob_bind]
      have h (a : A) :
          ((μ.repeats n).map (List.cons a)).prob (fun xs => ∀ z ∈ xs, P z) =
            if P a then (μ.prob P) ^ n else 0 := by
        rw [prob_map]
        by_cases ha : P a
        · simpa only [List.mem_cons, forall_eq_or_imp, ha, true_and, ↓reduceIte] using ih
        · have hz : (fun xs : List A => ∀ z ∈ a :: xs, P z) = fun _ => False := by
            funext xs
            apply propext
            simp [ha]
          simp only [hz, prob_false, ha, ↓reduceIte]
      simp_rw [h]
      rw [expect_indicator_mul, pow_succ]

end Law

end StreamingReachability
