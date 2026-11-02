module

public import StreamingSSSP.Probability

@[expose] public section

namespace StreamingSSSP

open scoped Classical

theorem weightedSum_filter {A : Type*} (xs : List (A × ℝ)) (P : A → Prop) (f : A → ℝ) :
    weightedSum (xs.filter fun z => P z.1) f =
      weightedSum xs (fun a => if P a then f a else 0) := by
  classical
  induction xs with
  | nil => simp
  | cons z xs ih =>
      by_cases hz : P z.1 <;> simp [hz, ih, weightedSum_cons]

private theorem weightedMaskedZero {A : Type*} (xs : List (A × ℝ)) (P : A → Prop)
    (hw : ∀ z ∈ xs, 0 ≤ z.2)
    (hz : weightedSum xs (fun a => if P a then (1 : ℝ) else 0) = 0)
    (f : A → ℝ) :
    weightedSum xs (fun a => if P a then f a else 0) = 0 := by
  classical
  induction xs with
  | nil => simp
  | cons z xs ih =>
      have hwt : ∀ a ∈ xs, 0 ≤ a.2 := fun a ha => hw a (by simp [ha])
      have hhead : 0 ≤ z.2 * (if P z.1 then (1 : ℝ) else 0) := by
        by_cases hp : P z.1 <;> simp [hp, hw z (by simp)]
      have htail : 0 ≤ weightedSum xs (fun a => if P a then (1 : ℝ) else 0) :=
        weightedSum_nonneg _ _ hwt (by intro a; split_ifs <;> norm_num)
      simp only [weightedSum_cons] at hz
      have hh : z.2 * (if P z.1 then (1 : ℝ) else 0) = 0 := by linarith
      have ht : weightedSum xs (fun a => if P a then (1 : ℝ) else 0) = 0 := by linarith
      have hf : z.2 * (if P z.1 then f z.1 else 0) = 0 := by
        by_cases hp : P z.1
        · have hz' : z.2 = 0 := by simpa [hp] using hh
          simp [hz']
        · simp [hp]
      simp only [weightedSum_cons, hf, ih hwt ht, add_zero]

namespace Law

variable {A : Type*}

noncomputable def masked (P : A → Prop) (f : A → ℝ) : A → ℝ :=
  fun a => if P a then f a else 0

theorem masked_mask (P Q : A → Prop) (f : A → ℝ) :
    masked P (masked Q f) = masked (fun a => P a ∧ Q a) f := by
  funext a
  by_cases hp : P a <;> by_cases hq : Q a <;> simp [masked, hp, hq]

theorem prob_eq_mask (μ : Law A) (P : A → Prop) :
    μ.prob P = μ.expect (masked P (fun _ => 1)) := rfl

theorem masked_expect_zero (μ : Law A) (P : A → Prop) (hz : μ.prob P = 0) (f : A → ℝ) :
    μ.expect (fun a => if P a then f a else 0) = 0 :=
  weightedMaskedZero μ.atoms P μ.nonneg hz f

noncomputable def condition (μ : Law A) (P : A → Prop) (hp : 0 < μ.prob P) : Law A where
  atoms := (μ.atoms.filter fun z => P z.1).map fun z => (z.1, (1 / μ.prob P) * z.2)
  nonneg := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    exact mul_nonneg (one_div_nonneg.mpr hp.le) (μ.nonneg a (List.mem_filter.mp ha).1)
  total := by
    rw [weightedSum_scale, weightedSum_filter]
    change (1 / μ.prob P) * μ.prob P = 1
    exact one_div_mul_cancel (ne_of_gt hp)

theorem expect_condition (μ : Law A) (P : A → Prop) (hp : 0 < μ.prob P) (f : A → ℝ) :
    (μ.condition P hp).expect f =
      (1 / μ.prob P) * μ.expect (fun a => if P a then f a else 0) := by
  change weightedSum
    ((μ.atoms.filter fun z => P z.1).map fun z => (z.1, (1 / μ.prob P) * z.2)) f = _
  rw [weightedSum_scale, weightedSum_filter]
  rfl

theorem prob_condition (μ : Law A) (P Q : A → Prop) (hp : 0 < μ.prob P) :
    (μ.condition P hp).prob Q = μ.prob (fun a => P a ∧ Q a) / μ.prob P := by
  rw [prob, expect_condition]
  have he : (μ.expect fun a => if P a then (if Q a then (1 : ℝ) else 0) else 0) =
      μ.prob (fun a => P a ∧ Q a) := by
    unfold prob
    congr 1
    funext a
    by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]
  rw [he]
  ring

noncomputable def given (μ : Law A) (P : A → Prop) : Law A :=
  if hp : 0 < μ.prob P then μ.condition P hp else μ

theorem given_factor (μ : Law A) (P : A → Prop) (f : A → ℝ) :
    μ.prob P * (μ.given P).expect f =
      μ.expect (fun a => if P a then f a else 0) := by
  by_cases hp : 0 < μ.prob P
  · rw [given, dite_eq_left hp, expect_condition]
    field_simp [ne_of_gt hp]
  · have hz : μ.prob P = 0 := le_antisymm (le_of_not_gt hp) (μ.prob_nonneg P)
    rw [hz, zero_mul, μ.masked_expect_zero P hz f]

theorem expect_mask_eq (μ : Law A) (P : A → Prop) (f : A → ℝ) :
    μ.expect (masked P f) = μ.prob P * (μ.given P).expect f :=
  (given_factor μ P f).symm

theorem expect_mask_mul (μ : Law A) (P : A → Prop) (c : ℝ) (f : A → ℝ) :
    μ.expect (masked P (fun a => c * f a)) = c * μ.expect (masked P f) := by
  have he : masked P (fun a => c * f a) = fun a => c * masked P f a := by
    funext a
    by_cases hp : P a <;> simp [masked, hp]
  rw [he, expect_mul]

theorem expect_bool (μ : Law Bool) (f : Bool → ℝ) :
    μ.expect f = (1 - μ.prob (· = true)) * f false + μ.prob (· = true) * f true := by
  let g : Bool → ℝ := fun b => @ite ℝ (b = true) (Classical.propDecidable _) 1 0
  have hg : μ.expect g = μ.prob (· = true) := rfl
  have he : f = fun b => f false + (f true - f false) * g b := by
    funext b
    cases b <;> simp [g]
  calc
    μ.expect f = μ.expect (fun b => f false + (f true - f false) * g b) :=
      congrArg μ.expect he
    _ = f false + (f true - f false) * μ.expect g := by
      rw [expect_add, expect_const, expect_mul]
    _ = _ := by rw [hg]; ring

theorem boolean_disintegration (μ : Law A) (P : A → Prop) (f : A → ℝ) :
    (coin (μ.prob P) (μ.prob_nonneg P) (μ.prob_le_one P)).expect
        (fun b => (if b then μ.given P else μ.given (fun a => ¬ P a)).expect f) =
      μ.expect f := by
  rw [expect_coin]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← μ.prob_compl P, given_factor, given_factor, ← expect_add]
  congr 1
  funext a
  by_cases hp : P a <;> simp [hp]

theorem prob_given_eq (μ : Law A) [DecidableEq A] (P : A → Prop) (a : A)
    (hP : P a) (hp : 0 < μ.prob P) :
    (μ.given P).prob (· = a) = μ.prob (· = a) / μ.prob P := by
  rw [given, dite_eq_left hp, prob_condition]
  congr 1
  apply μ.prob_congr
  intro b
  constructor
  · exact And.right
  · intro hb
    exact ⟨hb ▸ hP, hb⟩

end Law

end StreamingSSSP
