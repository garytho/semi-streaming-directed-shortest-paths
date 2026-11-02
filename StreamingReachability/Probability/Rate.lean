module

public import StreamingReachability.Probability.Uniform
public import StreamingReachability.Probability.Conditioning

@[expose] public section

namespace StreamingReachability

open scoped Classical

structure Rate where
  numerator : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator
  numerator_le : numerator ≤ denominator

namespace Rate

def zero : Rate := ⟨0, 1, by decide, by decide⟩

def one : Rate := ⟨1, 1, by decide, by decide⟩

noncomputable def value (p : Rate) : ℝ := (p.numerator : ℝ) / p.denominator

theorem value_nonneg (p : Rate) : 0 ≤ p.value := by
  unfold value
  positivity

theorem value_le_one (p : Rate) : p.value ≤ 1 := by
  have hd : (0 : ℝ) < p.denominator := by exact_mod_cast p.denominator_pos
  apply (div_le_one hd).mpr
  exact_mod_cast p.numerator_le

noncomputable def draw (p : Rate) : Law Bool :=
  (Law.uniform p.denominator p.denominator_pos).map fun i => decide (i.val < p.numerator)

theorem threshold_card (a d : ℕ) (had : a ≤ d) :
    (Finset.univ.filter fun i : Fin d => i.val < a).card = a := by
  let cast : Fin a → Fin d := fun i => ⟨i.val, lt_of_lt_of_le i.isLt had⟩
  have hinj : Function.Injective cast := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : Fin d => z.val) hij)
  have he : Finset.univ.image cast = (Finset.univ.filter fun i : Fin d => i.val < a) := by
    ext i
    constructor
    · intro hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
    · intro hi
      have hia := (Finset.mem_filter.mp hi).2
      let j : Fin a := ⟨i.val, hia⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, Fin.ext rfl⟩
  rw [← he, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem prob_draw_true (p : Rate) : p.draw.prob (· = true) = p.value := by
  rw [draw, Law.prob_map]
  have he : (fun i : Fin p.denominator => decide (i.val < p.numerator) = true) =
      fun i => i.val < p.numerator := by
    funext i
    exact propext (by simp)
  rw [he, Law.prob_uniform]
  unfold value
  congr 1
  norm_cast
  convert threshold_card p.numerator p.denominator p.numerator_le using 1
  congr 1
  ext i
  simp

theorem expect_draw (p : Rate) (f : Bool → ℝ) :
    p.draw.expect f = (1 - p.value) * f false + p.value * f true := by
  rw [Law.expect_bool, prob_draw_true]

theorem expect_as_coin (p : Rate) (f : Bool → ℝ) :
    p.draw.expect f =
      (Law.coin p.value p.value_nonneg p.value_le_one).expect f := by
  rw [expect_draw, Law.expect_coin]

theorem prob_draw_false (p : Rate) : p.draw.prob (· = false) = 1 - p.value := by
  rw [Law.prob, expect_draw]
  simp

end Rate

end StreamingReachability
