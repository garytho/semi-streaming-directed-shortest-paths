module

public import StreamingSSSP.Hopset.FixedGuessShortening

@[expose] public section

namespace StreamingSSSP.Core

theorem ceilNat_mul_le_add (A w : ℕ) : A * ceilNat A w ≤ w + A := by
  calc
    _ = ((w + A - 1) / A) * A := by unfold ceilNat; ring
    _ ≤ w + A - 1 := Nat.div_mul_le_self _ _
    _ ≤ w + A := Nat.sub_le _ _

end StreamingSSSP.Core

namespace StreamingSSSP.Late.Path

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem rounded_search_budget (Q : Path R G s t) (A : ℕ) :
    A * Q.searchWeight A ≤ Q.micro + A * Q.length := by
  induction Q with
  | nil => simp [searchWeight, micro, length]
  | cons e Q ih =>
      have he := Core.ceilNat_mul_le_add A e.micro
      simp only [searchWeight, Edge.searchWeight, micro, length]
      nlinarith

theorem searchWeight_le_three_unit (Q : Path R G s t) (A h U : ℕ) (hA : 0 < A)
    (hl : Q.length ≤ 2 * h) (hunit : 2 * h ≤ U) (hw : Q.micro ≤ 2 * A * U) :
    Q.searchWeight A ≤ 3 * U := by
  have hr := Q.rounded_search_budget A
  have hlen := Nat.mul_le_mul_left A (hl.trans hunit)
  have hbound : A * Q.searchWeight A ≤ A * (3 * U) := by nlinarith only [hr, hlen, hw]
  by_contra hn
  have hlt : 3 * U < Q.searchWeight A := by omega
  have hm := Nat.mul_lt_mul_of_pos_left hlt hA
  omega

end StreamingSSSP.Late.Path

namespace StreamingSSSP.Parameters

theorem two_hops_le_unit (n accuracy x : ℕ) (ha : 0 < accuracy) :
    2 * hopBound n accuracy x ≤ queryUnit n accuracy x := by
  have hd : 1 ≤ accuracyDenominator n accuracy := accuracyDenominator_pos n accuracy ha
  have hm := Nat.mul_le_mul_left (8 * hopBound n accuracy x) hd
  unfold queryUnit
  nlinarith

end StreamingSSSP.Parameters

namespace StreamingSSSP.Hopset

noncomputable section

variable {n : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)} {s t : Fin n}

theorem relative_search_budget (accuracy x delta : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hops : Q.length ≤ 2 * Parameters.hopBound n accuracy x)
    (hlower : delta * Parameters.queryUnit n accuracy x ≤ Q.micro) (debt : ℕ)
    (hdebt : (debt : ℝ) ≤
      (Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy) :
    ((delta * (Q.searchWeight delta + debt) : ℕ) : ℝ) ≤
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) * Q.micro := by
  let den : ℝ := Parameters.accuracyDenominator n accuracy
  let U : ℝ := Parameters.queryUnit n accuracy x
  let h : ℝ := Parameters.hopBound n accuracy x
  have hden : 0 < den := by dsimp only [den]; exact_mod_cast Parameters.accuracyDenominator_pos n accuracy ha
  have hdR : (0 : ℝ) < delta := by exact_mod_cast hd
  have hround : (delta : ℝ) * Q.searchWeight delta ≤ Q.micro + (delta : ℝ) * Q.length := by
    exact_mod_cast Q.rounded_search_budget delta
  have hlength : (Q.length : ℝ) ≤ 2 * h := by dsimp only [h]; exact_mod_cast hops
  have hlow : (delta : ℝ) * U ≤ Q.micro := by dsimp only [U]; exact_mod_cast hlower
  have hunit : U = 8 * h * den := by
    simp only [U, h, den, Parameters.queryUnit, Nat.cast_mul, Nat.cast_ofNat]
  have hdebtDen : (debt : ℝ) * den ≤ U := (le_div_iff₀ hden).mp hdebt
  have hroundDen := mul_le_mul_of_nonneg_right hround hden.le
  have hlengthDen := mul_le_mul_of_nonneg_left hlength (show 0 ≤ (delta : ℝ) * den by positivity)
  have hdebtDelta := mul_le_mul_of_nonneg_left hdebtDen hdR.le
  have hslack : 0 ≤ (Q.micro : ℝ) := Nat.cast_nonneg _
  push_cast
  change (delta : ℝ) * (Q.searchWeight delta + debt) ≤ (1 + 2 / den) * Q.micro
  apply (mul_le_mul_iff_left₀ hden).mp
  have heq : (1 + 2 / den) * Q.micro * den = den * Q.micro + 2 * Q.micro := by
    field_simp [hden.ne']
  rw [heq]
  rw [hunit] at hlow hdebtDelta
  nlinarith only [hroundDen, hlengthDen, hdebtDelta, hlow, hslack]

end

end StreamingSSSP.Hopset
