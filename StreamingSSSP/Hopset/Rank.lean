module

public import StreamingSSSP.Probability.Rate

@[expose] public section

namespace StreamingSSSP.Ranks

open scoped Classical

noncomputable def firstHit : List Rate → Law ℕ
  | [] => Law.pure 0
  | p :: ps =>
      p.draw.bind fun hit =>
        match hit with
        | true => Law.pure 0
        | false => (firstHit ps).map Nat.succ

def rate (ps : List Rate) (r : ℕ) : Rate := (ps[r]?).getD Rate.zero

noncomputable def survival (ps : List Rate) (r : ℕ) : ℝ :=
  ((ps.take r).map fun p => 1 - p.value).prod

def hasRank (cutoff r encoded : ℕ) : Prop := encoded < cutoff ∧ encoded = r

theorem firstHit_zero (p : Rate) (ps : List Rate) :
    (firstHit (p :: ps)).prob (· = 0) = p.value := by
  rw [firstHit, Law.prob_bind, Rate.expect_draw]
  have hz : ((firstHit ps).map Nat.succ).prob (· = 0) = 0 := by
    rw [Law.prob_map]
    exact ((firstHit ps).prob_congr (fun a => Nat.succ a = 0)
      (fun _ => False) (by
        intro a
        exact iff_false_intro (Nat.succ_ne_zero a))).trans
      ((firstHit ps).prob_false)
  have ho : (Law.pure 0).prob (· = 0) = 1 := by simp [Law.prob]
  change (1 - p.value) * ((firstHit ps).map Nat.succ).prob (· = 0) +
    p.value * (Law.pure 0).prob (· = 0) = _
  rw [hz, ho]
  ring

theorem firstHit_succ (p : Rate) (ps : List Rate) (r : ℕ) :
    (firstHit (p :: ps)).prob (· = r + 1) =
      (1 - p.value) * (firstHit ps).prob (· = r) := by
  rw [firstHit, Law.prob_bind, Rate.expect_draw]
  have hz : (Law.pure 0).prob (· = r + 1) = 0 := by simp [Law.prob]
  have hm : ((firstHit ps).map Nat.succ).prob (· = r + 1) =
      (firstHit ps).prob (· = r) := by
    rw [Law.prob_map]
    apply (firstHit ps).prob_congr
    intro a
    omega
  change (1 - p.value) * ((firstHit ps).map Nat.succ).prob (· = r + 1) +
    p.value * (Law.pure 0).prob (· = r + 1) = _
  rw [hz, hm]
  ring

theorem firstHit_ge_succ (p : Rate) (ps : List Rate) (r : ℕ) :
    (firstHit (p :: ps)).prob (fun a => r + 1 ≤ a) =
      (1 - p.value) * (firstHit ps).prob (fun a => r ≤ a) := by
  rw [firstHit, Law.prob_bind, Rate.expect_draw]
  have hz : (Law.pure 0).prob (fun a => r + 1 ≤ a) = 0 := by simp [Law.prob]
  have hm : ((firstHit ps).map Nat.succ).prob (fun a => r + 1 ≤ a) =
      (firstHit ps).prob (fun a => r ≤ a) := by
    rw [Law.prob_map]
    apply (firstHit ps).prob_congr
    intro a
    omega
  change (1 - p.value) * ((firstHit ps).map Nat.succ).prob (fun a => r + 1 ≤ a) +
    p.value * (Law.pure 0).prob (fun a => r + 1 ≤ a) = _
  rw [hz, hm]
  ring

theorem firstHit_tail (ps : List Rate) (r : ℕ) (hr : r ≤ ps.length) :
    (firstHit ps).prob (fun a => r ≤ a) = survival ps r := by
  induction ps generalizing r with
  | nil =>
      have he : r = 0 := by simpa using hr
      subst r
      simp [firstHit, survival, Law.prob]
  | cons p ps ih =>
      cases r with
      | zero => simp [survival, Law.prob]
      | succ r =>
          rw [firstHit_ge_succ, ih r (by simpa using hr)]
          simp [survival]

theorem survival_antitone (ps : List Rate) {r j : ℕ} (hrj : r ≤ j)
    (hj : j ≤ ps.length) : survival ps j ≤ survival ps r := by
  rw [← firstHit_tail ps j hj, ← firstHit_tail ps r (hrj.trans hj)]
  exact (firstHit ps).prob_mono (by intro a ha; omega)

theorem point_probability (ps : List Rate) (r : ℕ) (hr : r < ps.length) :
    (firstHit ps).prob (· = r) = (rate ps r).value * survival ps r := by
  induction ps generalizing r with
  | nil => simp at hr
  | cons p ps ih =>
      cases r with
      | zero => simp [firstHit_zero, rate, survival]
      | succ r =>
          rw [firstHit_succ, ih r (by simpa using hr)]
          simp only [rate, List.getElem?_cons_succ]
          simp only [survival, List.take_succ_cons, List.map_cons, List.prod_cons]
          ring

theorem rates_sum_nonneg (ps : List Rate) : 0 ≤ (ps.map Rate.value).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => exact add_nonneg p.value_nonneg ih

theorem survival_lower_sum (ps : List Rate) :
    1 - (ps.map Rate.value).sum ≤ (ps.map fun p => 1 - p.value).prod := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons]
      have h := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr p.value_le_one)
      nlinarith [mul_nonneg p.value_nonneg (rates_sum_nonneg ps)]

theorem survival_half (ps : List Rate) (r : ℕ)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    1 / 2 ≤ survival ps r := by
  have h := survival_lower_sum (ps.take r)
  change 1 / 2 ≤ ((ps.take r).map fun p => 1 - p.value).prod
  linarith

theorem censor_normalizer (ps : List Rate) (r : ℕ) (hr : r ≤ ps.length)
    (C : Finset ℕ) (hC : ∀ q ∈ C, q < r) :
    survival ps r ≤ (firstHit ps).prob (fun a => a ∉ C) := by
  rw [← firstHit_tail ps r hr]
  apply (firstHit ps).prob_mono
  intro a har hac
  have hlt := hC a hac
  omega

theorem censored_pivot_bounds (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (C : Finset ℕ) (hC : ∀ q ∈ C, q < r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (rate ps r).value / 2 ≤ ((firstHit ps).given (fun a => a ∉ C)).prob (· = r) ∧
      ((firstHit ps).given (fun a => a ∉ C)).prob (· = r) ≤ (rate ps r).value := by
  let μ := firstHit ps
  have hS := survival_half ps r hs
  have hSZ := censor_normalizer ps r hr.le C hC
  have hpos : 0 < μ.prob (fun a => a ∉ C) := by dsimp only [μ]; linarith
  have hnot : r ∉ C := by intro h; exact (lt_irrefl r) (hC r h)
  rw [Law.prob_given_eq μ (fun a => a ∉ C) r hnot hpos]
  rw [point_probability ps r hr]
  have hZ1 := μ.prob_le_one (fun a => a ∉ C)
  have hp := (rate ps r).value_nonneg
  constructor
  · apply (le_div_iff₀ hpos).mpr
    nlinarith
  · apply (div_le_iff₀ hpos).mpr
    exact mul_le_mul_of_nonneg_left hSZ hp

theorem eligible_pivot_exact (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    ((firstHit ps).given (fun a => r ≤ a)).prob (· = r) = (rate ps r).value := by
  let μ := firstHit ps
  have hS : 0 < survival ps r := by have hh := survival_half ps r hs; linarith
  have hp : 0 < μ.prob (fun a => r ≤ a) := by
    change 0 < (firstHit ps).prob (fun a => r ≤ a)
    rw [firstHit_tail ps r hr.le]
    exact hS
  rw [Law.prob_given_eq μ (fun a => r ≤ a) r le_rfl hp,
    point_probability ps r hr, firstHit_tail ps r hr.le]
  field_simp [ne_of_gt hS]

theorem censored_future_upper (ps : List Rate) (r j : ℕ)
    (hrj : r ≤ j) (hj : j < ps.length)
    (C : Finset ℕ) (hC : ∀ q ∈ C, q < r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    ((firstHit ps).given (fun a => a ∉ C)).prob (· = j) ≤ (rate ps j).value := by
  let μ := firstHit ps
  have hS := survival_half ps r hs
  have hSZ := censor_normalizer ps r (hrj.trans hj.le) C hC
  have hpos : 0 < μ.prob (fun a => a ∉ C) := by dsimp only [μ]; linarith
  have hnot : j ∉ C := by
    intro hm
    have hlt := hC j hm
    omega
  rw [Law.prob_given_eq μ (fun a => a ∉ C) j hnot hpos,
    point_probability ps j hj]
  apply (div_le_iff₀ hpos).mpr
  exact mul_le_mul_of_nonneg_left ((survival_antitone ps hrj hj.le).trans hSZ)
    (rate ps j).value_nonneg

end StreamingSSSP.Ranks
