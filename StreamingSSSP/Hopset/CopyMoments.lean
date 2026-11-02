module

public import StreamingSSSP.Hopset.History
public import StreamingSSSP.Hopset.FringeProbability

@[expose] public section

namespace StreamingSSSP.CopyHistory

open scoped Classical BigOperators

variable {n : ℕ}

noncomputable def visits (A : Finset (Fin n)) (r : ℕ) (ranks : Fin n → ℕ) : ℝ :=
  ∑ v ∈ A, if ranks v = r then 1 else 0

theorem expected_visits (ps : List Rate) (history : List (Observation n))
    (S A : Finset (Fin n)) (hAS : A ⊆ S) (r j : ℕ)
    (hrj : r ≤ j) (hj : j < ps.length)
    (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (law ps history).expect (visits A j) ≤ (Ranks.rate ps j).value * A.card := by
  change (law ps history).expect (fun ranks => ∑ v ∈ A, if ranks v = j then 1 else 0) ≤ _
  rw [Law.expect_finset_sum]
  calc
    _ ≤ ∑ _v ∈ A, (Ranks.rate ps j).value := by
      apply Finset.sum_le_sum
      intro v hv
      rw [Law.expect_indicator (law ps history) (fun ranks => ranks v = j)]
      rw [law, Law.family_marginal_probability n
        (fun w => (Ranks.firstHit ps).given (allowed history w)) v (fun t => t = j)]
      exact active_future_upper ps history S r j hrj hj hc hp hs (hAS hv)
    _ = _ := by simp [mul_comm]

theorem selected_fringe_expectation (ps : List Rate) (history : List (Observation n))
    (v : Fin n) (r : ℕ) {O : Type*} (owners : Law O) (inside : O → Prop) :
    ((law ps history).bind fun ranks => owners.map fun owner =>
      if ranks v = r ∧ inside owner then (1 : ℝ) else 0).expect id =
      (law ps history).prob (fun ranks => ranks v = r) * owners.prob inside := by
  rw [Law.expect_bind]
  simp_rw [Law.expect_map]
  simp only [id_eq]
  have he : (fun ranks : Fin n → ℕ => owners.expect
      (fun owner => if ranks v = r ∧ inside owner then (1 : ℝ) else 0)) =
      fun ranks => if ranks v = r then owners.prob inside else 0 := by
    funext ranks
    by_cases h : ranks v = r <;> simp [h, Law.prob]
  rw [he, Law.expect_ite_const (law ps history) (fun ranks => ranks v = r)]
  ring

theorem expected_selected_fringe_le (ps : List Rate) (history : List (Observation n))
    (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) (r : ℕ) (hr : r < ps.length)
    (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    {O : Type*} (owners : Law O) (inside : O → Prop) (a : ℝ)
    (hinside : owners.prob inside ≤ a) :
    ((law ps history).bind fun ranks => owners.map fun owner =>
      if ranks v = r ∧ inside owner then (1 : ℝ) else 0).expect id ≤
      (Ranks.rate ps r).value * a := by
  rw [selected_fringe_expectation]
  have hmargin : (law ps history).prob (fun ranks => ranks v = r) ≤
      (Ranks.rate ps r).value := by
    rw [law, Law.family_marginal_probability n
      (fun w => (Ranks.firstHit ps).given (allowed history w)) v (fun t => t = r)]
    exact (active_rate_bounds ps history S r hr hc hp hs hv).2
  exact (mul_le_mul_of_nonneg_left hinside (Law.prob_nonneg _ _)).trans
    (mul_le_mul_of_nonneg_right hmargin ((owners.prob_nonneg inside).trans hinside))

end StreamingSSSP.CopyHistory
