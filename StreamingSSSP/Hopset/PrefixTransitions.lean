module

public import StreamingSSSP.Hopset.EligibilitySampling
public import StreamingSSSP.Probability.Observation

@[expose] public section

namespace StreamingSSSP.RankPrefix

open scoped Classical

noncomputable section

def nextKnown (r : ℕ) : Option (Fin r) → Bool → Option (Fin (r + 1))
  | some old, _ => some old.castSucc
  | none, true => some (Fin.last r)
  | none, false => none

theorem observe_next (r rank : ℕ) :
    observe (r + 1) rank = nextKnown r (observe r rank) (decide (rank = r)) := by
  by_cases hk : rank < r
  · have hs : rank < r + 1 := by omega
    have hn : rank ≠ r := by omega
    simp only [observe, dite_eq_left hk, dite_eq_left hs, hn, decide_false, nextKnown]
    rfl
  · by_cases he : rank = r
    · subst rank
      simp [observe, nextKnown]
      rfl
    · have hs : ¬ rank < r + 1 := by omega
      simp [observe, nextKnown, hk, hs, he]

theorem component_next_factor (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Option (Fin r)) (b : Bool) (f : ℕ → ℝ) :
    (component ps r known).expect (Law.masked (fun rank => decide (rank = r) = b) f) =
      (currentLaw ps r known).prob (· = b) * (component ps (r + 1) (nextKnown r known b)).expect f := by
  cases known with
  | some old =>
      have hn : old.val ≠ r := Nat.ne_of_lt old.isLt
      cases b <;> simp [component, currentLaw, nextKnown, Law.prob, Law.masked, hn]
  | none =>
      let P := fun rank : ℕ => r ≤ rank
      let T := fun rank : ℕ => r + 1 ≤ rank
      have hp : 0 < (Ranks.firstHit ps).prob P := by
        change 0 < (Ranks.firstHit ps).prob (fun rank => r ≤ rank)
        rw [Ranks.firstHit_tail ps r hr.le]
        have h := Ranks.survival_half ps r hs
        linarith
      cases b with
      | false =>
          have he : (fun rank : ℕ => decide (rank = r) = false) = fun rank => rank ≠ r := by
            funext rank
            apply propext
            by_cases h : rank = r <;> simp [h]
          have hc := Law.given_restrict_factor (Ranks.firstHit ps) P (fun rank => rank ≠ r) T hp
            (fun rank => by dsimp [P, T]; omega) f
          have hprob : ((Ranks.firstHit ps).given P).prob (fun rank => rank ≠ r) =
              1 - (Ranks.rate ps r).value := by
            rw [Law.prob_compl]
            exact congrArg (fun z : ℝ => 1 - z) (current_probability ps r hr hs none)
          change ((Ranks.firstHit ps).given P).expect
              (Law.masked (fun rank => decide (rank = r) = false) f) =
            (Law.coin (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
              (Ranks.rate ps r).value_le_one).prob (· = false) *
                ((Ranks.firstHit ps).given T).expect f
          rw [he, Law.prob_coin_false, ← hprob]
          exact hc
      | true =>
          have he : (fun rank : ℕ => decide (rank = r) = true) = fun rank => rank = r := by
            funext rank
            apply propext
            simp
          change ((Ranks.firstHit ps).given P).expect
              (Law.masked (fun rank => decide (rank = r) = true) f) =
            (Law.coin (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
              (Ranks.rate ps r).value_le_one).prob (· = true) * (Law.pure r).expect f
          rw [he, Law.expect_mask_point, Law.prob_coin_true, Law.expect_pure]
          have h := current_probability ps r hr hs none
          change ((Ranks.firstHit ps).given P).prob (· = r) = (Ranks.rate ps r).value at h
          rw [h]

theorem next_disintegration {n : ℕ} (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Fin n → Option (Fin r)) (f : (Fin n → ℕ) → ℝ) :
    (law ps r known).expect f =
      (Law.family n (fun v => currentLaw ps r (known v))).expect (fun coins =>
        (law ps (r + 1) (fun v => nextKnown r (known v) (coins v))).expect f) :=
  Law.family_observation_tower n (fun v => component ps r (known v))
    (fun v => currentLaw ps r (known v)) (fun _ rank => decide (rank = r))
    (fun v b => component ps (r + 1) (nextKnown r (known v) b))
    (fun v b g => component_next_factor ps r hr hs (known v) b g) f

theorem next_observed {n : ℕ} (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Fin n → Option (Fin r)) (f : (Fin n → Bool) → (Fin n → ℕ) → ℝ) :
    (law ps r known).expect (fun ranks => f (fun v => decide (ranks v = r)) ranks) =
      (Law.family n (fun v => currentLaw ps r (known v))).expect (fun coins =>
        (law ps (r + 1) (fun v => nextKnown r (known v) (coins v))).expect (f coins)) :=
  Law.family_observation n (fun v => component ps r (known v))
    (fun v => currentLaw ps r (known v)) (fun _ rank => decide (rank = r))
    (fun v b => component ps (r + 1) (nextKnown r (known v) b))
    (fun v b g => component_next_factor ps r hr hs (known v) b g) f

theorem zero_expect {n : ℕ} (ps : List Rate) (f : (Fin n → ℕ) → ℝ) :
    (law ps 0 (fun _ => none)).expect f = (Law.family n (fun _ => Ranks.firstHit ps)).expect f := by
  apply Law.family_expect_congr
  intro v g
  have hp : (Ranks.firstHit ps).prob (fun rank => 0 ≤ rank) = 1 := by
    simp [Law.prob]
  have hm : Law.masked (fun rank : ℕ => 0 ≤ rank) g = g := by
    funext rank
    simp [Law.masked]
  have h := Law.expect_mask_eq (Ranks.firstHit ps) (fun rank => 0 ≤ rank) g
  rw [hp, hm, one_mul] at h
  exact h.symm

end

end StreamingSSSP.RankPrefix
