module

public import StreamingSSSP.Hopset.Rank
public import StreamingSSSP.Probability.ConditionalFamily
public import StreamingSSSP.Probability.Projection

@[expose] public section

namespace StreamingSSSP.RankPrefix

open scoped Classical BigOperators

def observe (r rank : ℕ) : Option (Fin r) :=
  if h : rank < r then some ⟨rank, h⟩ else none

theorem observe_none (r rank : ℕ) : observe r rank = none ↔ r ≤ rank := by
  by_cases h : rank < r <;> simp [observe, h] <;> omega

theorem observe_some (r rank : ℕ) (known : Fin r) :
    observe r rank = some known ↔ rank = known.val := by
  by_cases h : rank < r
  · simp only [observe, dite_eq_left h, Option.some.injEq]
    constructor
    · intro he
      exact congrArg Fin.val he
    · intro he
      exact Fin.ext he
  · have hne : rank ≠ known.val := by
      intro he
      apply h
      simpa only [he] using known.isLt
    simp [observe, h, hne]

noncomputable def component (ps : List Rate) (r : ℕ) : Option (Fin r) → Law ℕ
  | none => (Ranks.firstHit ps).given (fun rank => r ≤ rank)
  | some known => Law.pure known.val

noncomputable def law (ps : List Rate) (r : ℕ) {n : ℕ} (known : Fin n → Option (Fin r)) :
    Law (Fin n → ℕ) :=
  Law.family n fun v => component ps r (known v)

noncomputable def mass (ps : List Rate) (r : ℕ) {n : ℕ} (known : Fin n → Option (Fin r)) : ℝ :=
  ∏ v, (Ranks.firstHit ps).prob (fun rank => observe r rank = known v)

theorem component_factor (ps : List Rate) (r : ℕ) (known : Option (Fin r)) (f : ℕ → ℝ) :
    (Ranks.firstHit ps).expect (Law.masked (fun rank => observe r rank = known) f) =
      (Ranks.firstHit ps).prob (fun rank => observe r rank = known) *
        (component ps r known).expect f := by
  cases known with
  | none =>
      have he : (fun rank => observe r rank = none) = fun rank => r ≤ rank :=
        funext fun rank => propext (observe_none r rank)
      rw [he]
      exact Law.expect_mask_eq _ _ _
  | some known =>
      have he : (fun rank => observe r rank = some known) = fun rank => rank = known.val :=
        funext fun rank => propext (observe_some r rank known)
      rw [he, Law.expect_mask_point]
      simp only [component, Law.expect_pure]

theorem factor (ps : List Rate) (r : ℕ) {n : ℕ} (known : Fin n → Option (Fin r))
    (f : (Fin n → ℕ) → ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (fun ranks => ∀ v, observe r (ranks v) = known v) f) =
      mass ps r known * (law ps r known).expect f :=
  Law.family_mask_transfer n (fun _ => Ranks.firstHit ps) (fun v => component ps r (known v))
    (fun v rank => observe r rank = known v)
    (fun v => (Ranks.firstHit ps).prob (fun rank => observe r rank = known v))
    (fun v => component_factor ps r (known v)) f

theorem current_probability (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) (known : Option (Fin r)) :
    (component ps r known).prob (· = r) =
      match known with | none => (Ranks.rate ps r).value | some _ => 0 := by
  cases known with
  | none => exact Ranks.eligible_pivot_exact ps r hr hs
  | some known =>
      have hne : known.val ≠ r := Nat.ne_of_lt known.isLt
      simp [component, Law.prob, hne]

noncomputable def currentLaw (ps : List Rate) (r : ℕ) : Option (Fin r) → Law Bool
  | none => Law.coin (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
      (Ranks.rate ps r).value_le_one
  | some _ => Law.pure false

theorem current_coin (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Option (Fin r)) (f : Bool → ℝ) :
    ((component ps r known).map (fun rank => decide (rank = r))).expect f =
      (currentLaw ps r known).expect f := by
  cases known with
  | none =>
      have hprob :
          ((component ps r none).map (fun rank => decide (rank = r))).prob (· = true) =
            (Ranks.rate ps r).value := by
        rw [Law.prob_map]
        apply (Law.prob_congr _ _ (fun rank => rank = r) ?_).trans
          (current_probability ps r hr hs none)
        intro rank
        simp
      rw [Law.expect_bool, hprob]
      exact (Law.expect_coin (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
        (Ranks.rate ps r).value_le_one f).symm
  | some known =>
      have hne : known.val ≠ r := Nat.ne_of_lt known.isLt
      simp [component, currentLaw, Law.expect_map, hne]

theorem current_family (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    {n : ℕ} (known : Fin n → Option (Fin r)) (f : (Fin n → Bool) → ℝ) :
    (law ps r known).expect (fun ranks => f (fun v => decide (ranks v = r))) =
      (Law.family n (fun v => currentLaw ps r (known v))).expect f := by
  rw [law, Law.family_map n (fun v => component ps r (known v))
    (fun _ rank => decide (rank = r)) f]
  apply Law.family_expect_congr
  intro v g
  exact current_coin ps r hr hs (known v) g

end StreamingSSSP.RankPrefix
