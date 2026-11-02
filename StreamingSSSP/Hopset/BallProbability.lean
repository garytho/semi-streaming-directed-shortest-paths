module

public import StreamingSSSP.Hopset.History
public import StreamingSSSP.Tournament

@[expose] public section

namespace StreamingSSSP.CopyHistory

open scoped Classical BigOperators

variable {n : ℕ}

def Hits (A : Finset (Fin n)) (R : Fin n → Fin n → Prop) (b r : ℕ)
    (ranks : Fin n → ℕ) : Prop :=
  ∀ u ∈ A, b ≤ 2 * Tournament.degree A R u →
    ∃ p ∈ A.filter (R u), ranks p = r

theorem tournament_failure (ps : List Rate) (history : List (Observation n))
    (S A : Finset (Fin n)) (hAS : A ⊆ S) (R : Fin n → Fin n → Prop)
    (b r : ℕ) (hr : r < ps.length) (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (law ps history).prob (fun ranks => ¬ Hits A R b r ranks) ≤
      (A.card : ℝ) * Real.exp (-(Ranks.rate ps r).value * b / 4) := by
  let bad := fun (u : Fin n) (ranks : Fin n → ℕ) => b ≤ 2 * Tournament.degree A R u ∧
    ∀ p ∈ A.filter (R u), ranks p ≠ r
  have he : (law ps history).prob (fun ranks => ¬ Hits A R b r ranks) =
      (law ps history).prob (fun ranks => ∃ u ∈ A, bad u ranks) := by
    apply Law.prob_congr
    intro ranks
    constructor
    · intro h
      unfold Hits at h
      push Not at h
      exact h
    · rintro ⟨u, hu, hb, hnone⟩ hhit
      obtain ⟨p, hp, he⟩ := hhit u hu hb
      exact hnone p hp he
  rw [he]
  calc
    _ ≤ ∑ u ∈ A, (law ps history).prob (bad u) := Law.finite_union _ A bad
    _ ≤ ∑ _u ∈ A, Real.exp (-(Ranks.rate ps r).value * b / 4) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hdegree : b ≤ 2 * Tournament.degree A R u
      · have hsmall : A.filter (R u) ⊆ S := (Finset.filter_subset _ _).trans hAS
        have hno := no_pivot_bound ps history S (A.filter (R u)) hsmall r hr hc hp hs
        have hmono : (law ps history).prob (bad u) ≤
            (law ps history).prob (fun ranks => ∀ p ∈ A.filter (R u), ranks p ≠ r) :=
          Law.prob_mono _ (by intro ranks h; exact h.2)
        apply (hmono.trans hno).trans
        apply Real.exp_le_exp.mpr
        have hd : (b : ℝ) ≤ 2 * ((A.filter (R u)).card : ℝ) := by
          exact_mod_cast hdegree
        have hrate := (Ranks.rate ps r).value_nonneg
        nlinarith
      · have hz : (law ps history).prob (bad u) = 0 := by
          apply (Law.prob_congr _ _ (fun _ => False) ?_).trans (Law.prob_false _)
          intro ranks
          simp [bad, hdegree]
        rw [hz]
        exact (Real.exp_pos _).le
    _ = _ := by simp

theorem two_direction_failure (ps : List Rate) (history : List (Observation n))
    (S : Finset (Fin n)) (Ain Aout : Fin n → Finset (Fin n))
    (Rin Rout : Fin n → Fin n → Prop) (b r : ℕ)
    (hin : ∀ v ∈ S, Ain v ⊆ S) (hout : ∀ v ∈ S, Aout v ⊆ S)
    (hr : r < ps.length) (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (law ps history).prob (fun ranks => ∃ v ∈ S,
      ¬ Hits (Ain v) Rin b r ranks ∨ ¬ Hits (Aout v) Rout b r ranks) ≤
      2 * (S.card : ℝ) ^ 2 * Real.exp (-(Ranks.rate ps r).value * b / 4) := by
  let a := Real.exp (-(Ranks.rate ps r).value * b / 4)
  have ha : 0 ≤ a := (Real.exp_pos _).le
  calc
    _ ≤ ∑ v ∈ S, (law ps history).prob (fun ranks =>
        ¬ Hits (Ain v) Rin b r ranks ∨ ¬ Hits (Aout v) Rout b r ranks) :=
      Law.finite_union _ S _
    _ ≤ ∑ v ∈ S, ((law ps history).prob (fun ranks => ¬ Hits (Ain v) Rin b r ranks) +
        (law ps history).prob (fun ranks => ¬ Hits (Aout v) Rout b r ranks)) :=
      Finset.sum_le_sum fun v _ => Law.prob_union _ _ _
    _ ≤ ∑ _v ∈ S, 2 * S.card * a := by
      apply Finset.sum_le_sum
      intro v hv
      have hi := tournament_failure ps history S (Ain v) (hin v hv) Rin b r hr hc hp hs
      have ho := tournament_failure ps history S (Aout v) (hout v hv) Rout b r hr hc hp hs
      have hci : ((Ain v).card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card (hin v hv)
      have hco : ((Aout v).card : ℝ) ≤ S.card := by
        exact_mod_cast Finset.card_le_card (hout v hv)
      calc
        _ ≤ ((Ain v).card : ℝ) * a + ((Aout v).card : ℝ) * a := add_le_add hi ho
        _ ≤ (S.card : ℝ) * a + S.card * a :=
          add_le_add (mul_le_mul_of_nonneg_right hci ha) (mul_le_mul_of_nonneg_right hco ha)
        _ = _ := by ring
    _ = _ := by simp [a]; ring

theorem joint_two_direction_failure (ps : List Rate) (history : List (Observation n))
    (S : Finset (Fin n)) (Ain Aout : Fin n → Finset (Fin n))
    (Rin Rout : Fin n → Fin n → Prop) (b r : ℕ)
    (hin : ∀ v ∈ S, Ain v ⊆ S) (hout : ∀ v ∈ S, Aout v ⊆ S)
    (hr : r < ps.length) (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (Law.family n (fun _ : Fin n => Ranks.firstHit ps)).prob (fun ranks =>
      (∀ v, allowed history v (ranks v)) ∧ ∃ v ∈ S,
        ¬ Hits (Ain v) Rin b r ranks ∨ ¬ Hits (Aout v) Rout b r ranks) ≤
      mass ps history * (2 * (S.card : ℝ) ^ 2 *
        Real.exp (-(Ranks.rate ps r).value * b / 4)) := by
  rw [history_factor]
  exact mul_le_mul_of_nonneg_left
    (two_direction_failure ps history S Ain Aout Rin Rout b r hin hout hr hc hp hs)
    (mass_nonneg ps history)

end StreamingSSSP.CopyHistory
