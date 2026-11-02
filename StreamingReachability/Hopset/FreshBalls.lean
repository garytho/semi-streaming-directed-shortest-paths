module

public import StreamingReachability.Hopset.FreshMoments
public import StreamingReachability.Tournament

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def Hits (A : Finset (Fin n)) (R : Fin n → Fin n → Prop) (b : ℕ) (P : Finset (Fin n)) : Prop :=
  ∀ u ∈ A, b ≤ 2 * Tournament.degree A R u → ∃ p ∈ P ∩ A, R u p

theorem tournament_from_avoid (mu : Law (Finset (Fin n))) (S A : Finset (Fin n)) (hAS : A ⊆ S)
    (R : Fin n → Fin n → Prop) (b : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (havoid : ∀ T ⊆ S, mu.prob (fun P => Disjoint P T) ≤ Real.exp (-p * T.card)) :
    mu.prob (fun P => ¬ Hits A R b P) ≤
      (A.card : ℝ) * Real.exp (-p * b / 4) := by
  let bad := fun (u : Fin n) (P : Finset (Fin n)) =>
    b ≤ 2 * Tournament.degree A R u ∧ Disjoint P (A.filter (R u))
  have he : mu.prob (fun P => ¬ Hits A R b P) =
      mu.prob (fun P => ∃ u ∈ A, bad u P) := by
    apply Law.prob_congr
    intro P
    constructor
    · intro h
      unfold Hits at h
      push Not at h
      obtain ⟨u, hu, hb, hnone⟩ := h
      refine ⟨u, hu, hb, Finset.disjoint_left.mpr ?_⟩
      intro q hqP hqA
      obtain ⟨hqA, hR⟩ := Finset.mem_filter.mp hqA
      exact hnone q (Finset.mem_inter.mpr ⟨hqP, hqA⟩) hR
    · rintro ⟨u, hu, hb, hdis⟩ hhit
      obtain ⟨q, hq, hR⟩ := hhit u hu hb
      exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hq).1
        (Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hq).2, hR⟩)
  rw [he]
  calc
    _ ≤ ∑ u ∈ A, mu.prob (bad u) := Law.finite_union _ A bad
    _ ≤ ∑ _u ∈ A, Real.exp (-p * b / 4) := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hdegree : b ≤ 2 * Tournament.degree A R u
      · have ht : A.filter (R u) ⊆ S := (Finset.filter_subset _ _).trans hAS
        have hno := havoid (A.filter (R u)) ht
        apply ((Law.prob_mono mu (fun _ h => h.2)).trans hno).trans
        apply Real.exp_le_exp.mpr
        have hd : (b : ℝ) ≤ 2 * ((A.filter (R u)).card : ℝ) := by exact_mod_cast hdegree
        have hm := mul_le_mul_of_nonneg_left hd hp
        nlinarith
      · have hz : mu.prob (bad u) = 0 := by
          apply (Law.prob_congr _ _ (fun _ => False) ?_).trans (Law.prob_false _)
          intro P
          simp [bad, hdegree]
        rw [hz]
        exact (Real.exp_pos _).le
    _ = _ := by simp

theorem fresh_two_direction_failure (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n))
    (Ain Aout : Fin n → Finset (Fin n)) (Rin Rout : Fin n → Fin n → Prop) (b : ℕ)
    (hin : ∀ v ∈ S, Ain v ⊆ S) (hout : ∀ v ∈ S, Aout v ⊆ S) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).prob
        (fun P => ∃ v ∈ S, ¬ Hits (Ain v) Rin b P ∨ ¬ Hits (Aout v) Rout b P) ≤
      2 * (S.card : ℝ) ^ 2 * Real.exp (-p * b / 4) := by
  let mu := Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)
  let a := Real.exp (-p * b / 4)
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have havoid (T : Finset (Fin n)) (hT : T ⊆ S) :
      mu.prob (fun P => Disjoint P T) ≤ Real.exp (-p * T.card) :=
    fresh_avoid_exp p hp hp1 S T hT
  calc
    _ ≤ ∑ v ∈ S, mu.prob (fun P => ¬ Hits (Ain v) Rin b P ∨ ¬ Hits (Aout v) Rout b P) :=
      Law.finite_union _ S _
    _ ≤ ∑ v ∈ S, (mu.prob (fun P => ¬ Hits (Ain v) Rin b P) +
        mu.prob (fun P => ¬ Hits (Aout v) Rout b P)) :=
      Finset.sum_le_sum fun _ _ => Law.prob_union _ _ _
    _ ≤ ∑ _v ∈ S, 2 * S.card * a := by
      apply Finset.sum_le_sum
      intro v hv
      have hi := tournament_from_avoid mu S (Ain v) (hin v hv) Rin b p hp havoid
      have ho := tournament_from_avoid mu S (Aout v) (hout v hv) Rout b p hp havoid
      have hci : ((Ain v).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card (hin v hv)
      have hco : ((Aout v).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card (hout v hv)
      calc
        _ ≤ ((Ain v).card : ℝ) * a + ((Aout v).card : ℝ) * a := add_le_add hi ho
        _ ≤ (S.card : ℝ) * a + S.card * a :=
          add_le_add (mul_le_mul_of_nonneg_right hci ha) (mul_le_mul_of_nonneg_right hco ha)
        _ = _ := by ring
    _ = _ := by simp [a]; ring

end

end StreamingReachability.Hopset.Reference
