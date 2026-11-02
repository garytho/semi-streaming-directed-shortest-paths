module

public import StreamingSSSP.Hopset.ReferenceFacts

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

theorem members_filter_length (S T : Finset (Fin n)) (hTS : T ⊆ S) :
    ((members S).filter fun v => decide (v ∈ T)).length = T.card := by
  have hn := (members_nodup S).filter (fun v => decide (v ∈ T))
  rw [← List.toFinset_card_of_nodup hn]
  congr 1
  ext v
  simp only [List.mem_toFinset, List.mem_filter, mem_members, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hTS h, h⟩⟩

theorem fresh_avoid (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (S T : Finset (Fin n)) (hTS : T ⊆ S) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).prob
        (fun P => Disjoint P T) = (1 - p) ^ T.card := by
  rw [Law.constant_subset_avoid_list]
  have hc := members_filter_length S T hTS
  convert congrArg (fun count => (1 - p) ^ count) hc using 1
  congr 1
  apply congrArg List.length
  apply List.filter_congr
  intro v _
  by_cases hv : v ∈ T <;> simp [hv]

theorem fresh_avoid_exp (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S T : Finset (Fin n)) (hTS : T ⊆ S) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).prob
        (fun P => Disjoint P T) ≤ Real.exp (-p * T.card) := by
  rw [fresh_avoid p hp hp1 S T hTS]
  have hbase : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  calc
    (1 - p) ^ T.card ≤ Real.exp (-p) ^ T.card :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp1) hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem fresh_contains (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).prob
        (fun P => v ∈ P) = p := by
  let mu := Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)
  have hdis : mu.prob (fun P => v ∉ P) = mu.prob (fun P => Disjoint P {v}) := by
    apply Law.prob_congr
    intro P
    simp
  have havoid : mu.prob (fun P => v ∉ P) = 1 - p := by
    rw [hdis, fresh_avoid p hp hp1 S {v} (by simpa using hv)]
    simp
  have hcomp := mu.prob_compl (fun P => v ∉ P)
  have hdouble : mu.prob (fun P => ¬ v ∉ P) = mu.prob (fun P => v ∈ P) := by
    apply Law.prob_congr
    intro P
    exact not_not
  rw [hdouble, havoid] at hcomp
  linarith

theorem fresh_expected_visits (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S A : Finset (Fin n)) (hAS : A ⊆ S) :
    (Law.subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) (members S)).expect
        (fun P => ∑ v ∈ A, if v ∈ P then (1 : ℝ) else 0) = p * A.card := by
  rw [Law.expect_finset_sum]
  calc
    _ = ∑ _v ∈ A, p := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Law.expect_indicator _ (fun P => v ∈ P)]
      exact fresh_contains p hp hp1 S v (hAS hv)
    _ = _ := by simp [mul_comm]

end

end StreamingSSSP.Hopset.Reference
