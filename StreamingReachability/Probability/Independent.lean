module

public import StreamingReachability.Probability

@[expose] public section

namespace StreamingReachability.Law

open scoped Classical BigOperators

variable {V : Type*}

noncomputable def subset (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hp' : ∀ v, p v ≤ 1) :
    List V → Law (Finset V)
  | [] => pure ∅
  | v :: vs =>
      (coin (p v) (hp v) (hp' v)).bind fun hit =>
        if hit then (subset p hp hp' vs).map (insert v)
        else subset p hp hp' vs

theorem prob_insert_disjoint (μ : Law (Finset V)) (v : V) (T : Finset V) :
    (μ.map (insert v)).prob (fun S => Disjoint S T) =
      if v ∈ T then 0 else μ.prob (fun S => Disjoint S T) := by
  rw [prob_map]
  by_cases hv : v ∈ T
  · have he := μ.prob_congr (fun S => Disjoint (insert v S) T)
      (fun _ => False) (by intro S; simp [Finset.disjoint_insert_left, hv])
    simpa only [prob_false, hv, ↓reduceIte] using he
  · have he := μ.prob_congr (fun S => Disjoint (insert v S) T)
      (fun S => Disjoint S T) (by intro S; simp [Finset.disjoint_insert_left, hv])
    simpa only [hv, ↓reduceIte] using he

theorem subset_avoid (p : V → ℝ) (hp : ∀ v, 0 ≤ p v) (hp' : ∀ v, p v ≤ 1)
    (vs : List V) (T : Finset V) :
    (subset p hp hp' vs).prob (fun S => Disjoint S T) =
      (vs.map fun v => if v ∈ T then 1 - p v else 1).prod := by
  induction vs with
  | nil => simp [subset, prob]
  | cons v vs ih =>
      rw [subset, prob_bind, expect_coin]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [prob_insert_disjoint, ih]
      by_cases hv : v ∈ T <;> simp only [List.map_cons, List.prod_cons, hv, ↓reduceIte] <;> ring

theorem constant_subset_avoid_list (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (vs : List V) (T : Finset V) :
    (subset (fun _ : V => p) (fun _ => hp) (fun _ => hp') vs).prob
      (fun S => Disjoint S T) = (1 - p) ^ (vs.filter (· ∈ T)).length := by
  rw [subset_avoid]
  induction vs with
  | nil => simp
  | cons v vs ih =>
      by_cases hv : v ∈ T <;> simp [hv, ih, pow_succ, mul_comm]

theorem constant_subset_avoid (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (A T : Finset V) (hTA : T ⊆ A) :
    (subset (fun _ : V => p) (fun _ => hp) (fun _ => hp') A.toList).prob
      (fun S => Disjoint S T) = (1 - p) ^ T.card := by
  rw [constant_subset_avoid_list]
  have hn := (Finset.nodup_toList A).filter (fun v => v ∈ T)
  have hc : (A.toList.filter (· ∈ T)).length = T.card := by
    rw [← List.toFinset_card_of_nodup hn]
    congr 1
    ext v
    simp only [List.mem_toFinset, List.mem_filter, Finset.mem_toList, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hTA h, h⟩⟩
  rw [hc]

theorem exp_avoid_bound (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (A T : Finset V) (hTA : T ⊆ A) :
    (subset (fun _ : V => p) (fun _ => hp) (fun _ => hp') A.toList).prob
      (fun S => Disjoint S T) ≤ Real.exp (-p * T.card) := by
  rw [constant_subset_avoid p hp hp' A T hTA]
  have hbase : 1 - p ≤ Real.exp (-p) := by
    linarith [Real.add_one_le_exp (-p)]
  calc
    (1 - p) ^ T.card ≤ Real.exp (-p) ^ T.card :=
      pow_le_pow_left₀ (sub_nonneg.mpr hp') hbase _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end StreamingReachability.Law
