module

public import StreamingReachability.Probability

@[expose] public section

namespace StreamingReachability

open scoped Classical BigOperators

namespace Tournament

variable {V : Type*}

noncomputable def degree (A : Finset V) (R : V → V → Prop) (u : V) : ℕ :=
  (A.filter (R u)).card

noncomputable def low (A : Finset V) (R : V → V → Prop) (b : ℕ) : Finset V :=
  A.filter fun u => 2 * degree A R u < b

theorem low_card_le (A : Finset V) (R : V → V → Prop) (b : ℕ)
    (hR : ∀ u ∈ A, ∀ v ∈ A, R u v ∨ R v u) :
    (low A R b).card ≤ b := by
  let S := low A R b
  have hSA : S ⊆ A := Finset.filter_subset _ _
  let N := ∑ u ∈ S, ∑ v ∈ S, if R u v then (1 : ℕ) else 0
  have hswap : (∑ u ∈ S, ∑ v ∈ S, if R v u then (1 : ℕ) else 0) = N := by
    exact Finset.sum_comm
  have hcount : S.card * S.card ≤ 2 * N := by
    calc
      S.card * S.card = ∑ u ∈ S, ∑ v ∈ S, (1 : ℕ) := by simp
      _ ≤ ∑ u ∈ S, ∑ v ∈ S,
          ((if R u v then 1 else 0) + (if R v u then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro v hv
        rcases hR u (hSA hu) v (hSA hv) with h | h <;> simp [h]
      _ = 2 * N := by
        simp only [Finset.sum_add_distrib]
        rw [hswap]
        omega
  have hN : N ≤ ∑ u ∈ S, degree A R u := by
    apply Finset.sum_le_sum
    intro u _
    change (∑ v ∈ S, if R u v then (1 : ℕ) else 0) ≤ (A.filter (R u)).card
    rw [← Finset.card_filter]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hSA)
  have hbudget : 2 * (∑ u ∈ S, degree A R u) ≤ S.card * b := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ _u ∈ S, b := by
        apply Finset.sum_le_sum
        intro u hu
        exact (Finset.mem_filter.mp hu).2.le
      _ = _ := by simp
  have hquad : S.card * S.card ≤ S.card * b :=
    hcount.trans ((Nat.mul_le_mul_left 2 hN).trans hbudget)
  change S.card ≤ b
  by_contra hn
  have hbs : b + 1 ≤ S.card := by omega
  have hm := Nat.mul_le_mul_left S.card hbs
  nlinarith

noncomputable def survivors (A P : Finset V) (R : V → V → Prop) : Finset V :=
  A.filter fun u => ∀ p ∈ P, ¬ R u p

theorem survivors_card_le (A P : Finset V) (R : V → V → Prop) (b : ℕ)
    (hR : ∀ u ∈ A, ∀ v ∈ A, R u v ∨ R v u)
    (hhit : ∀ u ∈ A, b ≤ 2 * degree A R u → ∃ p ∈ P, R u p) :
    (survivors A P R).card ≤ b := by
  apply (Finset.card_le_card (t := low A R b) ?_).trans (low_card_le A R b hR)
  intro u hu
  obtain ⟨huA, hnone⟩ := Finset.mem_filter.mp hu
  apply Finset.mem_filter.mpr
  refine ⟨huA, ?_⟩
  by_contra h
  obtain ⟨p, hp, hup⟩ := hhit u huA (Nat.le_of_not_gt h)
  exact hnone p hp hup

theorem prod_le_factor (A : Finset V) (f : V → ℝ)
    (h0 : ∀ i ∈ A, 0 ≤ f i) (h1 : ∀ i ∈ A, f i ≤ 1) {q : V} (hq : q ∈ A) :
    ∏ i ∈ A, f i ≤ f q := by
  have hr : ∏ i ∈ A.erase q, f i ≤ 1 :=
    Finset.prod_le_one₀ (fun i hi => h0 i (Finset.mem_of_mem_erase hi))
      (fun i hi => h1 i (Finset.mem_of_mem_erase hi))
  rw [← Finset.mul_prod_erase A f hq]
  exact mul_le_of_le_one_right (h0 q hq) hr

theorem row_product_sum_le_one (A : Finset V) (a : V → V → ℝ)
    (h0 : ∀ i ∈ A, ∀ j ∈ A, 0 ≤ a i j)
    (h1 : ∀ i ∈ A, ∀ j ∈ A, a i j ≤ 1)
    (hpair : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → a i j + a j i ≤ 1) :
    ∑ i ∈ A, ∏ j ∈ A.erase i, a i j ≤ 1 := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert p A hp ih =>
      have hA0 : ∀ i ∈ A, ∀ j ∈ A, 0 ≤ a i j :=
        fun i hi j hj => h0 i (by simp [hi]) j (by simp [hj])
      have hA1 : ∀ i ∈ A, ∀ j ∈ A, a i j ≤ 1 :=
        fun i hi j hj => h1 i (by simp [hi]) j (by simp [hj])
      have hAp : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → a i j + a j i ≤ 1 :=
        fun i hi j hj hne => hpair i (by simp [hi]) j (by simp [hj]) hne
      have hind := ih hA0 hA1 hAp
      let P := ∏ j ∈ A, a p j
      let b := fun i => ∏ j ∈ A.erase i, a i j
      have hP0 : 0 ≤ P :=
        Finset.prod_nonneg (fun j hj => h0 p (by simp) j (by simp [hj]))
      have hP1 : P ≤ 1 :=
        Finset.prod_le_one₀ (fun j hj => h0 p (by simp) j (by simp [hj]))
          (fun j hj => h1 p (by simp) j (by simp [hj]))
      have hb0 (i : V) (hi : i ∈ A) : 0 ≤ b i :=
        Finset.prod_nonneg fun j hj => hA0 i hi j (Finset.mem_of_mem_erase hj)
      have hrow (i : V) (hi : i ∈ A) : a i p ≤ 1 - P := by
        have hip : i ≠ p := fun he => hp (he ▸ hi)
        have hprod : P ≤ a p i :=
          prod_le_factor A (a p)
            (fun j hj => h0 p (by simp) j (by simp [hj]))
            (fun j hj => h1 p (by simp) j (by simp [hj])) hi
        have hsum := hpair i (by simp [hi]) p (by simp) hip
        linarith
      have hsum : ∑ i ∈ A, a i p * b i ≤ 1 - P := by
        calc
          _ ≤ ∑ i ∈ A, (1 - P) * b i :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_right (hrow i hi) (hb0 i hi)
          _ = (1 - P) * ∑ i ∈ A, b i := (Finset.mul_sum ..).symm
          _ ≤ (1 - P) * 1 :=
            mul_le_mul_of_nonneg_left hind (sub_nonneg.mpr hP1)
          _ = _ := mul_one _
      have hexpand :
          (∑ i ∈ insert p A, ∏ j ∈ (insert p A).erase i, a i j) =
            P + ∑ i ∈ A, a i p * b i := by
        rw [Finset.sum_insert hp]
        simp only [Finset.erase_insert hp]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        have hip : i ≠ p := fun he => hp (he ▸ hi)
        rw [Finset.erase_insert_of_ne hip.symm,
          Finset.prod_insert (fun hm => hp (Finset.mem_of_mem_erase hm))]
      rw [hexpand]
      linarith

end Tournament

end StreamingReachability
