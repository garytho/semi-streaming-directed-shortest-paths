module

public import StreamingReachability.Probability

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

namespace Fractional

variable {V : Type*}

def off (q : V → V → ℝ) (u v : V) : ℝ := if u = v then 0 else q u v

def degree (A : Finset V) (q : V → V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ A, off q u v

theorem internal_weight_lower (S : Finset V) (q : V → V → ℝ)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (1 : ℝ) / 2 ≤ q u v + q v u) :
    (S.card : ℝ) * ((S.card : ℝ) - 1) / 4 ≤
      ∑ u ∈ S, ∑ v ∈ S, off q u v := by
  have hswap :
      (∑ u ∈ S, ∑ v ∈ S, off q v u) =
        ∑ u ∈ S, ∑ v ∈ S, off q u v := Finset.sum_comm
  have hcount :
      (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 =
        ∑ u ∈ S, ∑ v ∈ S, if u = v then (0 : ℝ) else 1 / 2 := by
    have hrow (u : V) (hu : u ∈ S) :
        (∑ v ∈ S, if u = v then (0 : ℝ) else 1 / 2) =
          ((S.card : ℝ) - 1) / 2 := by
      have he (v : V) : (if u = v then (0 : ℝ) else 1 / 2) =
          1 / 2 - (if u = v then 1 / 2 else 0) := by
        by_cases h : u = v <;> simp [h]
      simp_rw [he]
      rw [Finset.sum_sub_distrib]
      simp [hu]
      ring
    simp_rw [Finset.sum_congr rfl hrow]
    simp
    ring
  have hsum :
      (∑ u ∈ S, ∑ v ∈ S, if u = v then (0 : ℝ) else 1 / 2) ≤
        ∑ u ∈ S, ∑ v ∈ S, (off q u v + off q v u) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    by_cases h : u = v
    · subst v
      simp [off]
    · simpa [off, h, show v ≠ u from Ne.symm h] using hpair u hu v hv h
  simp only [Finset.sum_add_distrib] at hsum
  rw [hswap, ← hcount] at hsum
  linarith

theorem subset_degree_lower (A S : Finset V) (q : V → V → ℝ)
    (hSA : S ⊆ A)
    (h0 : ∀ u ∈ A, ∀ v ∈ A, 0 ≤ q u v)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → (1 : ℝ) / 2 ≤ q u v + q v u) :
    (S.card : ℝ) * ((S.card : ℝ) - 1) / 4 ≤ ∑ u ∈ S, degree A q u := by
  apply (internal_weight_lower S q
    (fun u hu v hv h => hpair u (hSA hu) v (hSA hv) h)).trans
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum_of_subset_of_nonneg hSA
  intro v hv _
  by_cases h : u = v
  · simp [off, h]
  · simpa only [off, h, ↓reduceIte] using h0 u (hSA hu) v hv

theorem sorted_degree_lower (A : Finset V) (q : V → V → ℝ)
    (h0 : ∀ u ∈ A, ∀ v ∈ A, 0 ≤ q u v)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → (1 : ℝ) / 2 ≤ q u v + q v u)
    (L : List V) (hperm : L.Perm A.toList)
    (hsorted : L.Pairwise fun u v => degree A q u ≤ degree A q v)
    (i : Fin L.length) :
    (i.val : ℝ) / 4 ≤ degree A q (L.get i) := by
  have hn : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList A)
  let f : Fin (i.val + 1) → V := fun j =>
    L.get ⟨j.val, by have := i.isLt; omega⟩
  let S := Finset.univ.image f
  have hf : Function.Injective f := by
    intro j k he
    have hh := hn.injective_get he
    exact Fin.ext (congrArg (fun x : Fin L.length => x.val) hh)
  have hSc : S.card = i.val + 1 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hSA : S ⊆ A := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_toList.mp (hperm.mem_iff.mp (List.get_mem L _))
  have hupper : ∑ u ∈ S, degree A q u ≤
      (S.card : ℝ) * degree A q (L.get i) := by
    calc
      _ ≤ ∑ _u ∈ S, degree A q (L.get i) := by
        apply Finset.sum_le_sum
        intro u hu
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
        have hji : j.val ≤ i.val := by have := j.isLt; omega
        by_cases he : j.val = i.val
        · have hh : (⟨j.val, by have := i.isLt; omega⟩ : Fin L.length) = i := Fin.ext he
          simpa only [f, hh] using
            (le_rfl : degree A q (L.get i) ≤ degree A q (L.get i))
        · exact hsorted.rel_get_of_lt (by change j.val < i.val; omega)
      _ = _ := by simp
  have hlower := subset_degree_lower A S q hSA h0 hpair
  rw [hSc] at hlower hupper
  push_cast at hlower hupper
  have hi : (0 : ℝ) < i.val + 1 := by positivity
  nlinarith

theorem exp_sum_le_geometric (A : Finset V) (q : V → V → ℝ)
    (h0 : ∀ u ∈ A, ∀ v ∈ A, 0 ≤ q u v)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → (1 : ℝ) / 2 ≤ q u v + q v u)
    (p : ℝ) (hp : 0 ≤ p) :
    ∑ u ∈ A, Real.exp (-p * degree A q u) ≤
      ∑ i ∈ Finset.range A.card, (Real.exp (-p / 4)) ^ i := by
  let L := A.toList.mergeSort (fun u v => decide (degree A q u ≤ degree A q v))
  have hperm : L.Perm A.toList := List.mergeSort_perm _ _
  have hsorted : L.Pairwise fun u v => degree A q u ≤ degree A q v := by
    have h := List.pairwise_mergeSort
      (le := fun u v => decide (degree A q u ≤ degree A q v))
      (fun a b c h1 h2 => by
        exact of_decide_eq_true h1 |>.trans (of_decide_eq_true h2) |> decide_eq_true)
      (fun a b => by
        rcases le_total (degree A q a) (degree A q b) with h | h <;> simp [h])
      A.toList
    simpa only [decide_eq_true_eq] using h
  have hn : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList A)
  have hlength : L.length = A.card := by simpa using hperm.length_eq
  have heq : (∑ u ∈ A, Real.exp (-p * degree A q u)) =
      ∑ i : Fin L.length, Real.exp (-p * degree A q (L.get i)) := by
    symm
    apply Finset.sum_bij (fun i _ => L.get i)
    · intro i _
      exact Finset.mem_toList.mp (hperm.mem_iff.mp (List.get_mem L i))
    · intro i _ j _ he
      exact hn.injective_get he
    · intro u hu
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hperm.mem_iff.mpr (Finset.mem_toList.mpr hu))
      exact ⟨i, Finset.mem_univ _, hi⟩
    · intro i _
      rfl
  rw [heq]
  calc
    _ ≤ ∑ i : Fin L.length, Real.exp (-p * (i.val : ℝ) / 4) := by
      apply Finset.sum_le_sum
      intro i _
      apply Real.exp_le_exp.mpr
      have := sorted_degree_lower A q h0 hpair L hperm hsorted i
      nlinarith
    _ = ∑ i ∈ Finset.range L.length, (Real.exp (-p / 4)) ^ i := by
      simp_rw [show ∀ i : Fin L.length, -p * (i.val : ℝ) / 4 =
        (i.val : ℝ) * (-p / 4) by intro i; ring, Real.exp_nat_mul]
      exact Fin.sum_univ_eq_sum_range (fun k : ℕ => Real.exp (-p / 4) ^ k) L.length
    _ = _ := by rw [hlength]

theorem one_sub_exp_lower (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    p / 8 ≤ 1 - Real.exp (-p / 4) := by
  have he0 := Real.exp_pos (-p / 4)
  have he1 : Real.exp (-p / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hx := Real.add_one_le_exp (p / 4)
  have hm := mul_le_mul_of_nonneg_right hx he0.le
  have he : Real.exp (p / 4) * Real.exp (-p / 4) = 1 := by
    rw [← Real.exp_add]
    have hz : p / 4 + -p / 4 = 0 := by ring
    rw [hz, Real.exp_zero]
  rw [he] at hm
  have hn := mul_nonneg (sub_nonneg.mpr he1) (show 0 ≤ 1 - p / 4 by linarith)
  nlinarith

theorem geometric_exp_le (n : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ Finset.range n, (Real.exp (-p / 4)) ^ i) ≤ 8 / p := by
  let r := Real.exp (-p / 4)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hden : 0 < 1 - r := by
    have := one_sub_exp_lower p hp hp1
    dsimp [r]
    linarith
  have hg := geom_sum_mul_neg r n
  have hn : 0 ≤ r ^ n := pow_nonneg hr0 n
  have hsum : (∑ i ∈ Finset.range n, r ^ i) ≤ 1 / (1 - r) :=
    (le_div_iff₀ hden).mpr (by nlinarith)
  have hd := one_sub_exp_lower p hp hp1
  have hh : 1 / (1 - r) ≤ 1 / (p / 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hd
  have he : (1 : ℝ) / (p / 8) = 8 / p := by ring
  exact hsum.trans (hh.trans_eq he)

/-- A fractional tournament with only half a unit of pairwise killing still
has `O(1/p)` expected survivors. No bound on the number of sampled pivots
and no exceptional Chernoff event is required. -/
theorem exp_sum_le (A : Finset V) (q : V → V → ℝ)
    (h0 : ∀ u ∈ A, ∀ v ∈ A, 0 ≤ q u v)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → (1 : ℝ) / 2 ≤ q u v + q v u)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑ u ∈ A, Real.exp (-p * degree A q u) ≤ 8 / p :=
  (exp_sum_le_geometric A q h0 hpair p hp.le).trans (geometric_exp_le _ p hp hp1)

theorem product_survival_le_exp (A : Finset V) (q : V → V → ℝ)
    (_h0 : ∀ u ∈ A, ∀ v ∈ A, 0 ≤ q u v)
    (h1 : ∀ u ∈ A, ∀ v ∈ A, q u v ≤ 1)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) {u : V} (hu : u ∈ A) :
    (∏ v ∈ A.erase u, (1 - p * q u v)) ≤ Real.exp (-p * degree A q u) := by
  have hle :
      (∏ v ∈ A.erase u, (1 - p * q u v)) ≤
        ∏ v ∈ A.erase u, Real.exp (-p * q u v) := by
    apply Finset.prod_le_prod₀
    · intro v hv
      have hvA := Finset.mem_of_mem_erase hv
      nlinarith [h1 u hu v hvA]
    · intro v _
      linarith [Real.add_one_le_exp (-p * q u v)]
  have hdegree : degree A q u = ∑ v ∈ A.erase u, q u v := by
    rw [degree, ← Finset.sum_erase_add _ _ hu]
    simp only [off, ite_true, add_zero]
    apply Finset.sum_congr rfl
    intro v hv
    simp [(Finset.ne_of_mem_erase hv).symm]
  rw [hdegree, Finset.mul_sum]
  simpa only [Real.exp_sum] using hle

theorem product_survival_sum_le (A : Finset V) (q : V → V → ℝ)
    (h0 : ∀ u ∈ A, ∀ v ∈ A, 0 ≤ q u v)
    (h1 : ∀ u ∈ A, ∀ v ∈ A, q u v ≤ 1)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v → (1 : ℝ) / 2 ≤ q u v + q v u)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑ u ∈ A, ∏ v ∈ A.erase u, (1 - p * q u v) ≤ 8 / p := by
  exact (Finset.sum_le_sum fun u hu =>
    product_survival_le_exp A q h0 h1 p hp.le hp1 hu).trans
      (exp_sum_le A q h0 hpair p hp hp1)

end Fractional

end

end StreamingReachability.Early
