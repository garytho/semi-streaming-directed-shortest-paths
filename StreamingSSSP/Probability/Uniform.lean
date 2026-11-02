module

public import StreamingSSSP.Probability

@[expose] public section

namespace StreamingSSSP.Law

open scoped Classical BigOperators

noncomputable def uniform (n : ℕ) (hn : 0 < n) : Law (Fin n) where
  atoms := List.ofFn fun i : Fin n => (i, 1 / (n : ℝ))
  nonneg := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    positivity
  total := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [weightedSum, List.map_ofFn, List.sum_ofFn, hn']

theorem expect_uniform {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    (uniform n hn).expect f = (∑ i, f i) / (n : ℝ) := by
  simp only [expect, uniform, weightedSum, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  rw [← Finset.mul_sum]
  ring

theorem prob_uniform {n : ℕ} (hn : 0 < n) (P : Fin n → Prop) :
    (uniform n hn).prob P =
      ((Finset.univ.filter P).card : ℝ) / (n : ℝ) := by
  rw [prob, expect_uniform]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

noncomputable def uniformPair (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Law (Fin m × Fin n) :=
  (uniform m hm).bind fun i => (uniform n hn).map fun j => (i, j)

theorem expect_uniformPair {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (f : Fin m × Fin n → ℝ) :
    (uniformPair m n hm hn).expect f = (∑ z, f z) / ((m : ℝ) * n) := by
  rw [uniformPair, expect_bind]
  simp_rw [expect_map, expect_uniform]
  rw [← Finset.sum_div, Fintype.sum_prod_type]
  simp only [div_div, mul_comm]

theorem prob_uniformPair {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (P : Fin m × Fin n → Prop) :
    (uniformPair m n hm hn).prob P =
      ((Finset.univ.filter P).card : ℝ) / ((m : ℝ) * n) := by
  rw [prob, expect_uniformPair]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end StreamingSSSP.Law
