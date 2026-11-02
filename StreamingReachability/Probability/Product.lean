module

public import StreamingReachability.Probability.Projection

@[expose] public section

namespace StreamingReachability.Law

open scoped Classical BigOperators

variable {A : Type*}

def rowsFromFlat (m n : ℕ) (xs : Fin (m * n) → A) : Fin m → Fin n → A :=
  fun i j => xs (finProdFinEquiv (i, j))

theorem family_rows_probability (m n : ℕ) (mu : Law A) (target : Fin m → Fin n → A) :
    (family m (fun _ => family n (fun _ => mu))).prob (· = target) =
      ∏ i : Fin m, ∏ j : Fin n, mu.prob (· = target i j) := by
  have ho := family_projection_probability m m (fun _ => family n (fun _ => mu))
    (fun i => i) Function.injective_id target
  change (family m (fun _ => family n (fun _ => mu))).prob (· = target) = _ at ho
  rw [ho]
  apply Finset.prod_congr rfl
  intro i _
  exact family_projection_probability n n (fun _ => mu) (fun j => j) Function.injective_id (target i)

theorem family_flat_rows_probability (m n : ℕ) (mu : Law A) (target : Fin m → Fin n → A) :
    (family (m * n) (fun _ => mu)).prob (fun xs => rowsFromFlat m n xs = target) =
      ∏ i : Fin m, ∏ j : Fin n, mu.prob (· = target i j) := by
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  have he :
      (fun xs : Fin (m * n) → A => rowsFromFlat m n xs = target) =
        fun xs => ∀ k, xs k = target (e.symm k).1 (e.symm k).2 := by
    funext xs
    apply propext
    constructor
    · intro h k
      have hk := congrFun (congrFun h (e.symm k).1) (e.symm k).2
      change xs (e (e.symm k)) = target (e.symm k).1 (e.symm k).2 at hk
      simpa only [Equiv.apply_symm_apply] using hk
    · intro h
      funext i j
      change xs (e (i, j)) = target i j
      simpa only [Equiv.symm_apply_apply] using h (e (i, j))
  rw [he, family_probability (m * n) (fun _ => mu)
    (fun k a => a = target (e.symm k).1 (e.symm k).2),
    ← Fintype.prod_prod_type (fun ij : Fin m × Fin n => mu.prob (fun a => a = target ij.1 ij.2))]
  refine Finset.prod_bij (fun k _ => e.symm k) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro k hk l hl hkl
    exact e.symm.injective hkl
  · intro ij hij
    exact ⟨e ij, Finset.mem_univ _, e.symm_apply_apply ij⟩
  · intro k hk
    rfl

theorem family_rows [Fintype A] (m n : ℕ) (mu : Law A)
    (f : (Fin m → Fin n → A) → ℝ) :
    (family m (fun _ => family n (fun _ => mu))).expect f =
      (family (m * n) (fun _ => mu)).expect (fun xs => f (rowsFromFlat m n xs)) := by
  rw [← expect_map (family (m * n) (fun _ => mu)) (rowsFromFlat m n) f,
    expect_finite, expect_finite]
  apply Finset.sum_congr rfl
  intro target _
  congr 1
  rw [prob_map, family_rows_probability, family_flat_rows_probability]

end StreamingReachability.Law
