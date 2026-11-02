module

public import StreamingSSSP.Probability.Projection

@[expose] public section

namespace StreamingSSSP.Law

open scoped Classical

variable {A I : Type*}

def sampleIndices (mu : I → Law A) : List I → Law (List A)
  | [] => pure []
  | i :: indices => (mu i).bind fun a => (sampleIndices mu indices).map (a :: ·)

theorem sampleIndices_congr (mu nu : I → Law A) (indices : List I)
    (h : ∀ i ∈ indices, mu i = nu i) : sampleIndices mu indices = sampleIndices nu indices := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      have hh := h i (by simp)
      have ht := ih (fun j hj => h j (by simp [hj]))
      simp only [sampleIndices, hh, ht]

theorem expect_sampleIndices (mu : I → Law A) (indices : List I) (f : List A → ℝ) :
    (sampleIndices mu indices).expect f =
      (family indices.length (fun j => mu (indices.get j))).expect (fun xs => f (List.ofFn xs)) := by
  induction indices generalizing f with
  | nil => simp [sampleIndices, family]
  | cons i indices ih =>
      rw [sampleIndices, expect_bind]
      simp only [List.length_cons, expect_family_succ, expect_map]
      apply congrArg (mu i).expect
      funext a
      rw [ih (fun xs => f (a :: xs))]
      simp only [List.ofFn_succ, Fin.cases_zero, Fin.cases_succ]
      rfl

theorem expect_sampleIndices_projection [Fintype A] (n : ℕ) (mu : Fin n → Law A)
    (indices : List (Fin n)) (hindices : indices.Nodup) (f : List A → ℝ) :
    (sampleIndices mu indices).expect f =
      (family n mu).expect (fun xs => f (indices.map xs)) := by
  rw [expect_sampleIndices]
  have he :
      (fun xs : Fin n → A => f (indices.map xs)) =
        fun xs => f (List.ofFn (fun j => xs (indices.get j))) := by
    funext xs
    apply congrArg f
    have h := congrArg (List.map xs) (List.ofFn_get indices)
    simpa only [List.map_ofFn, Function.comp_def] using h.symm
  rw [he]
  exact (family_projection n indices.length mu indices.get hindices.injective_get
    (fun xs => f (List.ofFn xs))).symm

end StreamingSSSP.Law
