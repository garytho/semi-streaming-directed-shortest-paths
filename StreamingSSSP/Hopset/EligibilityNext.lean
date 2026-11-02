module

public import StreamingSSSP.Hopset.PrefixTransitions

@[expose] public section

namespace StreamingSSSP.RankPrefix

open scoped Classical

noncomputable section

theorem nextKnown_none_iff (r : ℕ) (known : Option (Fin r)) (coin : Bool) :
    nextKnown r known coin = none ↔ known = none ∧ coin = false := by
  cases known <;> cases coin <;> simp [nextKnown]

variable {n : ℕ}

theorem mem_eligible_next (r : ℕ) (known : Fin n → Option (Fin r)) (coins : Fin n → Bool)
    (X : Finset (Fin n)) (v : Fin n) :
    v ∈ eligible (r + 1) (fun w => nextKnown r (known w) (coins w)) X ↔
      v ∈ X ∧ known v = none ∧ coins v = false := by
  unfold eligible
  rw [Finset.mem_filter, nextKnown_none_iff]

theorem eligible_next_subset (r : ℕ) (known : Fin n → Option (Fin r)) (coins : Fin n → Bool)
    (X S : Finset (Fin n)) (hXS : X ⊆ S) :
    eligible (r + 1) (fun w => nextKnown r (known w) (coins w)) X ⊆ eligible r known S := by
  intro v hv
  obtain ⟨hvX, hk, _⟩ := (mem_eligible_next r known coins X v).mp hv
  exact Finset.mem_filter.mpr ⟨hXS hvX, hk⟩

theorem eligible_next_not_pivot (r : ℕ) (known : Fin n → Option (Fin r)) (coins : Fin n → Bool)
    (X S : Finset (Fin n)) (v : Fin n)
    (hv : v ∈ eligible (r + 1) (fun w => nextKnown r (known w) (coins w)) X) :
    v ∉ S.filter (fun w => coins w = true) := by
  have hf := ((mem_eligible_next r known coins X v).mp hv).2.2
  intro hp
  have ht := (Finset.mem_filter.mp hp).2
  rw [hf] at ht
  contradiction

end

end StreamingSSSP.RankPrefix
