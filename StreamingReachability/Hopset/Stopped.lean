module

public import StreamingReachability.Hopset.CopyFlow

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical

noncomputable section

variable {n : ℕ}

def stoppedKernel (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (r : ℕ) (S : Finset (Fin n)) :
    Law (Branching.Step (Finset (Fin n)) (Choice n cfg)) :=
  if BallsGood cfg stored input r S then kernel cfg hn stored input ranks r S
  else Law.pure ⟨⟨∅, fun _ => (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)⟩, []⟩

def copyCharge (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n)
    (r : ℕ) (S : Finset (Fin n)) (_step : Branching.Step (Finset (Fin n)) (Choice n cfg)) : ℕ :=
  if BallsGood cfg stored input r S ∧ v ∈ S then 1 else 0

def copyPotential (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (fuel r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) : ℝ :=
  Branching.potential (stoppedKernel cfg hn stored input ranks)
    (copyCharge cfg stored input v) fuel r S

theorem copyPotential_zero (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) :
    copyPotential cfg hn stored input v 0 r S ranks = 0 := rfl

theorem copyPotential_nonneg (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (fuel r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) :
    0 ≤ copyPotential cfg hn stored input v fuel r S ranks :=
  Branching.potential_nonneg _ _ _ _ _

theorem copyPotential_succ (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (fuel r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) :
    copyPotential cfg hn stored input v (fuel + 1) r S ranks =
      if BallsGood cfg stored input r S then
        (if v ∈ S then (1 : ℝ) else 0) +
          (kernel cfg hn stored input ranks r S).expect (fun step =>
            (step.children.map fun T => copyPotential cfg hn stored input v fuel (r + 1) T ranks).sum)
      else 0 := by
  by_cases hg : BallsGood cfg stored input r S
  · simp only [copyPotential, Branching.potential, stoppedKernel, hg, ↓reduceIte]
    have he : (fun step : Branching.Step (Finset (Fin n)) (Choice n cfg) =>
        ((copyCharge cfg stored input v r S step : ℕ) : ℝ)) =
        fun _ => if v ∈ S then (1 : ℝ) else 0 := by
      funext step
      by_cases hv : v ∈ S <;> simp [copyCharge, hg, hv]
    rw [Law.expect_add, he, Law.expect_const]
  · simp [copyPotential, Branching.potential, stoppedKernel, copyCharge, hg]

theorem copyPotential_outside (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (fuel r : ℕ) (S : Finset (Fin n))
    (hv : v ∉ S) (ranks : Fin n → ℕ) :
    copyPotential cfg hn stored input v fuel r S ranks = 0 := by
  induction fuel generalizing r S with
  | zero => rfl
  | succ fuel ih =>
      rw [copyPotential_succ]
      by_cases hg : BallsGood cfg stored input r S
      · simp only [hg, hv, ↓reduceIte, zero_add]
        rw [kernel, Law.expect_map]
        have he (choice : Choice n cfg) :
            ((children cfg stored input r S choice).map fun T =>
              copyPotential cfg hn stored input v fuel (r + 1) T ranks).sum = 0 := by
          apply List.sum_eq_zero
          intro a ha
          obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
          apply ih (r + 1) T
          intro hvT
          exact hv (children_subset cfg stored input r S choice T hT hvT)
        simp only [he, Law.expect_const]
      · simp [hg]

end

end StreamingReachability.Hopset.Reference
