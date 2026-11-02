module

public import StreamingReachability.Late.Paths
public import StreamingReachability.Hopset.Protocol

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical
open Early

noncomputable section

variable {n : ℕ}

def shellScore (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ)
    (p : Fin n) (sigma : Fin M) (phi : Fin N) (j : ℕ) : ℕ :=
  (fringe H p
    ((lambda k M + (4 * k : ℕ) * (sigma.val : ℝ) + (j : ℝ) + shiftValue phi) * D) D).card

/-- This uses the controller's actual first-minimum `argmin`, including its
tie rule, rather than choosing an arbitrary minimum-shell certificate. -/
def candidate (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (p : Fin n) (sigma : Fin M) (phi : Fin N) : Fin (4 * k) :=
  ⟨Hopset.argmin (shellScore H D k M N p sigma phi) (4 * k),
    Hopset.argmin_lt _ _ (by omega)⟩

def radius (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (p : Fin n) (z : Fin M × Fin N) : ℝ :=
  candidateRadius (lambda k M) (4 * k) z.1
    (candidate H D k M N hk p z.1 z.2) (shiftValue z.2) D

theorem candidate_minimal (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (p : Fin n) (z : Fin M × Fin N) (j : Fin (4 * k)) :
    (fringe H p (radius H D k M N hk p z) D).card ≤
      (fringe H p (candidateRadius (lambda k M) (4 * k) z.1 j (shiftValue z.2) D) D).card := by
  exact Hopset.argmin_minimal (shellScore H D k M N p z.1 z.2) (4 * k) j.val j.isLt

theorem radius_bounds (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (hD : 0 < D) (p : Fin n) (z : Fin M × Fin N) :
    lambda k M * D ≤ radius H D k M N hk p z ∧
      radius H D k M N hk p z < nearRadius k M D :=
  early_candidate_bounds k M N hk hD z.1 z.2 _

theorem argmin_congr_below (f g : ℕ → ℕ) (width : ℕ)
    (h : ∀ j < width, f j = g j) : Hopset.argmin f width = Hopset.argmin g width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      have hp := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have hb : Hopset.argmin g width < width + 1 := by
        by_cases hw : width = 0
        · subst width
          simp [Hopset.argmin]
        · exact Nat.lt_succ_of_lt (Hopset.argmin_lt g width (Nat.pos_of_ne_zero hw))
      simp only [Hopset.argmin, hp, h width (Nat.lt_succ_self _), h _ hb]

theorem candidate_eq_actual_argmin (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ)
    (hk : 0 < k) (p : Fin n) (sigma : Fin M) (phi : Fin N) (score : ℕ → ℕ)
    (hscore : ∀ j < 4 * k, shellScore H D k M N p sigma phi j = score j) :
    (candidate H D k M N hk p sigma phi).val = Hopset.argmin score (4 * k) :=
  argmin_congr_below _ score _ hscore

end

end StreamingReachability.Late
