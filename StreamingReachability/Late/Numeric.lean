module

public import StreamingReachability.Late.Expectation
public import StreamingReachability.Late.Selection

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical
open Early Implicit

noncomputable section

theorem source_boundary_numeric (b k M ell : ℕ) (p : ℝ)
    (hk : 2 ≤ k) (he : 0 < ell) (hp : 0 ≤ p)
    (hgroups : 384 * 100 ^ 2 * k ^ 2 * ell ^ 2 ≤ M)
    (hbp : (b : ℝ) * p ≤ 2 * 100 * k * ell) :
    48 * (b : ℝ) * p / M ≤ 1 / (4 * 100 * k * ell) ∧
      1 / (4 * 100 * (k : ℝ) * ell) ≤ (1 : ℝ) / 2 := by
  have hk0 : 0 < k := by omega
  have hM : 0 < M := lt_of_lt_of_le (by positivity) hgroups
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk0
  have he' : (0 : ℝ) < ell := by exact_mod_cast he
  have hgroups' : 384 * (100 : ℝ) ^ 2 * (k : ℝ) ^ 2 * (ell : ℝ) ^ 2 ≤ M := by
    exact_mod_cast hgroups
  refine ⟨boundary_numeric b p M 100 k ell (Nat.cast_nonneg _) hp hM'
    (by norm_num) hk' he' hbp hgroups', ?_⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have he1 : (1 : ℝ) ≤ ell := by exact_mod_cast he
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * 100 * (k : ℝ) * ell)
    (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith

namespace Config

theorem small_charge_of_source (C : Config) (ell : ℕ) (hk : 2 ≤ C.k) (he : 0 < ell)
    (hgroups : 384 * 100 ^ 2 * C.k ^ 2 * ell ^ 2 ≤ C.M)
    (hbp : ∀ r, (C.ballBound r : ℝ) * C.rate r ≤ 2 * 100 * C.k * ell) :
    ∀ r, 48 * (C.ballBound r : ℝ) * C.rate r / C.M ≤ (1 : ℝ) / 2 :=
  fun r => (source_boundary_numeric (C.ballBound r) C.k C.M ell (C.rate r)
    hk he (C.rate_nonneg r) hgroups (hbp r)).1.trans
      (source_boundary_numeric (C.ballBound r) C.k C.M ell (C.rate r)
        hk he (C.rate_nonneg r) hgroups (hbp r)).2

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem boundary_expectation_source (C : Config) (ell : ℕ)
    (hk : 2 ≤ C.k) (he : 0 < ell)
    (hgroups : 384 * 100 ^ 2 * C.k ^ 2 * ell ^ 2 ≤ C.M)
    (Q : Path R G s t) (r : ℕ) (S : Finset (Fin n)) (D : ℝ) (hS : Q.Inside S)
    (hD : 0 < D) (hgrid : D ≤ C.N) (hshort : (Q.searchWeight C.A : ℝ) ≤ D)
    (hballs : C.BallsGood R G r S D)
    (hbp : (C.ballBound r : ℝ) * C.rate r ≤ 2 * 100 * C.k * ell) :
    (C.fresh S r).expect (fun xs => (C.boundaryCount R G Q S D xs : ℝ)) ≤
      1 / (4 * 100 * C.k * ell) :=
  (C.boundary_expectation Q r S D hS hD hgrid hshort hballs).trans
    (source_boundary_numeric (C.ballBound r) C.k C.M ell (C.rate r)
      hk he (C.rate_nonneg r) hgroups hbp).1

theorem expected_stopped_hops_source (C : Config) (ell : ℕ)
    (hk : 2 ≤ C.k) (he : 0 < ell)
    (hgroups : 384 * 100 ^ 2 * C.k ^ 2 * ell ^ 2 ≤ C.M)
    (hbp : ∀ r, (C.ballBound r : ℝ) * C.rate r ≤ 2 * 100 * C.k * ell)
    (r : ℕ) (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (hS : Q.Inside S) (hD : 0 < D) (hgrid : D ≤ C.N)
    (hshort : (Q.searchWeight C.A : ℝ) ≤ D) :
    (C.law R G r S D).expect (C.stoppedHops R G Q r S D) ≤
      (14 : ℝ) ^ (r + 1) :=
  C.expected_stopped_hops (C.small_charge_of_source ell hk he hgroups hbp)
    r Q S D hS hD hgrid hshort

/-- The returned objects are genuine simple paths in the exact represented
graph. The expectation is stopped on the stated good-ball event, never
conditioned on that event. Here `r = rmax - currentLevel`. -/
theorem streaming_late_shortening (C : Config) (ell : ℕ)
    (hk : 2 ≤ C.k) (he : 0 < ell)
    (hgroups : 384 * 100 ^ 2 * C.k ^ 2 * ell ^ 2 ≤ C.M)
    (hbp : ∀ r, (C.ballBound r : ℝ) * C.rate r ≤ 2 * 100 * C.k * ell)
    (r : ℕ) (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (hS : Q.Inside S) (hD : 0 < D) (hgrid : D ≤ C.N)
    (hshort : (Q.searchWeight C.A : ℝ) ≤ D) :
    ∃ shortcut : List (C.Stage n) → List (Fin n),
      (∀ run, (shortcut run).Nodup ∧ Graph.Endpoints (shortcut run) s t ∧
        (C.graph R G S D run).pathCost (shortcut run) ≤ (Q.micro : Distance)) ∧
      (C.law R G r S D).expect (fun run =>
        if C.Good R G r S D run then (((shortcut run).length - 1 : ℕ) : ℝ) else 0) ≤
          (14 : ℝ) ^ (r + 1) := by
  refine ⟨fun run => (C.path R G Q S D run).vertices, ?_, ?_⟩
  · intro run
    exact ⟨C.path_simple R G Q S D run, (C.path R G Q S D run).endpoints,
      (C.path R G Q S D run).cost_le⟩
  · exact C.expected_stopped_hops_source ell hk he hgroups hbp r Q S D
      hS hD hgrid hshort

end Config

end

end StreamingReachability.Late
