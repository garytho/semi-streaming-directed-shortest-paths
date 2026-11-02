module

public import StreamingReachability.Late.Run

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

namespace Config

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t : Fin n}

theorem sum_constant {T : Type*} (xs : List T) (H : ℝ) :
    (xs.map fun _ => H).sum = (xs.length : ℝ) * H := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
      ring

def boundaryCount (C : Config) (R : Representation n) (G : Graph (Fin n))
    (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) : ℕ :=
  type3Count Q (C.search R G S) S (Sampling.pivots xs)
    (C.radii (C.search R G S) D xs) D (searchRadius C.k C.M D)

theorem boundary_expectation (C : Config) (Q : Path R G s t) (r : ℕ)
    (S : Finset (Fin n)) (D : ℝ) (hS : Q.Inside S)
    (hD : 0 < D) (hgrid : D ≤ C.N) (hshort : (Q.searchWeight C.A : ℝ) ≤ D)
    (hballs : C.BallsGood R G r S D) :
    (C.fresh S r).expect (fun xs => (C.boundaryCount R G Q S D xs : ℝ)) ≤
      48 * C.ballBound r * C.rate r / C.M := by
  have hs : s ∈ S := hS s Q.endpoints_support.1
  have ht : t ∈ S := hS t Q.endpoints_support.2
  exact expected_type3 Q C.A C.positive_rounding S S hS D hD hshort
    C.k C.M C.N (C.ballBound r) C.positive_k C.positive_groups C.positive_shifts hgrid
    (hballs t ht).1 (hballs s hs).2 (C.rate r) (C.rate_nonneg r) (C.rate_le_one r)

theorem step_expectation (C : Config) (Q : Path R G s t) (r : ℕ)
    (S : Finset (Fin n)) (D : ℝ) (hS : Q.Inside S)
    (hD : 0 < D) (hshort : (Q.searchWeight C.A : ℝ) ≤ D)
    (xs : C.Stage n) (mu : Law (List (C.Stage n))) (H : ℝ) (hH : 0 ≤ H)
    (hfuture : ∀ P : ChildPiece R G (C.child R G S D xs) C.A (D / 4),
      mu.expect (C.stoppedHops R G P.path r (C.child R G S D xs) (D / 4)) ≤ H) :
    mu.expect (fun ys => C.stoppedHops R G Q (r + 1) S D (xs :: ys)) ≤
      8 + C.boundaryCount R G Q S D xs +
        (5 + C.boundaryCount R G Q S D xs) * H := by
  let X := C.child R G S D xs
  let F₀ := C.stageGraph R G S D xs
  have hplan : ∃ B : Plan R G F₀ X C.A (D / 4) Q,
      B.overhead ≤ 8 + C.boundaryCount R G Q S D xs ∧
      B.pieces.length ≤ 5 + C.boundaryCount R G Q S D xs := by
    exact exists_plan_at Q C.A C.positive_rounding S
      (Sampling.pivots xs) hS (C.radii (C.search R G S) D xs) D (searchRadius C.k C.M D)
      hD hshort F₀ (C.stage_le_original R G S D xs)
      (fun p hp => C.stage_le_block R G S D xs hp)
  obtain ⟨B, hBover, hBpieces⟩ := hplan
  let children := fun ys (P : ChildPiece R G X C.A (D / 4)) =>
    (C.path R G P.path X (D / 4) ys).mono (C.graph_cons_le_child R G S D xs ys)
  have hpoint (ys : List (C.Stage n)) :
      C.stoppedHops R G Q (r + 1) S D (xs :: ys) ≤ (B.overhead : ℝ) +
        (B.pieces.map fun P => C.stoppedHops R G P.path r X (D / 4) ys).sum := by
    by_cases hg : C.Good R G (r + 1) S D (xs :: ys)
    · have hchild : C.Good R G r X (D / 4) ys := hg.2
      have hbest := Route.best_le _ (Q.originalRoute _
        (C.graph_le_original R G S D (xs :: ys)))
        (B.build _ (C.graph_cons_le_stage R G S D xs ys) (children ys))
      have hbuild := B.hops _ (C.graph_cons_le_stage R G S D xs ys) (children ys)
      have hbound := hbest.trans hbuild
      have hcast := (show ((C.path R G Q S D (xs :: ys)).hops : ℝ) ≤
          (B.overhead : ℝ) + (B.pieces.map fun P => ((children ys P).hops : ℝ)).sum from by
        have h := (show ((C.path R G Q S D (xs :: ys)).hops : ℝ) ≤
            ((B.overhead + (B.pieces.map fun P => (children ys P).hops).sum : ℕ) : ℝ) from by
          exact_mod_cast hbound)
        rw [Nat.cast_add, Nat.cast_list_sum, List.map_map] at h
        exact h)
      simpa only [stoppedHops, ite_eq_left hg, ite_eq_left hchild, children,
        Route.hops_mono] using hcast
    · simp only [stoppedHops, ite_eq_right hg]
      apply add_nonneg (Nat.cast_nonneg _)
      apply List.sum_nonneg
      intro a ha
      obtain ⟨P, _, rfl⟩ := List.mem_map.mp ha
      exact C.stoppedHops_nonneg R G P.path r X (D / 4) ys
  have h := mu.expect_mono hpoint
  rw [Law.expect_add, Law.expect_const, expect_list_sum] at h
  have hsum : (B.pieces.map fun P =>
      mu.expect (C.stoppedHops R G P.path r X (D / 4))).sum ≤
        (B.pieces.length : ℝ) * H := by
    apply (List.sum_le_sum (fun P _ => hfuture P)).trans_eq
    exact sum_constant B.pieces H
  have hover : (B.overhead : ℝ) ≤ 8 + C.boundaryCount R G Q S D xs := by
    exact_mod_cast hBover
  have hpieces : (B.pieces.length : ℝ) ≤ 5 + C.boundaryCount R G Q S D xs := by
    exact_mod_cast hBpieces
  exact h.trans ((add_le_add_right hsum _).trans
    (add_le_add hover (mul_le_mul_of_nonneg_right hpieces hH)))

/-- This is a raw expectation of the stopped (good-event-weighted) hop count.
No current owner law is conditioned on a future good-ball event. -/
theorem expected_stopped_hops (C : Config)
    (hsmall : ∀ r, 48 * (C.ballBound r : ℝ) * C.rate r / C.M ≤ (1 : ℝ) / 2)
    (r : ℕ) (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (hS : Q.Inside S) (hD : 0 < D) (hgrid : D ≤ C.N)
    (hshort : (Q.searchWeight C.A : ℝ) ≤ D) :
    (C.law R G r S D).expect (C.stoppedHops R G Q r S D) ≤
      (14 : ℝ) ^ (r + 1) := by
  induction r generalizing s t S D with
  | zero =>
      rw [law, Law.expect_map]
      have hpoint : Sampling.Holds (C.allOwners S.toList) (fun xs =>
          C.stoppedHops R G Q 0 S D [xs] ≤ (1 : ℝ)) := by
        refine Sampling.holds_mono (C.allOwners_pivots S) ?_
        intro xs hxs
        have hblocks (p : Fin n) (hp : p ∈ S) (u v : Fin n) :
            C.graph R G S D [xs] u v ≤ closure (R.base G)
              (block (C.search R G S) S p (C.radii (C.search R G S) D xs p) D) u v :=
          (C.graph_cons_le_stage R G S D xs [] u v).trans
            (C.stage_le_block R G S D xs (by rwa [hxs]) u v)
        obtain ⟨P, hP⟩ := final_level_shortcut Q C.A C.positive_rounding S hS
          (C.radii (C.search R G S) D xs) D hshort
          (fun p _ => C.radii_nonneg R G S D hD xs p) _ hblocks
        have hbest := Route.best_le _ (Q.originalRoute _
          (C.graph_le_original R G S D [xs])) P
        have hh : (C.path R G Q S D [xs]).hops ≤ 1 := hbest.trans hP
        simpa [stoppedHops, Good]
          using (show ((C.path R G Q S D [xs]).hops : ℝ) ≤ 1 from by exact_mod_cast hh)
      have h := Sampling.expect_mono_on _ hpoint
      rw [Law.expect_const] at h
      exact h.trans (by norm_num)
  | succ r ih =>
      by_cases hballs : C.BallsGood R G (r + 1) S D
      · rw [law, Law.expect_bind]
        simp_rw [Law.expect_map]
        let H : ℝ := 14 ^ (r + 1)
        have hH : 1 ≤ H := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 14)
        have hDnext : 0 < D / 4 := by positivity
        have hgridnext : D / 4 ≤ C.N := by
          have hN0 : (0 : ℝ) ≤ C.N := Nat.cast_nonneg _
          linarith
        have hstep (xs : C.Stage n) :
            (C.law R G r (C.child R G S D xs) (D / 4)).expect
                (fun ys => C.stoppedHops R G Q (r + 1) S D (xs :: ys)) ≤
              8 + C.boundaryCount R G Q S D xs +
                (5 + C.boundaryCount R G Q S D xs) * H := by
          apply C.step_expectation Q r S D hS hD hshort xs _ H (by linarith)
          intro P
          exact ih P.path (C.child R G S D xs) (D / 4) P.inside hDnext hgridnext P.short
        have h := (C.fresh S (r + 1)).expect_mono hstep
        have hm := (C.boundary_expectation Q (r + 1) S D hS hD hgrid hshort hballs).trans
          (hsmall (r + 1))
        let E := (C.fresh S (r + 1)).expect (fun xs =>
          (C.boundaryCount R G Q S D xs : ℝ))
        have hlinear :
            (C.fresh S (r + 1)).expect (fun xs =>
              8 + (C.boundaryCount R G Q S D xs : ℝ) +
                (5 + C.boundaryCount R G Q S D xs) * H) =
              8 + E + (5 + E) * H := by
          have he : (fun xs : C.Stage n =>
              8 + (C.boundaryCount R G Q S D xs : ℝ) +
                (5 + C.boundaryCount R G Q S D xs) * H) =
              fun xs => (8 + 5 * H) + (1 + H) * (C.boundaryCount R G Q S D xs : ℝ) := by
            funext xs
            ring
          rw [he, Law.expect_add, Law.expect_const, Law.expect_mul]
          dsimp only [E]
          ring
        rw [hlinear] at h
        have hbound : 8 + E + (5 + E) * H ≤ 14 * H := by
          change E ≤ (1 : ℝ) / 2 at hm
          nlinarith
        apply h.trans (hbound.trans_eq ?_)
        change 14 * 14 ^ (r + 1) = 14 ^ ((r + 1) + 1)
        rw [pow_succ]
        ring
      · have hz (run : List (C.Stage n)) : C.stoppedHops R G Q (r + 1) S D run = 0 := by
          cases run <;> simp [stoppedHops, Good, hballs]
        have hf : C.stoppedHops R G Q (r + 1) S D = fun _ => 0 := funext hz
        rw [hf, Law.expect_const]
        positivity

theorem expected_hops_of_good (C : Config)
    (hsmall : ∀ r, 48 * (C.ballBound r : ℝ) * C.rate r / C.M ≤ (1 : ℝ) / 2)
    (r : ℕ) (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (hS : Q.Inside S) (hD : 0 < D) (hgrid : D ≤ C.N)
    (hshort : (Q.searchWeight C.A : ℝ) ≤ D)
    (hgood : Sampling.Holds (C.law R G r S D) (C.Good R G r S D)) :
    (C.law R G r S D).expect (fun run => ((C.path R G Q S D run).hops : ℝ)) ≤
      (14 : ℝ) ^ (r + 1) := by
  have h := Sampling.expect_mono_on _ (Sampling.holds_mono hgood (fun run hg =>
    show ((C.path R G Q S D run).hops : ℝ) ≤ C.stoppedHops R G Q r S D run from by
      simp [stoppedHops, hg]))
  exact h.trans (C.expected_stopped_hops hsmall r Q S D hS hD hgrid hshort)

/-- Parent controllers can subtract their bad-ball/abort probability here,
rather than reusing the uniform owner bound after conditioning on success. -/
theorem hop_failure_bound (C : Config)
    (hsmall : ∀ r, 48 * (C.ballBound r : ℝ) * C.rate r / C.M ≤ (1 : ℝ) / 2)
    (r : ℕ) (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (hS : Q.Inside S) (hD : 0 < D) (hgrid : D ≤ C.N)
    (hshort : (Q.searchWeight C.A : ℝ) ≤ D) (hops : ℝ) (hhops : 0 < hops) :
    (C.law R G r S D).prob (fun run =>
      ¬ C.Good R G r S D run ∨ hops ≤ (C.path R G Q S D run).hops) ≤
      (C.law R G r S D).prob (fun run => ¬ C.Good R G r S D run) +
        (14 : ℝ) ^ (r + 1) / hops := by
  let mu := C.law R G r S D
  have he : mu.prob (fun run =>
      ¬ C.Good R G r S D run ∨ hops ≤ (C.path R G Q S D run).hops) =
      mu.prob (fun run =>
        ¬ C.Good R G r S D run ∨ hops ≤ C.stoppedHops R G Q r S D run) := by
    apply mu.prob_congr
    intro run
    by_cases hg : C.Good R G r S D run <;> simp [stoppedHops, hg]
  rw [he]
  apply (mu.prob_union _ _).trans
  apply add_le_add_right
  exact (mu.markov _ (C.stoppedHops_nonneg R G Q r S D) hops hhops).trans
    (div_le_div_of_nonneg_right (C.expected_stopped_hops hsmall r Q S D hS hD hgrid hshort)
      hhops.le)

end Config

end

end StreamingReachability.Late
