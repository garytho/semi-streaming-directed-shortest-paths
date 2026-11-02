module

public import StreamingReachability.Early.MarkedFamily
public import StreamingReachability.Probability.Independent

@[expose] public section

namespace StreamingReachability.Early.Sampling

open scoped Classical

noncomputable section

theorem marked_pivots_expect {V O : Type*} (owner : V → Law O)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (vertices : List V) (f : Finset V → ℝ) :
    (marked owner p hp hp1 vertices).expect (fun xs => f (pivots xs)) =
      (Law.subset (fun _ : V => p) (fun _ => hp) (fun _ => hp1) vertices).expect f := by
  induction vertices generalizing f with
  | nil => simp [marked, pivots, Law.subset]
  | cons v vertices ih =>
      simp only [marked, Law.subset, Law.expect_bind]
      apply congrArg (Law.coin p hp hp1).expect
      funext coin
      cases coin with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih f
      | true =>
          simp only [↓reduceIte, Law.expect_bind, Law.expect_map]
          have he (o : O) :
              (marked owner p hp hp1 vertices).expect (fun xs => f (pivots ((v, o) :: xs))) =
                (Law.subset (fun _ : V => p) (fun _ => hp) (fun _ => hp1) vertices).expect (fun S => f (insert v S)) := by
            simpa only [pivots, List.map_cons, List.toFinset_cons] using ih (fun S => f (insert v S))
          simp_rw [he, Law.expect_const]

end

end StreamingReachability.Early.Sampling

namespace StreamingReachability.Law

open scoped Classical

noncomputable section

theorem family_subset {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (vertices : List (Fin n)) (hn : vertices.Nodup) (f : Finset (Fin n) → ℝ) :
    (family n (fun _ => coin p hp hp1)).expect (fun coins => f (vertices.toFinset.filter (fun v => coins v = true))) =
      (subset (fun _ : Fin n => p) (fun _ => hp) (fun _ => hp1) vertices).expect f := by
  have h := Early.Sampling.family_ownedSubset (fun _ : Fin n => coin p hp hp1)
    (fun _ => pure ()) p hp hp1 vertices hn (fun _ _ => rfl) (fun xs => f (Early.Sampling.pivots xs))
  simp only [Early.Sampling.ownedSubset_pivots, expect_const] at h
  have hset : @List.toFinset (Fin n) (Classical.decEq (Fin n)) vertices = vertices.toFinset := by
    ext v
    simp
  rw [hset] at h
  exact h.trans (Early.Sampling.marked_pivots_expect (fun _ : Fin n => pure ()) p hp hp1 vertices f)

theorem subset_one_expect {V : Type*} (vertices : List V) (f : Finset V → ℝ) :
    (subset (fun _ : V => (1 : ℝ)) (fun _ => by norm_num) (fun _ => le_rfl) vertices).expect f = f vertices.toFinset := by
  induction vertices generalizing f with
  | nil => simp [subset]
  | cons v vertices ih =>
      simp only [subset, expect_bind, expect_coin, sub_self, zero_mul, one_mul, zero_add]
      simp only [↓reduceIte, expect_map]
      simpa only [List.toFinset_cons] using ih (fun S => f (insert v S))

end

end StreamingReachability.Law
