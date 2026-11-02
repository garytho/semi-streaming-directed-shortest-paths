module

public import StreamingReachability.Probability.Family

@[expose] public section

namespace StreamingReachability.Branching

open scoped Classical BigOperators

variable {S O : Type*}

structure Step (S O : Type*) where
  value : O
  children : List S

theorem sum_flatMap {A B : Type*} (xs : List A) (f : A → List B) (g : B → ℝ) :
    ((xs.flatMap f).map g).sum = (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons, ih]

theorem sum_get {A : Type*} (xs : List A) (f : A → ℝ) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i.val] := by
  have h : List.ofFn (fun i : Fin xs.length => f xs[i.val]) = xs.map f := by
    have hget : List.ofFn (fun i : Fin xs.length => xs[i.val]) = xs := List.ofFn_getElem
    have hmap := congrArg (List.map f) hget
    rw [List.map_ofFn] at hmap
    simpa only [Function.comp_def] using hmap
  rw [← h, List.sum_ofFn]

theorem expect_list_sum {A I : Type*} (mu : Law A) (xs : List I) (f : I → A → ℝ) :
    mu.expect (fun a => (xs.map fun i => f i a).sum) =
      (xs.map fun i => mu.expect (f i)).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp only [List.map_cons, List.sum_cons, Law.expect_add, ih]

theorem sum_scale {I : Type*} (xs : List I) (f : I → ℝ) (c : ℝ) :
    c * (xs.map f).sum = (xs.map fun i => c * f i).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem sum_list_finset {I T : Type*} (xs : List T) (indices : Finset I) (f : I → T → ℝ) :
    (xs.map fun x => ∑ i ∈ indices, f i x).sum =
      ∑ i ∈ indices, (xs.map (f i)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

noncomputable def potential (kernel : ℕ → S → Law (Step S O))
    (charge : ℕ → S → Step S O → ℕ) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | fuel + 1, r, state =>
      (kernel r state).expect fun step =>
        (charge r state step : ℝ) +
          (step.children.map (potential kernel charge fuel (r + 1))).sum

noncomputable def runCost (kernel : ℕ → S → Law (Step S O))
    (charge : ℕ → S → Step S O → ℕ) : ℕ → ℕ → List S → Law ℕ
  | 0, _, _ => Law.pure 0
  | fuel + 1, r, queue =>
      (Law.family queue.length (fun i => kernel r queue[i.val])).bind fun steps =>
        let children := (List.ofFn steps).flatMap Step.children
        let spent := ((List.finRange queue.length).map fun i =>
          charge r queue[i.val] (steps i)).sum
        (runCost kernel charge fuel (r + 1) children).map fun future => spent + future

theorem potential_nonneg (kernel : ℕ → S → Law (Step S O))
    (charge : ℕ → S → Step S O → ℕ) (fuel r : ℕ) (state : S) :
    0 ≤ potential kernel charge fuel r state := by
  induction fuel generalizing r state with
  | zero => exact le_rfl
  | succ fuel ih =>
      apply Law.expect_nonneg
      intro step
      apply add_nonneg (Nat.cast_nonneg _)
      apply List.sum_nonneg
      intro a ha
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp ha
      exact ih (r + 1) s

theorem potential_sum {I : Type*} (kernel : ℕ → S → Law (Step S O))
    (indices : Finset I) (charge : I → ℕ → S → Step S O → ℕ)
    (fuel r : ℕ) (state : S) :
    potential kernel (fun r S step => ∑ i ∈ indices, charge i r S step) fuel r state =
      ∑ i ∈ indices, potential kernel (charge i) fuel r state := by
  induction fuel generalizing r state with
  | zero => simp [potential]
  | succ fuel ih =>
      simp only [potential]
      have he :
          (fun step : Step S O =>
            ((∑ i ∈ indices, charge i r state step : ℕ) : ℝ) +
              (step.children.map
                (potential kernel (fun r S step => ∑ i ∈ indices, charge i r S step) fuel (r + 1))).sum) =
            fun step => ∑ i ∈ indices,
              ((charge i r state step : ℝ) +
                (step.children.map (potential kernel (charge i) fuel (r + 1))).sum) := by
        funext step
        simp only [Nat.cast_sum]
        have hfun :
            potential kernel (fun r S step => ∑ i ∈ indices, charge i r S step) fuel (r + 1) =
              fun state => ∑ i ∈ indices, potential kernel (charge i) fuel (r + 1) state :=
          funext (fun state => ih (r + 1) state)
        rw [hfun]
        rw [sum_list_finset, Finset.sum_add_distrib]
      rw [he, Law.expect_finset_sum]

theorem expected_breadth_first_cost (kernel : ℕ → S → Law (Step S O))
    (charge : ℕ → S → Step S O → ℕ) (fuel r : ℕ) (queue : List S) :
    (runCost kernel charge fuel r queue).expect (fun count => (count : ℝ)) =
      (queue.map (potential kernel charge fuel r)).sum := by
  induction fuel generalizing r queue with
  | zero => simp [runCost, potential]
  | succ fuel ih =>
      rw [runCost, Law.expect_bind]
      simp_rw [Law.expect_map]
      have he (steps : Fin queue.length → Step S O) :
          (runCost kernel charge fuel (r + 1) ((List.ofFn steps).flatMap Step.children)).expect
              (fun future =>
                ((((List.finRange queue.length).map fun i =>
                  charge r queue[i.val] (steps i)).sum + future : ℕ) : ℝ)) =
            ∑ i : Fin queue.length,
              ((charge r queue[i.val] (steps i) : ℝ) +
                ((steps i).children.map (potential kernel charge fuel (r + 1))).sum) := by
        simp only [Nat.cast_add, Law.expect_add, Law.expect_const]
        rw [ih, sum_flatMap]
        simp only [List.map_ofFn, List.sum_ofFn]
        rw [Nat.cast_list_sum, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
        rw [Finset.sum_add_distrib]
        simp only [Function.comp_def]
      simp_rw [he]
      rw [Law.expect_finset_sum, sum_get]
      apply Finset.sum_congr rfl
      intro i _
      exact Law.family_marginal queue.length (fun j => kernel r queue[j.val]) i
        (fun step => (charge r queue[i.val] step : ℝ) +
          (step.children.map (potential kernel charge fuel (r + 1))).sum)

end StreamingReachability.Branching
