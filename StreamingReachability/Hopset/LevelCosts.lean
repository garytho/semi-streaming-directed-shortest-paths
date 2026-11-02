module

public import StreamingReachability.Hopset.NodeViews

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ} {M : Type*} [AddCommMonoid M]

theorem sum_by_index {A : Type*} (L : List A) (index : A → Fin ns) (f : A → M) :
    (L.map f).sum = ∑ i : Fin ns, ((L.filter fun a => decide (index a = i)).map f).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have he (i : Fin ns) :
          (((a :: L).filter fun b => decide (index b = i)).map f).sum =
            (if index a = i then f a else 0) +
              ((L.filter fun b => decide (index b = i)).map f).sum := by
        by_cases hi : index a = i <;> simp [hi]
      simp_rw [he]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ↓reduceIte, List.map_cons, List.sum_cons]
      exact congrArg (fun x => f a + x) ih

theorem sum_finRange (f : Fin ns → M) :
    ((List.finRange ns).map f).sum = ∑ i : Fin ns, f i := by
  have he : (List.finRange ns).toFinset = Finset.univ := by ext i; simp
  simpa only [he] using (List.sum_toFinset f (List.nodup_finRange ns)).symm

theorem sum_flatMap_map {I A : Type*} (L : List I) (g : I → List A) (f : A → M) :
    ((L.flatMap g).map f).sum = (L.map fun i => ((g i).map f).sum).sum := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem earlyCore_cost (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (P : Fin ns → Finset (Fin n)) (G : Fin ns → Graph (Fin n)) (rho : Fin ns → Fin n → ℝ)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i) (G i) (rho i))
    (f : Finset (Fin n) → M) :
    ((earlyCore cfg r sets pivots reply).map f).sum =
      ∑ i : Fin ns, ((Geometry.core (G i) (sets.get i) (P i) (rho i)).map f).sum := by
  have he : earlyCore cfg r sets pivots reply =
      (List.finRange ns).flatMap fun i => Geometry.core (G i) (sets.get i) (P i) (rho i) := by
    unfold earlyCore
    apply List.flatMap_congr
    intro i _
    exact (hview i).core
  rw [he, sum_flatMap_map, sum_finRange]

theorem earlyFringes_cost (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (P : Fin ns → Finset (Fin n)) (G : Fin ns → Graph (Fin n)) (rho : Fin ns → Fin n → ℝ)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i) (G i) (rho i))
    (f : Finset (Fin n) → M) :
    ((earlyFringes cfg r sets pivots reply).map f).sum =
      ∑ i : Fin ns,
        ((Geometry.fringes (G i) (sets.get i) (P i) (rho i) (Reference.distanceScale cfg r)).map f).sum := by
  unfold earlyFringes
  rw [List.map_map, sum_by_index pivots Pivot.setId]
  apply Finset.sum_congr rfl
  intro i _
  have he :
      ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
        fringe cfg r p.eta p.shift (sets.get p.setId) reply p.forward p.backward) =
        Geometry.fringes (G i) (sets.get i) (P i) (rho i) (Reference.distanceScale cfg r) := by
    calc
      _ = ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
          fringe cfg r p.eta p.shift (sets.get i) reply p.forward p.backward) := by
        apply List.map_congr_left
        intro p hp
        have hi := of_decide_eq_true (List.mem_filter.mp hp).2
        rw [hi]
      _ = _ := (hview i).fringes
  simpa only [List.map_map, Function.comp_def] using congrArg (fun L => (L.map f).sum) he

theorem lateBlocks_cost (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (P : Fin ns → Finset (Fin n)) (G : Fin ns → Graph (Fin n)) (rho : Fin ns → Fin n → ℝ)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i) (G i) (rho i))
    (f : Finset (Fin n) → M) :
    ((lateBlocks cfg r sets pivots reply).map f).sum =
      ∑ i : Fin ns, (((members (P i)).map fun v =>
        sets.get i ∩ Early.bothBall (G i) v (rho i v + Reference.distanceScale cfg r)).map f).sum := by
  unfold lateBlocks
  rw [List.map_map, sum_by_index pivots Pivot.setId]
  apply Finset.sum_congr rfl
  intro i _
  have he :
      ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
        bothBall cfg r (p.eta + 1) p.shift (sets.get p.setId) reply p.forward p.backward) =
        (members (P i)).map fun v =>
          sets.get i ∩ Early.bothBall (G i) v (rho i v + Reference.distanceScale cfg r) := by
    calc
      _ = ((pivots.filter fun p => decide (p.setId = i)).map fun p =>
          bothBall cfg r (p.eta + 1) p.shift (sets.get i) reply p.forward p.backward) := by
        apply List.map_congr_left
        intro p hp
        have hi := of_decide_eq_true (List.mem_filter.mp hp).2
        rw [hi]
      _ = _ := (hview i).blocks
  simpa only [List.map_map, Function.comp_def] using congrArg (fun L => (L.map f).sum) he

theorem lateCore_cost (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (P : Fin ns → Finset (Fin n)) (G : Fin ns → Graph (Fin n)) (rho : Fin ns → Fin n → ℝ)
    (hview : ∀ i, NodeView cfg r pivots reply i (sets.get i) (P i) (G i) (rho i))
    (f : Finset (Fin n) → M) :
    ((lateCore cfg r sets pivots reply).map f).sum =
      ∑ i : Fin ns, f (Reference.lateChild (G i) (sets.get i) (P i) (rho i)) := by
  have he : lateCore cfg r sets pivots reply =
      (List.finRange ns).map fun i => Reference.lateChild (G i) (sets.get i) (P i) (rho i) := by
    unfold lateCore
    apply List.map_congr_left
    intro i _
    exact (hview i).lateCore
  rw [he, List.map_map]
  exact sum_finRange _

end

end StreamingReachability.Hopset
