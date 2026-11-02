module

public import StreamingSSSP.Hopset.InputScaling

@[expose] public section

namespace StreamingSSSP.Approx

variable {n : ℕ}

structure Bounds where
  minimum : Option ℕ
  maximum : ℕ

def Bounds.push (bounds : Bounds) (edge : StoredEdges.Edge n) : Bounds :=
  ⟨some (match bounds.minimum with | none => edge.weight | some w => min w edge.weight),
    max bounds.maximum edge.weight⟩

def Bounds.minWeight (bounds : Bounds) : ℕ := bounds.minimum.getD 1

def initialBounds : Bounds := ⟨none, 0⟩

def scan (input : List (StoredEdges.Edge n)) : Bounds := input.foldl Bounds.push initialBounds

def scanViewed {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E) : Bounds :=
  input.foldl (fun bounds raw => match view raw with | none => bounds | some edge => bounds.push edge) initialBounds

structure Bounds.Valid (bounds : Bounds) (seen : List (StoredEdges.Edge n)) : Prop where
  positive : ∀ w, bounds.minimum = some w → 0 < w
  lower : ∀ e ∈ seen, ∃ w, bounds.minimum = some w ∧ w ≤ e.weight
  upper : ∀ e ∈ seen, e.weight ≤ bounds.maximum

theorem Bounds.Valid.push {bounds : Bounds} {seen : List (StoredEdges.Edge n)}
    (h : bounds.Valid seen) (edge : StoredEdges.Edge n) (hp : 0 < edge.weight) :
    (bounds.push edge).Valid (seen ++ [edge]) := by
  have hupper : ∀ e ∈ seen ++ [edge], e.weight ≤ max bounds.maximum edge.weight := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact (h.upper e he).trans (Nat.le_max_left _ _)
    · have heq := List.mem_singleton.mp he
      subst e
      exact Nat.le_max_right _ _
  cases hm : bounds.minimum with
  | none =>
      refine ⟨?_, ?_, hupper⟩
      · intro w hw
        have heq : edge.weight = w := by simpa only [Bounds.push, hm, Option.some.injEq] using hw
        omega
      · intro e he
        rcases List.mem_append.mp he with he | he
        · obtain ⟨w, hw, _⟩ := h.lower e he
          rw [hm] at hw
          cases hw
        · have heq := List.mem_singleton.mp he
          subst e
          exact ⟨edge.weight, by simp only [Bounds.push, hm], le_rfl⟩
  | some old =>
      have hold := h.positive old hm
      refine ⟨?_, ?_, hupper⟩
      · intro w hw
        have heq : min old edge.weight = w := by simpa only [Bounds.push, hm, Option.some.injEq] using hw
        rw [← heq]
        exact lt_min hold hp
      · intro e he
        refine ⟨min old edge.weight, by simp only [Bounds.push, hm], ?_⟩
        rcases List.mem_append.mp he with he | he
        · obtain ⟨w, hw, hwe⟩ := h.lower e he
          have heq : old = w := by simpa only [hm, Option.some.injEq] using hw
          exact (Nat.min_le_left _ _).trans (by rw [heq]; exact hwe)
        · have heq := List.mem_singleton.mp he
          subst e
          exact Nat.min_le_right _ _

theorem fold_bounds_valid (input : List (StoredEdges.Edge n)) (bounds : Bounds)
    (seen : List (StoredEdges.Edge n)) (h : bounds.Valid seen)
    (hp : ∀ e ∈ input, 0 < e.weight) : (input.foldl Bounds.push bounds).Valid (seen ++ input) := by
  induction input generalizing bounds seen with
  | nil => simpa only [List.foldl_nil, List.append_nil] using h
  | cons edge input ih =>
      have hn := h.push edge (hp edge List.mem_cons_self)
      have ht := ih (bounds.push edge) (seen ++ [edge]) hn (fun e he => hp e (List.mem_cons_of_mem _ he))
      simpa only [List.foldl_cons, List.append_assoc, List.singleton_append] using ht

theorem scan_valid (input : List (StoredEdges.Edge n)) (hp : ∀ e ∈ input, 0 < e.weight) :
    (scan input).Valid input := by
  have hinit : initialBounds.Valid ([] : List (StoredEdges.Edge n)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      cases hw
    · intro e he
      cases he
    · intro e he
      cases he
  exact fold_bounds_valid input initialBounds [] hinit hp

theorem Bounds.Valid.minWeight_pos {bounds : Bounds} {seen : List (StoredEdges.Edge n)}
    (h : bounds.Valid seen) : 0 < bounds.minWeight := by
  cases hm : bounds.minimum with
  | none => simpa only [Bounds.minWeight, hm, Option.getD_none] using (show (0 : ℕ) < 1 by decide)
  | some w => simpa only [Bounds.minWeight, hm, Option.getD_some] using h.positive w hm

theorem Bounds.Valid.minWeight_le {bounds : Bounds} {seen : List (StoredEdges.Edge n)}
    (h : bounds.Valid seen) (edge : StoredEdges.Edge n) (he : edge ∈ seen) : bounds.minWeight ≤ edge.weight := by
  obtain ⟨w, hw, hwe⟩ := h.lower edge he
  simpa only [Bounds.minWeight, hw, Option.getD_some] using hwe

theorem scanViewed_eq {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E) :
    scanViewed view input = scan (input.filterMap view) := by
  have h (bounds : Bounds) :
      input.foldl (fun bounds raw => match view raw with | none => bounds | some edge => bounds.push edge) bounds =
        (input.filterMap view).foldl Bounds.push bounds := by
    induction input generalizing bounds with
    | nil => rfl
    | cons raw input ih =>
        cases hv : view raw <;> simp only [List.foldl_cons, List.filterMap_cons, hv, ih]
  exact h initialBounds

end StreamingSSSP.Approx
