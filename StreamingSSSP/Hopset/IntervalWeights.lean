module

public import StreamingSSSP.Hopset.IntervalPaths

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical BigOperators

noncomputable section

theorem list_sum_indices {A : Type*} (xs : List A) (w : A → ℕ) :
    (xs.map w).sum = ∑ i : Fin xs.length, w (xs.get i) := by
  have he : List.ofFn (fun i : Fin xs.length => w (xs.get i)) = xs.map w := by
    simpa only [List.map_ofFn, Function.comp_def] using congrArg (List.map w) (List.ofFn_get xs)
  rw [← he, List.sum_ofFn]

theorem list_window_sum {A : Type*} (xs : List A) (w : A → ℕ) (start count : ℕ) :
    (((xs.drop start).take count).map w).sum =
      ∑ i : Fin xs.length, if start ≤ i.val ∧ i.val < start + count then w (xs.get i) else 0 := by
  induction xs generalizing start count with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_take, List.map_drop, List.get_eq_getElem] at ih
      cases start with
      | zero =>
          cases count with
          | zero => simp
          | succ count =>
              simp [Fin.sum_univ_succ, List.get_eq_getElem]
              simpa using ih 0 count
      | succ start =>
          have hc (k : ℕ) : k + 1 < start + (1 + count) ↔ k < start + count := by omega
          simp [Fin.sum_univ_succ, List.get_eq_getElem, ih, Nat.add_assoc, hc]

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem intervalEdges_indices (Q : Late.Path R G s t) (w : Late.Path.PackedEdge R G → ℕ) (I : ℕ × ℕ)
    (hp : I.1 < I.2) :
    ((Q.intervalPath I).edges.map w).sum = ∑ i : Fin Q.edges.length,
      if I.1 ≤ i.val ∧ i.val + 1 < I.2 then w (Q.edges.get i) else 0 := by
  simp only [Late.Path.intervalPath, Late.Path.edges_take, Late.Path.edges_suffix]
  rw [list_window_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : I.1 ≤ i.val ∧ i.val < I.1 + (I.2 - 1 - I.1) ↔
      I.1 ≤ i.val ∧ i.val + 1 < I.2 := by omega
  simp only [he]

theorem intervalEdges_sum_le {L : Type*} (Q : Late.Path R G s t)
    (C : VertexCover Q.vertices.length L) (w : Late.Path.PackedEdge R G → ℕ) :
    (∑ label ∈ C.labels, ((Q.intervalPath (C.interval label)).edges.map w).sum) ≤
      (Q.edges.map w).sum := by
  calc
    _ = ∑ label ∈ C.labels, ∑ i : Fin Q.edges.length,
        if (C.interval label).1 ≤ i.val ∧ i.val + 1 < (C.interval label).2
          then w (Q.edges.get i) else 0 := by
      apply Finset.sum_congr rfl
      intro label hl
      exact intervalEdges_indices Q w (C.interval label) (C.bounds label hl).1
    _ ≤ ∑ i : Fin Q.edges.length, w (Q.edges.get i) := C.internal_weights_le _
    _ = _ := (list_sum_indices Q.edges w).symm

theorem intervalSearch_indices (Q : Late.Path R G s t) (A : ℕ) (I : ℕ × ℕ)
    (hp : I.1 < I.2) :
    Q.intervalSearch A I = ∑ i : Fin Q.edges.length,
      if I.1 ≤ i.val ∧ i.val + 1 < I.2 then (Q.edges.get i).2.2.searchWeight A else 0 := by
  simpa only [Late.Path.intervalSearch, Late.Path.searchWeight_edges] using
    intervalEdges_indices Q (fun e => e.2.2.searchWeight A) I hp

theorem intervalSearch_sum_le {L : Type*} (Q : Late.Path R G s t)
    (C : VertexCover Q.vertices.length L) (A : ℕ) :
    (∑ label ∈ C.labels, Q.intervalSearch A (C.interval label)) ≤ Q.searchWeight A := by
  have he (label : L) (hl : label ∈ C.labels) :=
    intervalSearch_indices Q A (C.interval label) (C.bounds label hl).1
  calc
    _ = ∑ label ∈ C.labels, ∑ i : Fin Q.edges.length,
        if (C.interval label).1 ≤ i.val ∧ i.val + 1 < (C.interval label).2
          then (Q.edges.get i).2.2.searchWeight A else 0 := by
      apply Finset.sum_congr rfl
      intro label hl
      exact he label hl
    _ ≤ ∑ i : Fin Q.edges.length, (Q.edges.get i).2.2.searchWeight A :=
      C.internal_weights_le _
    _ = _ := by
      rw [Late.Path.searchWeight_edges, list_sum_indices]

end

end StreamingSSSP.Hopset
