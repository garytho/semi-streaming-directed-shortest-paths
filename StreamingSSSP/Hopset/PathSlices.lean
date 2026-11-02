module

public import StreamingSSSP.Late.Routes

@[expose] public section

namespace StreamingSSSP.Late.Path

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem get_vertices (Q : Path R G s t) (i : Fin Q.vertices.length) :
    Q.vertices.get i = Q.vertex i.val := by
  induction Q with
  | nil v =>
      have hi : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
      have he : i = ⟨0, by simp [vertices]⟩ := Fin.ext hi
      subst i
      rfl
  | cons e Q ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [vertices, vertex]
      · change Q.vertices.get j = Q.vertex j.val
        exact ih j

theorem vertices_take (Q : Path R G s t) (i : ℕ) :
    (Q.take i).vertices = Q.vertices.take (i + 1) := by
  induction Q generalizing i with
  | nil v => simp [take, vertices]
  | cons e Q ih =>
      cases i with
      | zero => simp [take, vertices]
      | succ i =>
          change _ :: (Q.take i).vertices = _ :: Q.vertices.take (i + 1)
          exact congrArg (List.cons _) (ih i)

theorem vertices_suffix (Q : Path R G s t) (i : ℕ) (hi : i ≤ Q.length) :
    (Q.suffix i).vertices = Q.vertices.drop i := by
  induction Q generalizing i with
  | nil v =>
      have he : i = 0 := by change i ≤ 0 at hi; omega
      subst i
      rfl
  | cons e Q ih =>
      cases i with
      | zero => rfl
      | succ i =>
          have h : i ≤ Q.length := by simpa only [length, Nat.add_le_add_iff_right] using hi
          change (Q.suffix i).vertices = Q.vertices.drop i
          exact ih i h

theorem length_take (Q : Path R G s t) (i : ℕ) : (Q.take i).length = min i Q.length := by
  induction Q generalizing i with
  | nil v => simp [take, length]
  | cons e Q ih =>
      cases i with
      | zero => simp [take, length]
      | succ i =>
          change (Q.take i).length + 1 = min (i + 1) (Q.length + 1)
          have h := ih i
          omega

theorem vertex_take (Q : Path R G s t) (count i : ℕ) (hi : i ≤ count) :
    (Q.take count).vertex i = Q.vertex i := by
  induction Q generalizing count i with
  | nil v => rfl
  | cons e Q ih =>
      cases count with
      | zero =>
          have he : i = 0 := by omega
          subst i
          rfl
      | succ count =>
          cases i with
          | zero => rfl
          | succ i => exact ih count i (by omega)

theorem edges_take (Q : Path R G s t) (i : ℕ) : (Q.take i).edges = Q.edges.take i := by
  induction Q generalizing i with
  | nil v => simp [take, edges]
  | cons e Q ih =>
      cases i with
      | zero => simp [take, edges]
      | succ i =>
          change _ :: (Q.take i).edges = _ :: Q.edges.take i
          exact congrArg (List.cons _) (ih i)

theorem edges_suffix (Q : Path R G s t) (i : ℕ) : (Q.suffix i).edges = Q.edges.drop i := by
  induction Q generalizing i with
  | nil v => simp [suffix, edges]
  | cons e Q ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (Q.suffix i).edges = Q.edges.drop i
          exact ih i

theorem searchWeight_edges (Q : Path R G s t) (A : ℕ) :
    Q.searchWeight A = (Q.edges.map fun e => e.2.2.searchWeight A).sum := by
  induction Q with
  | nil v => rfl
  | cons e Q ih => simp only [searchWeight, edges, List.map_cons, List.sum_cons, ih]

theorem micro_edges (Q : Path R G s t) :
    Q.micro = (Q.edges.map fun e => e.2.2.micro).sum := by
  induction Q with
  | nil v => rfl
  | cons e Q ih => simp only [micro, edges, List.map_cons, List.sum_cons, ih]

theorem micro_zero_of_length_zero (Q : Path R G s t) (h : Q.length = 0) : Q.micro = 0 := by
  cases Q with
  | nil v => rfl
  | cons e Q => simp [length] at h

theorem exists_cons_of_length_pos (Q : Path R G s t) (h : 0 < Q.length) :
    ∃ v : Fin n, ∃ e : Edge R G s v, ∃ T : Path R G v t, Q = .cons e T := by
  cases Q with
  | nil v => simp [length] at h
  | cons e Q => exact ⟨_, e, Q, rfl⟩

theorem micro_take_full (Q : Path R G s t) : (Q.take Q.length).micro = Q.micro := by
  have hs : (Q.suffix Q.length).length = 0 := by simp [length_suffix]
  have hm := (Q.suffix Q.length).micro_zero_of_length_zero hs
  have h := Q.micro_split Q.length
  omega

theorem micro_suffix_suffix (Q : Path R G s t) (i j : ℕ) :
    ((Q.suffix i).suffix j).micro = (Q.suffix (i + j)).micro := by
  simp only [micro_edges, edges_suffix, List.drop_drop, Nat.add_comm]

theorem micro_take_suffix_suffix (Q : Path R G s t) (i j count : ℕ) :
    (((Q.suffix i).suffix j).take count).micro = ((Q.suffix (i + j)).take count).micro := by
  simp only [micro_edges, edges_take, edges_suffix, List.drop_drop, Nat.add_comm]

theorem searchWeight_take_suffix_suffix (Q : Path R G s t) (A i j count : ℕ) :
    (((Q.suffix i).suffix j).take count).searchWeight A =
      ((Q.suffix (i + j)).take count).searchWeight A := by
  simp only [searchWeight_edges, edges_take, edges_suffix, List.drop_drop, Nat.add_comm]

structure Slice (Q : Path R G s t) where
  start : ℕ
  count : ℕ
  bounded : start + count ≤ Q.length

namespace Slice

variable {Q : Path R G s t}

def path (I : Slice Q) : Path R G (Q.vertex I.start) ((Q.suffix I.start).vertex I.count) :=
  (Q.suffix I.start).take I.count

theorem target (I : Slice Q) : (Q.suffix I.start).vertex I.count = Q.vertex (I.start + I.count) :=
  Q.vertex_suffix I.start I.count

theorem vertices_eq (I : Slice Q) :
    I.path.vertices = (Q.vertices.drop I.start).take (I.count + 1) := by
  rw [path, vertices_take, Q.vertices_suffix I.start (by have := I.bounded; omega)]

theorem edges_eq (I : Slice Q) : I.path.edges = (Q.edges.drop I.start).take I.count := by
  rw [path, edges_take, edges_suffix]

theorem length_eq (I : Slice Q) : I.path.length = I.count := by
  rw [path, length_take, length_suffix, Nat.min_eq_left]
  have h := I.bounded
  omega

theorem inside (I : Slice Q) {S : Finset (Fin n)} (hS : Q.Inside S) : I.path.Inside S :=
  (Q.suffix I.start).prefix_inside (Q.suffix_inside hS I.start) I.count

theorem searchWeight_le (I : Slice Q) (A : ℕ) : I.path.searchWeight A ≤ Q.searchWeight A :=
  ((Q.suffix I.start).searchWeight_take_le A I.count).trans (Q.searchWeight_suffix_le A I.start)

theorem contains_index (I : Slice Q) (j : Fin I.path.vertices.length) :
    ∃ i : Fin Q.vertices.length, I.start ≤ i.val ∧ i.val ≤ I.start + I.count ∧
      I.path.vertices.get j = Q.vertices.get i := by
  have hj : j.val ≤ I.count := by
    have hlen : I.path.vertices.length = I.count + 1 := by rw [length_vertices, I.length_eq]
    have h := j.isLt
    omega
  let i : Fin Q.vertices.length := ⟨I.start + j.val, by
    have hlen := Q.length_vertices
    have h := I.bounded
    omega⟩
  refine ⟨i, by dsimp [i]; omega, by dsimp [i]; omega, ?_⟩
  rw [get_vertices, get_vertices]
  change ((Q.suffix I.start).take I.count).vertex j.val = Q.vertex (I.start + j.val)
  rw [vertex_take (Q.suffix I.start) I.count j.val hj, Q.vertex_suffix]

end Slice

end

end StreamingSSSP.Late.Path
