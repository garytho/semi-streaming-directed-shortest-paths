module

public import StreamingSSSP.Hopset.IntervalPaths

@[expose] public section

namespace StreamingSSSP.Late.Path

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem micro_le_search (Q : Path R G s t) (A : ℕ) (hA : 0 < A) : Q.micro ≤ A * Q.searchWeight A := by
  induction Q with
  | nil => simp [micro, searchWeight]
  | cons e Q ih =>
      have he : e.micro ≤ A * e.searchWeight A := (Core.ceilNat_le_iff hA).mp le_rfl
      simpa only [micro, searchWeight, Nat.mul_add] using Nat.add_le_add he ih

theorem searchWeight_zero_of_length_zero (Q : Path R G s t) (A : ℕ) (h : Q.length = 0) :
    Q.searchWeight A = 0 := by
  cases Q with
  | nil => rfl
  | cons e Q => simp [length] at h

theorem searchWeight_take_full (Q : Path R G s t) (A : ℕ) : (Q.take Q.length).searchWeight A = Q.searchWeight A := by
  have hs : (Q.suffix Q.length).length = 0 := by simp [length_suffix]
  have hz := (Q.suffix Q.length).searchWeight_zero_of_length_zero A hs
  have he := Q.weight_split A Q.length
  omega

theorem searchWeight_suffix_suffix (Q : Path R G s t) (A i j : ℕ) :
    ((Q.suffix i).suffix j).searchWeight A = (Q.suffix (i + j)).searchWeight A := by
  simp only [searchWeight_edges, edges_suffix, List.drop_drop, Nat.add_comm]

theorem searchWeight_suffix_zero (Q : Path R G s t) (A : ℕ) : (Q.suffix 0).searchWeight A = Q.searchWeight A := by
  simp only [searchWeight_edges, edges_suffix, List.drop_zero]

theorem intervalSearch_final (Q : Path R G s t) (A : ℕ) (I : ℕ × ℕ)
    (hp : I.1 < I.2) (hf : I.2 = Q.vertices.length) :
    Q.intervalSearch A I = (Q.suffix I.1).searchWeight A := by
  have hc : I.2 - 1 - I.1 = (Q.suffix I.1).length := by
    have hlen := Q.length_vertices
    have hs := Q.length_suffix I.1
    omega
  unfold intervalSearch intervalPath
  rw [hc, searchWeight_take_full]

theorem intervalSearch_split (Q : Path R G s t) (A : ℕ) (I : ℕ × ℕ) (hp : I.1 < I.2) :
    Q.intervalSearch A I + (Q.suffix (I.2 - 1)).searchWeight A = (Q.suffix I.1).searchWeight A := by
  have he := (Q.suffix I.1).weight_split A (I.2 - 1 - I.1)
  have hs := Q.searchWeight_suffix_suffix A I.1 (I.2 - 1 - I.1)
  have harg : I.1 + (I.2 - 1 - I.1) = I.2 - 1 := by omega
  rw [harg] at hs
  rw [hs] at he
  exact he

end

end StreamingSSSP.Late.Path
