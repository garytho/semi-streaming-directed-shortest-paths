module

public import StreamingReachability.Hopset.IntervalCover

@[expose] public section

namespace StreamingReachability.Late.Path

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

def intervalPath (Q : Path R G s t) (I : ℕ × ℕ) :
    Path R G (Q.vertex I.1) ((Q.suffix I.1).vertex (I.2 - 1 - I.1)) :=
  (Q.suffix I.1).take (I.2 - 1 - I.1)

def intervalMicro (Q : Path R G s t) (I : ℕ × ℕ) : ℕ := (Q.intervalPath I).micro
def intervalSearch (Q : Path R G s t) (A : ℕ) (I : ℕ × ℕ) : ℕ := (Q.intervalPath I).searchWeight A

theorem interval_endpoints (Q : Path R G s t) (I : ℕ × ℕ) (hproper : I.1 < I.2) :
    Graph.Endpoints (Q.intervalPath I).vertices (Q.vertex I.1) (Q.vertex (I.2 - 1)) := by
  have he := (Q.intervalPath I).endpoints
  have htarget : (Q.suffix I.1).vertex (I.2 - 1 - I.1) = Q.vertex (I.2 - 1) := by
    rw [Q.vertex_suffix]
    congr 1
    omega
  exact ⟨he.1, he.2.trans (congrArg some htarget)⟩

theorem intervalMicro_final (Q : Path R G s t) (I : ℕ × ℕ)
    (hproper : I.1 < I.2) (hfinal : I.2 = Q.vertices.length) :
    Q.intervalMicro I = (Q.suffix I.1).micro := by
  have hc : I.2 - 1 - I.1 = (Q.suffix I.1).length := by
    have hlen := Q.length_vertices
    have hs := Q.length_suffix I.1
    omega
  unfold intervalMicro intervalPath
  rw [hc, micro_take_full]

theorem intervalMicro_split (Q : Path R G s t) (I : ℕ × ℕ) (hproper : I.1 < I.2) :
    Q.intervalMicro I + (Q.suffix (I.2 - 1)).micro = (Q.suffix I.1).micro := by
  have h := (Q.suffix I.1).micro_split (I.2 - 1 - I.1)
  have hs := Q.micro_suffix_suffix I.1 (I.2 - 1 - I.1)
  have hp : I.1 + (I.2 - 1 - I.1) = I.2 - 1 := by omega
  rw [hp] at hs
  rw [hs] at h
  exact h

theorem interval_vertices (Q : Path R G s t) (I : ℕ × ℕ)
    (hproper : I.1 < I.2) (hbounded : I.2 ≤ Q.vertices.length) {v : Fin n}
    (hv : v ∈ (Q.intervalPath I).vertices) :
    ∃ i : Fin Q.vertices.length, Early.Cells.Contains I i.val ∧ v = Q.vertices.get i := by
  let slice : Slice Q := ⟨I.1, I.2 - 1 - I.1, by
    have hlen := Q.length_vertices
    omega⟩
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hv
  have he := slice.contains_index j
  obtain ⟨i, hi₁, hi₂, hie⟩ := he
  refine ⟨i, ⟨hi₁, by dsimp only [slice] at hi₂; omega⟩, ?_⟩
  exact hj.symm.trans hie

theorem interval_inside (Q : Path R G s t) (I : ℕ × ℕ)
    {S : Finset (Fin n)} (hS : Q.Inside S) : (Q.intervalPath I).Inside S :=
  (Q.suffix I.1).prefix_inside (Q.suffix_inside hS I.1) (I.2 - 1 - I.1)

theorem micro_suffix_zero (Q : Path R G s t) : (Q.suffix 0).micro = Q.micro := by
  simp only [micro_edges, edges_suffix, List.drop_zero]

end

end StreamingReachability.Late.Path
