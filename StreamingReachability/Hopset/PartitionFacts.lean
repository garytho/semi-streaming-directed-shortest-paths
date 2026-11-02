module

public import StreamingReachability.Hopset.IntervalPaths

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)}
    {s t : Fin n}

namespace Path

theorem vertices_append_cons {u v : Fin n} (Pre : Path R G s u)
    (e : Edge R G u v) (Tail : Path R G v t) :
    (Pre.append (.cons e Tail)).vertices = Pre.vertices ++ Tail.vertices := by
  induction Pre with
  | nil => rfl
  | cons f Pre ih => exact congrArg (List.cons _) (ih e)

theorem interval_vertices_infix (Q : Path R G s t) (I : ℕ × ℕ)
    (hp : I.1 < I.2) (hb : I.2 ≤ Q.vertices.length) :
    (Q.intervalPath I).vertices.IsInfix Q.vertices := by
  have hlo : I.1 ≤ Q.length := by have h := Q.length_vertices; omega
  rw [intervalPath, vertices_take, vertices_suffix Q I.1 hlo]
  refine ⟨Q.vertices.take I.1, (Q.vertices.drop I.1).drop (I.2 - 1 - I.1 + 1), ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

end Path

namespace Partition

variable {X : Finset (Fin n)} {A : ℕ} {d : ℝ} {Q : Path R G s t}

theorem firstWeight_le (B : Partition R G X A d Q) : B.firstWeight ≤ Q.searchWeight A := by
  cases B with
  | one => exact le_rfl
  | cut Pre e Tail hinside hshort rest =>
      simp only [firstWeight, Path.searchWeight_append, Path.searchWeight]
      omega

theorem type2_zero_of_short (B : Partition R G X A d Q) (hgreedy : B.Greedy)
    (hshort : (Q.searchWeight A : ℝ) ≤ d) : B.type2 = 0 := by
  induction B with
  | one => rfl
  | cut Pre e Tail hinside hpre rest ih =>
      have htail : (Tail.searchWeight A : ℝ) ≤ d := by
        simp only [Path.searchWeight_append, Path.searchWeight, Nat.cast_add] at hshort
        have h₁ : (0 : ℝ) ≤ Pre.searchWeight A := Nat.cast_nonneg _
        have h₂ : (0 : ℝ) ≤ e.searchWeight A := Nat.cast_nonneg _
        linarith
      have hnot : ¬ e.Inside X := by
        intro he
        have hc := hgreedy.2.resolve_left (not_not.mpr he)
        have hr : (rest.firstWeight : ℝ) ≤ Tail.searchWeight A := by exact_mod_cast rest.firstWeight_le
        simp only [Path.searchWeight_append, Path.searchWeight, Nat.cast_add] at hshort
        have hp : (0 : ℝ) ≤ Pre.searchWeight A := Nat.cast_nonneg _
        linarith
      simp only [type2, hnot, ↓reduceIte, zero_add]
      exact ih hgreedy.1 htail

theorem piece_vertices_infix (B : Partition R G X A d Q) :
    ∀ C ∈ B.pieces, C.path.vertices.IsInfix Q.vertices := by
  induction B with
  | one Q hinside hshort =>
      intro C hC
      have he := List.mem_singleton.mp hC
      subst C
      exact ⟨[], [], by simp⟩
  | cut Pre e Tail hinside hshort rest ih =>
      intro C hC
      rcases List.mem_cons.mp hC with he | hC
      · subst C
        rw [Path.vertices_append_cons]
        exact ⟨[], Tail.vertices, by simp⟩
      · have ht := ih C hC
        apply ht.trans
        rw [Path.vertices_append_cons]
        exact ⟨Pre.vertices, [], by simp⟩

end Partition

end

end StreamingReachability.Late
