module

public import StreamingReachability.Hopset.EarlyPlanBounds

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)}
    {s t a b u v : Fin n}

namespace Path

theorem append_nil (Q : Path R G s t) : Q.append (.nil t) = Q := by
  induction Q with
  | nil => rfl
  | cons e Q ih => exact congrArg (Path.cons e) ih

theorem vertices_append_tail (P : Path R G s a) (Q : Path R G a t) :
    (P.append Q).vertices = P.vertices ++ Q.vertices.tail := by
  induction P with
  | nil => cases Q <;> rfl
  | cons e P ih =>
      simpa only [append, vertices, List.cons_append] using congrArg (List.cons _) (ih Q)

theorem vertices_append_dropLast (P : Path R G s a) (Q : Path R G a t) :
    (P.append Q).vertices = P.vertices.dropLast ++ Q.vertices := by
  induction P with
  | nil => rfl
  | cons e P ih =>
      have hn := Graph.endpoints_nonempty P.endpoints
      simp only [append, vertices, List.dropLast_cons_of_ne_nil hn, List.cons_append, ih]

def IsSubpath (C : Path R G a b) (Q : Path R G s t) : Prop :=
  ∃ Pre : Path R G s a, ∃ Post : Path R G b t, Q = Pre.append (C.append Post)

theorem IsSubpath.refl (Q : Path R G s t) : Q.IsSubpath Q :=
  ⟨.nil s, .nil t, by simp only [append_nil, append]⟩

theorem IsSubpath.trans {C : Path R G a b} {Q : Path R G s t} {D : Path R G u v}
    (hDC : D.IsSubpath C) (hCQ : C.IsSubpath Q) : D.IsSubpath Q := by
  obtain ⟨Pre₁, Post₁, hQ⟩ := hCQ
  obtain ⟨Pre₂, Post₂, hC⟩ := hDC
  refine ⟨Pre₁.append Pre₂, Post₂.append Post₁, ?_⟩
  rw [hQ, hC]
  simp only [append_assoc]

theorem IsSubpath.vertices_infix {C : Path R G a b} {Q : Path R G s t}
    (h : C.IsSubpath Q) : C.vertices.IsInfix Q.vertices := by
  obtain ⟨Pre, Post, rfl⟩ := h
  refine ⟨Pre.vertices.dropLast, Post.vertices.tail, ?_⟩
  rw [vertices_append_dropLast, vertices_append_tail]
  exact List.append_assoc _ _ _

theorem IsSubpath.searchWeight_le {C : Path R G a b} {Q : Path R G s t}
    (h : C.IsSubpath Q) (A : ℕ) : C.searchWeight A ≤ Q.searchWeight A := by
  obtain ⟨Pre, Post, hQ⟩ := h
  simp only [hQ, searchWeight_append]
  omega

theorem IsSubpath.inside {C : Path R G a b} {Q : Path R G s t}
    (h : C.IsSubpath Q) {S : Finset (Fin n)} (hS : Q.Inside S) : C.Inside S := by
  obtain ⟨Pre, Post, hQ⟩ := h
  rw [hQ] at hS
  exact ((C.inside_append Post).mp ((Pre.inside_append (C.append Post)).mp hS).2).1

theorem interval_subpath (Q : Path R G s t) (I : ℕ × ℕ) : (Q.intervalPath I).IsSubpath Q := by
  refine ⟨Q.take I.1, (Q.suffix I.1).suffix (I.2 - 1 - I.1), ?_⟩
  unfold intervalPath
  rw [(Q.suffix I.1).rejoin, Q.rejoin]

end Path

namespace Partition

theorem piece_subpath {X : Finset (Fin n)} {A : ℕ} {d : ℝ} {Q : Path R G s t}
    (B : Partition R G X A d Q) : ∀ C ∈ B.pieces, C.path.IsSubpath Q := by
  induction B with
  | one Q hinside hshort =>
      intro C hC
      have he := List.mem_singleton.mp hC
      subst C
      exact Path.IsSubpath.refl Q
  | cut Pre e Tail hinside hshort rest ih =>
      intro C hC
      rcases List.mem_cons.mp hC with he | hC
      · subst C
        exact ⟨.nil _, .cons e Tail, rfl⟩
      · obtain ⟨left, right, hTail⟩ := ih C hC
        refine ⟨Pre.append (.cons e left), right, ?_⟩
        rw [hTail]
        simp only [Path.append_assoc, Path.append]

end Partition

end

end StreamingReachability.Late

namespace StreamingReachability.Hopset.EarlyPlan

open scoped Classical

noncomputable section

theorem piece_subpath {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)}
    {s t : Fin n} {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {hS : Q.Inside S}
    {D : ℝ} {hshort : (Q.searchWeight A : ℝ) ≤ D} {P : Finset (Fin n)} {rho : Fin n → ℝ} {Rmax d : ℝ}
    (B : EarlyPlan Q A S hS D hshort P rho Rmax d) (i : B.ChildIndex) :
    (B.piece i).path.IsSubpath Q :=
  ((B.parts i.1).piece_subpath _ (List.get_mem _ i.2)).trans (Q.interval_subpath _)

end

end StreamingReachability.Hopset.EarlyPlan
