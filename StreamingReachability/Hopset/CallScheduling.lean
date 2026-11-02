module

public import StreamingReachability.Hopset.TrackedPaths
public import StreamingReachability.Hopset.EarlyPlanRelated

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem queue_member_index {T : Type*} (queue : List T) (value : T) (h : value ∈ queue) :
    ∃ i : Fin queue.toArray.size, queue.toArray.toVector.get i = value := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  refine ⟨⟨j.val, by simpa using j.isLt⟩, ?_⟩
  simpa [Vector.get_eq_getElem] using hj

theorem early_child_mem (cfg : Config) (r : ℕ) (he : r < cfg.earlyLevel)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (sets : Vector (Finset (Fin n)) ns) (choices : Fin ns → Reference.Choice n cfg)
    (i : Fin ns) (T : Finset (Fin n))
    (hT : T ∈
      Geometry.fringes (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
        (sets.get i) (choices i).pivots
        (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (choices i).owners)
        (Reference.distanceScale cfg r) ++
      Geometry.core (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale)
        (sets.get i) (choices i).pivots
        (Reference.radii cfg r (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) (choices i).owners)) :
    T ∈ Batched.geometricChildren cfg r stored input sets choices := by
  simp only [Batched.geometricChildren, he, ↓reduceIte]
  rcases List.mem_append.mp hT with hT | hT
  · exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨i, by simp, hT⟩))
  · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨i, by simp, hT⟩))

namespace TrackedPath

variable {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}

def schedule (queue : List (Finset (Fin n))) (X : Finset (Fin n)) (hX : X ∈ queue)
    {A : ℕ} {D : ℝ} (C : Late.ChildPiece stored (StoredEdges.graphOfEdges input) X A D) :
    TrackedPath stored input queue.toArray.toVector :=
  let i := Classical.choose (queue_member_index queue X hX)
  { node := i
    source := C.source
    target := C.target
    path := C.path
    inside := by
      rw [Classical.choose_spec (queue_member_index queue X hX)]
      exact C.inside }

theorem schedule_set (queue : List (Finset (Fin n))) (X : Finset (Fin n)) (hX : X ∈ queue)
    {A : ℕ} {D : ℝ} (C : Late.ChildPiece stored (StoredEdges.graphOfEdges input) X A D) :
    queue.toArray.toVector.get (schedule queue X hX C).node = X :=
  Classical.choose_spec (queue_member_index queue X hX)

theorem schedule_related (cfg : Config) (r : ℕ) (known : Fin n → Option (Fin r))
    (queue : List (Finset (Fin n))) (X : Finset (Fin n)) (hX : X ∈ queue)
    {A : ℕ} {D : ℝ} (C : Late.ChildPiece stored (StoredEdges.graphOfEdges input) X A D) :
    Following.related cfg r known [schedule queue X hX C] =
      (relatedVertices (Backend.roundedRestricted stored input X cfg.inputScale) C.path.vertices
        (RankPrefix.eligible r known X)
        (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card := by
  simp only [Following.related, List.map_singleton, List.sum_singleton, schedule_set]
  rfl

end TrackedPath

end

end StreamingReachability.Hopset.Following
