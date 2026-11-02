module

public import StreamingReachability.Hopset.PathSubpaths
public import StreamingReachability.Hopset.TrackedEarly

@[expose] public section

namespace StreamingReachability.Hopset.Following.TrackedPath

open scoped Classical

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

theorem split_subpath (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P Q : TrackedPath stored input sets) (hQ : Q ∈ P.split cfg r hnum) : Q.path.IsSubpath P.path := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hQ
  exact (P.type2Plan cfg r hnum).piece_subpath C hC

theorem split_node (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P Q : TrackedPath stored input sets) (hQ : Q ∈ P.split cfg r hnum) : Q.node = P.node := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hQ
  rfl

theorem advance_subpath (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (Q : TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector)
    (hQ : Q ∈ P.advance cfg r hnum he choices hshort) : Q.path.IsSubpath P.path := by
  unfold advance at hQ
  split_ifs at hQ with hs
  · simp at hQ
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hQ
    exact (P.earlyPlan cfg r hnum hshort (choices P.node) hs).piece_subpath i

theorem advance_set_subset (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (Q : TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector)
    (hQ : Q ∈ P.advance cfg r hnum he choices hshort) :
    (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector.get Q.node ⊆ sets.get P.node := by
  unfold advance at hQ
  split_ifs at hQ with hs
  · simp at hQ
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hQ
    let B := P.earlyPlan cfg r hnum hshort (choices P.node) hs
    have hset := schedule_set (Batched.geometricChildren cfg r stored input sets choices) (B.target i.1)
      (P.earlyPlan_target_mem cfg r hnum he choices hshort hs i.1)
      (A := cfg.inputScale) (D := Reference.distanceScale cfg r) (by exact B.piece i)
    rw [hset]
    exact type1Target_subset _ _ _ _ _ _

end

end StreamingReachability.Hopset.Following.TrackedPath
