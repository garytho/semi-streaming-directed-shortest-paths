module

public import StreamingReachability.Hopset.TrackedAncestry

@[expose] public section

namespace StreamingReachability.Hopset.Following.TrackedPath

open scoped Classical

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

def nextPieces (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    List (TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector) :=
  splitAll cfg (r + 1) hnum (P.advance cfg r hnum he choices hshort)

theorem nextPieces_short (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (he : r < cfg.earlyLevel) (choices : Fin ns → Reference.Choice n cfg)
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    ∀ Q ∈ P.nextPieces cfg r hnum he choices hshort,
      (Q.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg (r + 1) :=
  splitAll_short cfg (r + 1) hnum _

theorem nextPieces_subpath (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (he : r < cfg.earlyLevel) (choices : Fin ns → Reference.Choice n cfg)
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (Q : TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector)
    (hQ : Q ∈ P.nextPieces cfg r hnum he choices hshort) : Q.path.IsSubpath P.path := by
  obtain ⟨C, hC, hQ⟩ := List.mem_flatMap.mp hQ
  exact (C.split_subpath cfg (r + 1) hnum Q hQ).trans
    (P.advance_subpath cfg r hnum he choices hshort C hC)

theorem nextPieces_set_subset (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (he : r < cfg.earlyLevel) (choices : Fin ns → Reference.Choice n cfg)
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r)
    (Q : TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector)
    (hQ : Q ∈ P.nextPieces cfg r hnum he choices hshort) :
    (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector.get Q.node ⊆
      sets.get P.node := by
  obtain ⟨C, hC, hQ⟩ := List.mem_flatMap.mp hQ
  rw [C.split_node cfg (r + 1) hnum Q hQ]
  exact P.advance_set_subset cfg r hnum he choices hshort C hC

theorem nextPieces_weight (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (he : r < cfg.earlyLevel) (choices : Fin ns → Reference.Choice n cfg)
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    weight cfg.inputScale (P.nextPieces cfg r hnum he choices hshort) ≤ P.path.searchWeight cfg.inputScale :=
  (splitAll_weight cfg (r + 1) hnum _).trans (P.advance_weight cfg r hnum he choices hshort)

end

end StreamingReachability.Hopset.Following.TrackedPath
