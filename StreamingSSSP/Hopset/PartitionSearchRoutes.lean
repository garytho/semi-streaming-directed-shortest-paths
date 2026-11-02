module

public import StreamingSSSP.Hopset.SearchPathAlgebra

@[expose] public section

namespace StreamingSSSP.Late.Partition

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G F : Graph (Fin n)}
    {X : Finset (Fin n)} {A : ℕ} {d : ℝ} {s t : Fin n}

def assembleSearch (hA : 0 < A) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (debt : ChildPiece R G X A d → ℕ)
    (child : (P : ChildPiece R G X A d) →
      Route F P.source P.target (A * (P.path.searchWeight A + debt P))) :
    {s t : Fin n} → {Q : Path R G s t} → (B : Partition R G X A d Q) →
      Route F s t (A * (Q.searchWeight A + (B.pieces.map debt).sum))
  | _, _, _, .one Q hX hd => by
      let T := child ⟨_, _, Q, hX, hd⟩
      exact ⟨T.vertices, T.endpoints, by
        simpa only [pieces, List.map_singleton, List.sum_singleton] using T.cost_le⟩
  | _, _, _, .cut Pre e Tail hX hd rest => by
      let left := child ⟨_, _, Pre, hX, hd⟩
      have he : e.micro ≤ A * e.searchWeight A := (Core.ceilNat_le_iff hA).mp le_rfl
      let boundary := Route.edge _ _ (A * e.searchWeight A)
        (((hF _ _).trans_eq e.weight).trans (WithTop.coe_le_coe.mpr he))
      let tail := assembleSearch hA hF debt child rest
      exact (left.append (boundary.append tail)).weaken (by
        simp only [Path.searchWeight_append, Path.searchWeight, pieces, List.map_cons, List.sum_cons]
        apply le_of_eq
        ring)

theorem assembleSearch_hops (hA : 0 < A) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (debt : ChildPiece R G X A d → ℕ)
    (child : (P : ChildPiece R G X A d) →
      Route F P.source P.target (A * (P.path.searchWeight A + debt P)))
    {Q : Path R G s t} (B : Partition R G X A d Q) :
    (B.assembleSearch hA hF debt child).hops ≤ B.boundaries +
      (B.pieces.map fun C => (child C).hops).sum := by
  induction B with
  | one Q hinside hshort =>
      simp only [assembleSearch, Route.hops, pieces, boundaries, List.map_singleton, List.sum_singleton, Nat.zero_add, le_refl]
  | cut Pre e Tail hinside hshort rest ih =>
      have he : e.micro ≤ A * e.searchWeight A := (Core.ceilNat_le_iff hA).mp le_rfl
      let boundary := Route.edge _ _ (A * e.searchWeight A)
        (((hF _ _).trans_eq e.weight).trans (WithTop.coe_le_coe.mpr he))
      have hh := (child ⟨_, _, Pre, hinside, hshort⟩).hops_append
        (boundary.append (rest.assembleSearch hA hF debt child))
      have ht := boundary.hops_append (rest.assembleSearch hA hF debt child)
      have hb : boundary.hops = 1 := Route.hops_edge _ _ _ _
      change ((child ⟨_, _, Pre, hinside, hshort⟩).append
        (boundary.append (rest.assembleSearch hA hF debt child))).hops ≤
          rest.boundaries + 1 + ((child ⟨_, _, Pre, hinside, hshort⟩).hops +
            (rest.pieces.map fun C => (child C).hops).sum)
      omega

end

end StreamingSSSP.Late.Partition
