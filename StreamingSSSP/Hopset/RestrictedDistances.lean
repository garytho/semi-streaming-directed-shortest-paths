module

public import StreamingSSSP.Hopset.Representation
public import StreamingSSSP.Early.Geometry

@[expose] public section

namespace StreamingSSSP.Hopset.Geometry

open scoped Classical

noncomputable section

theorem restrict_distance_le_of_induced {V : Type*} [Fintype V]
    (H F : Graph V) (X : Finset V) (C : Set V) [Fintype C]
    (hXC : ∀ v ∈ X, v ∈ C) (hF : Implicit.induced F X = F)
    (hmono : ∀ u v, H u v ≤ F u v)
    (u v : V) (hu : u ∈ X) (hv : v ∈ X) :
    (H.restrict C).dist ⟨u, hXC u hu⟩ ⟨v, hXC v hv⟩ ≤ F.dist u v := by
  let retract : V → C := fun z => if h : z ∈ X then ⟨z, hXC z h⟩ else ⟨u, hXC u hu⟩
  have hedge : ∀ a b, ((H.restrict C).comap retract) a b ≤ F a b := by
    intro a b
    by_cases hab : a ∈ X ∧ b ∈ X
    · simpa only [Graph.comap, Graph.restrict, retract, hab.1, hab.2, ↓reduceDIte] using hmono a b
    · have htop : F a b = ⊤ := by
        have he := congrFun (congrFun hF a) b
        simpa only [Implicit.induced, hab, ↓reduceIte] using he.symm
      rw [htop]
      exact le_top
  have hd := ((H.restrict C).dist_comap_le retract u v).trans (Graph.dist_mono hedge u v)
  simpa only [retract, hu, hv, ↓reduceDIte] using hd

theorem within_restrict_of_induced {V : Type*} [Fintype V]
    (H F : Graph V) (X : Finset V) (C : Set V) [Fintype C]
    (hXC : ∀ v ∈ X, v ∈ C) (hF : Implicit.induced F X = F)
    (hmono : ∀ u v, H u v ≤ F u v)
    (u v : V) (hu : u ∈ X) (hv : v ∈ X) (radius : ℝ)
    (h : Early.Within F u v radius) :
    Early.Within (H.restrict C) ⟨u, hXC u hu⟩ ⟨v, hXC v hv⟩ radius :=
  Early.bounded_mono_distance (restrict_distance_le_of_induced H F X C hXC hF hmono u v hu hv) h

end

end StreamingSSSP.Hopset.Geometry
