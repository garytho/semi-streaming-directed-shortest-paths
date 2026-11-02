module

public import StreamingReachability.Hopset.ReferenceFacts

@[expose] public section

namespace StreamingReachability

open scoped Classical

noncomputable section

namespace Graph

theorem dist_top_of_row_top {V : Type*} [Fintype V] (G : Graph V) (s t : V) (hne : s ≠ t)
    (hrow : ∀ v, G s v = ⊤) : G.dist s t = ⊤ := by
  apply (G.dist_eq_top_iff s t).mpr
  rintro ⟨xs, he, hf⟩
  cases xs with
  | nil => simp [Endpoints] at he
  | cons u xs =>
      have hu : u = s := by simpa [Endpoints] using he.1
      subst u
      cases xs with
      | nil =>
          have hst : s = t := by simpa [Endpoints] using he.2
          exact hne hst
      | cons v xs => simp [pathCost_cons_cons, hrow v] at hf

end Graph

namespace Hopset.Geometry

variable {n : ℕ}

theorem outside_inball (G : Graph (Fin n)) (S : Finset (Fin n))
    (hG : Implicit.induced G S = G) (v : Fin n) (hv : v ∉ S) (radius : ℝ) :
    Early.searchIn G v radius ⊆ {v} := by
  have hcolumn (u : Fin n) : G u v = ⊤ := by
    have h := congrFun (congrFun hG u) v
    simpa only [Implicit.induced, hv, and_false, ↓reduceIte] using h.symm
  intro u hu
  by_cases he : u = v
  · exact Finset.mem_singleton.mpr he
  · have hd : G.dist u v = ⊤ := by
      have h := Graph.dist_top_of_row_top G.reverse v u (Ne.symm he) hcolumn
      simpa only [Graph.dist_reverse] using h
    obtain ⟨q, hq, hr⟩ := (Finset.mem_filter.mp hu).2
    rw [hd] at hq
    simp at hq

theorem outside_outball (G : Graph (Fin n)) (S : Finset (Fin n))
    (hG : Implicit.induced G S = G) (v : Fin n) (hv : v ∉ S) (radius : ℝ) :
    Early.searchOut G v radius ⊆ {v} := by
  have hrow (u : Fin n) : G v u = ⊤ := by
    have h := congrFun (congrFun hG v) u
    simpa only [Implicit.induced, hv, false_and, ↓reduceIte] using h.symm
  intro u hu
  by_cases he : u = v
  · exact Finset.mem_singleton.mpr he
  · have hd := Graph.dist_top_of_row_top G v u (Ne.symm he) hrow
    obtain ⟨q, hq, hr⟩ := (Finset.mem_filter.mp hu).2
    rw [hd] at hq
    simp at hq

end Hopset.Geometry

namespace Hopset.Reference

theorem ballsGood_all_vertices {n : ℕ} (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n))
    (hballs : BallsGood cfg stored input r S) (hb : 1 ≤ Parameters.ballSize n r) :
    ∀ v : Fin n,
      (Early.searchIn (Backend.roundedRestricted stored input S cfg.inputScale)
        v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ Parameters.ballSize n r ∧
      (Early.searchOut (Backend.roundedRestricted stored input S cfg.inputScale)
        v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ Parameters.ballSize n r := by
  intro v
  by_cases hv : v ∈ S
  · exact hballs v hv
  · have hG := Late.search_induced stored (StoredEdges.graphOfEdges input) S cfg.inputScale
    constructor
    · exact (Finset.card_le_card (Geometry.outside_inball _ S hG v hv _)).trans (by simpa using hb)
    · exact (Finset.card_le_card (Geometry.outside_outball _ S hG v hv _)).trans (by simpa using hb)

end Hopset.Reference

end

end StreamingReachability
