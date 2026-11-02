module

public import StreamingSSSP.Exact.PositiveOracle
public import StreamingSSSP.Core.RoundingGraph
public import StreamingSSSP.Hopset.Representation

@[expose] public section

namespace StreamingSSSP

open scoped Classical

namespace Graph

variable {V : Type*}

def scaled (G : Graph V) (A : ℕ) : Graph V := Exact.affineGraph G A 0

theorem scaled_apply (G : Graph V) (A : ℕ) (u v : V) :
    scaled G A u v = WithTop.map (fun d => A * d) (G u v) := by
  simp [scaled, Exact.affineGraph, Exact.mapWeights]

theorem scaled_dist [Fintype V] (G : Graph V) (A : ℕ) (s t : V) :
    (scaled G A).dist s t = WithTop.map (fun d => A * d) (G.dist s t) := by
  by_cases htop : G.dist s t = ⊤
  · have hs : (scaled G A).dist s t = ⊤ := by
      by_contra hn
      obtain ⟨xs, _, he, _, hc⟩ := (scaled G A).exists_dist_path hn
      have hfinite : G.pathCost xs ≠ ⊤ :=
        (Exact.affine_path_finite G A 0 xs).mp (by
          change (scaled G A).pathCost xs ≠ ⊤
          rwa [hc])
      have hb := G.dist_le_pathCost he
      rw [htop] at hb
      exact hfinite (top_le_iff.mp hb)
    simp [hs, htop]
  · lift G.dist s t to ℕ using htop with d hd
    obtain ⟨e, he, hl, hu⟩ := Exact.affine_dist_bounds G A 0 hd.symm
    have heq : e = A * d := by omega
    simpa [scaled, heq, ← hd] using he

theorem scaled_pathCost (G : Graph V) (A : ℕ) (xs : List V) :
    (scaled G A).pathCost xs = WithTop.map (fun d => A * d) (G.pathCost xs) := by
  by_cases htop : G.pathCost xs = ⊤
  · have hs : (scaled G A).pathCost xs = ⊤ := by
      by_contra hn
      exact ((Exact.affine_path_finite G A 0 xs).mp hn) htop
    simp [hs, htop]
  · lift G.pathCost xs to ℕ using htop with d hd
    simpa [scaled, ← hd] using Exact.affine_pathCost G A 0 xs d hd.symm

end Graph

theorem le_scale_round (A : ℕ) (hA : 0 < A) (d : Distance) :
    d ≤ WithTop.map (fun w => A * w) (Core.roundDistance A d) := by
  induction d using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe d =>
      change (d : Distance) ≤ ((A * Core.ceilNat A d : ℕ) : Distance)
      exact WithTop.coe_le_coe.mpr ((Core.ceilNat_le_iff hA).mp le_rfl)

theorem noncontracting_rounded_dist {V : Type*} [Fintype V]
    (G F : Graph V) (A : ℕ) (hA : 0 < A) (hF : Implicit.Noncontracting G F)
    (s t : V) :
    G.dist s t ≤ WithTop.map (fun d => A * d)
      (Graph.dist (fun u v => Core.roundDistance A (F u v)) s t) := by
  let Q : Graph V := fun u v => Core.roundDistance A (F u v)
  have hscale : Implicit.Noncontracting G (Graph.scaled Q A) := by
    intro u v
    rw [Graph.scaled_apply]
    exact (hF u v).trans (le_scale_round A hA (F u v))
  have h := Implicit.dist_le_of_noncontracting G (Graph.scaled Q A) hscale s t
  rwa [Graph.scaled_dist] at h

namespace Implicit.Representation

variable {n : ℕ}

def Sound (stored : Representation n) (G : Graph (Fin n)) : Prop :=
  ∀ e ∈ stored.explicit, G.dist e.source e.target ≤ (e.weight : Distance)

theorem sound_base (stored : Representation n) (G : Graph (Fin n)) (h : stored.Sound G) :
    Implicit.Noncontracting G (stored.base G) := by
  intro u v
  apply le_min (Graph.dist_le_edge G u v)
  apply (StoredEdges.le_graphOfEdges_iff stored.explicit u v _).mpr
  intro e he hs ht
  simpa only [hs, ht] using h e he

theorem sound_graph (stored : Representation n) (G : Graph (Fin n)) (h : stored.Sound G) :
    Implicit.Noncontracting G (stored.graph G) :=
  Implicit.closures_noncontracting G _ _ (sound_base stored G h)

theorem sound_restricted (stored : Representation n) (G : Graph (Fin n))
    (h : stored.Sound G) (S : Finset (Fin n)) :
    Implicit.Noncontracting G (stored.restricted G S) := by
  apply Implicit.closures_noncontracting
  intro u v
  exact (sound_base stored G h u v).trans (Implicit.le_induced (stored.base G) S u v)

theorem sound_base_over (stored : Representation n) (G F : Graph (Fin n))
    (hinput : Implicit.Noncontracting G F) (h : stored.Sound G) :
    Implicit.Noncontracting G (stored.base F) := by
  intro u v
  apply le_min (hinput u v)
  apply (StoredEdges.le_graphOfEdges_iff stored.explicit u v _).mpr
  intro e he hs ht
  simpa only [hs, ht] using h e he

theorem sound_restricted_over (stored : Representation n) (G F : Graph (Fin n))
    (hinput : Implicit.Noncontracting G F) (h : stored.Sound G) (S : Finset (Fin n)) :
    Implicit.Noncontracting G (stored.restricted F S) := by
  apply Implicit.closures_noncontracting
  intro u v
  exact (sound_base_over stored G F hinput h u v).trans
    (Implicit.le_induced (stored.base F) S u v)

theorem sound_distance (stored : Representation n) (G : Graph (Fin n)) (h : stored.Sound G) :
    (stored.graph G).dist = G.dist := by
  apply Implicit.distance_unchanged G _ (sound_graph stored G h)
  intro u v
  exact (Implicit.closures_le_base (stored.base G) stored.blocks u v).trans (min_le_left _ _)

end Implicit.Representation

end StreamingSSSP
