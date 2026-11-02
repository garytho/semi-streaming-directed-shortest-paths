module

public import StreamingSSSP.Core.ClosureDistances

@[expose] public section

namespace StreamingSSSP.Core

open scoped Classical

theorem roundDistance_min (A : ℕ) (hA : 0 < A) (u v : Distance) :
    roundDistance A (min u v) = min (roundDistance A u) (roundDistance A v) := by
  by_cases h : u ≤ v
  · rw [min_eq_left h, min_eq_left (roundDistance_mono hA h)]
  · have h' := le_of_not_ge h
    rw [min_eq_right h', min_eq_right (roundDistance_mono hA h')]

namespace RoundedEdges

open StoredEdges

variable {n : ℕ}

def rounded (A : ℕ) (e : Edge n) : Edge n :=
  { e with weight := ceilNat A e.weight }

theorem graph_rounding (A : ℕ) (hA : 0 < A) (input : List (Edge n)) (u v : Fin n) :
    graphOfEdges (input.map (rounded A)) u v = roundDistance A (graphOfEdges input u v) := by
  induction input with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, graphOfEdges_cons, roundDistance_min A hA, ih]
      by_cases h : e.source = u ∧ e.target = v
      · simp [edgeCost, rounded, h, roundDistance]
      · simp [edgeCost, rounded, h, roundDistance]

end RoundedEdges

section Diagonal

variable {V : Type*}

theorem nodup_pathCost_congr {G F : Graph V} (h : ∀ u v, u ≠ v → G u v = F u v)
    {xs : List V} (hn : xs.Nodup) : G.pathCost xs = F.pathCost xs := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
      cases xs with
      | nil => rfl
      | cons v xs =>
          obtain ⟨hu, ht⟩ := List.nodup_cons.mp hn
          have huv : u ≠ v := fun he => hu (by simp [he])
          rw [Graph.pathCost_cons_cons, Graph.pathCost_cons_cons, h u v huv, ih ht]

theorem dist_congr_off_diagonal [Fintype V] {G F : Graph V}
    (h : ∀ u v, u ≠ v → G u v = F u v) (s t : V) :
    G.dist s t = F.dist s t := by
  have hle {P Q : Graph V} (hpq : ∀ u v, u ≠ v → P u v = Q u v) :
      P.dist s t ≤ Q.dist s t := by
    by_cases htop : Q.dist s t = ⊤
    · rw [htop]; exact le_top
    obtain ⟨xs, hn, he, _, hc⟩ := Q.exists_dist_path htop
    exact (P.dist_le_pathCost he).trans_eq ((nodup_pathCost_congr hpq hn).trans hc)
  exact le_antisymm (hle h) (hle (fun u v hne => (h u v hne).symm))

end Diagonal

noncomputable def fullQueryGraph {n : ℕ} (edges : List (StoredEdges.Edge n))
    (blocks : List (Finset (Fin n))) (A : ℕ) : Graph (Fin n) :=
  fun u v => min (roundDistance A (StoredEdges.graphOfEdges edges u v))
    (blocks.toFinset.inf fun B =>
      if u ∈ B ∧ v ∈ B
      then roundDistance A ((BlockSearch.blockGraph edges B).dist u v) else ⊤)

theorem queryGraph_dist_eq_full {n : ℕ} (edges : List (StoredEdges.Edge n))
    (blocks : List (Finset (Fin n))) (A : ℕ) (s t : Fin n) :
    (queryGraph edges blocks A).dist s t = (fullQueryGraph edges blocks A).dist s t := by
  apply dist_congr_off_diagonal
  intro u v huv
  unfold queryGraph fullQueryGraph
  congr 1
  apply Finset.inf_congr rfl
  intro B _
  by_cases hb : u ∈ B ∧ v ∈ B
  · rw [ite_eq_left ⟨hb.1, hb.2, huv⟩, ite_eq_left hb]
  · rw [ite_eq_right (fun h => hb ⟨h.1, h.2.1⟩), ite_eq_right hb]

end StreamingSSSP.Core
