module

public import StreamingReachability.Graph.StoredEdges

@[expose] public section

namespace StreamingReachability.Core

open scoped Classical

variable {V : Type*} [Fintype V]

noncomputable def multiDist (G : Graph V) (seed : V → Distance) (v : V) : Distance :=
  Finset.univ.inf fun u => seed u + G.dist u v

theorem multiDist_le (G : Graph V) (seed : V → Distance) (u v : V) :
    multiDist G seed v ≤ seed u + G.dist u v :=
  Finset.inf_le_of_le (Finset.mem_univ u) le_rfl

theorem multiDist_attained (G : Graph V) (seed : V → Distance) (v : V) :
    ∃ u, multiDist G seed v = seed u + G.dist u v := by
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_inf Finset.univ
    (show (Finset.univ : Finset V).Nonempty from ⟨v, Finset.mem_univ v⟩)
    (fun u => seed u + G.dist u v)
  exact ⟨u, hu⟩

theorem multiDist_le_seed (G : Graph V) (seed : V → Distance) (v : V) :
    multiDist G seed v ≤ seed v := by
  simpa using multiDist_le G seed v v

theorem multiDist_triangle (G : Graph V) (seed : V → Distance) (u v : V) :
    multiDist G seed v ≤ multiDist G seed u + G.dist u v := by
  obtain ⟨y, hy⟩ := multiDist_attained G seed u
  calc
    multiDist G seed v ≤ seed y + G.dist y v := multiDist_le G seed y v
    _ ≤ seed y + (G.dist y u + G.dist u v) :=
      add_le_add le_rfl (G.dist_triangle y u v)
    _ = multiDist G seed u + G.dist u v := by rw [hy, add_assoc]

theorem multiDist_edge (G : Graph V) (seed : V → Distance) (u v : V) :
    multiDist G seed v ≤ multiDist G seed u + G u v :=
  (multiDist_triangle G seed u v).trans (add_le_add le_rfl (G.dist_le_edge u v))

theorem multiDist_mono {G F : Graph V} {seed initial : V → Distance}
    (hg : ∀ u v, G u v ≤ F u v) (hs : ∀ v, seed v ≤ initial v) (v : V) :
    multiDist G seed v ≤ multiDist F initial v := by
  apply Finset.le_inf
  intro u _
  exact (multiDist_le G seed u v).trans
    (add_le_add (hs u) (Graph.dist_mono hg u v))

theorem multiDist_potential {G F : Graph V} {seed initial : V → Distance}
    (hg : ∀ u v, G u v ≤ F u v)
    (hs : ∀ v, multiDist G seed v ≤ initial v) (v : V) :
    multiDist G seed v ≤ multiDist F initial v := by
  apply Finset.le_inf
  intro u _
  exact (multiDist_triangle G seed u v).trans
    (add_le_add (hs u) (Graph.dist_mono hg u v))

namespace StoredSearch

open StoredEdges

variable {n : ℕ}

def run (edges : List (Edge n)) (initial : DistanceArray n) : DistanceArray n :=
  runRounds edges (n - 1) initial

theorem lower (edges : List (Edge n)) (initial : DistanceArray n) (k : ℕ) :
    ∀ v, multiDist (graphOfEdges edges) initial.get v ≤
      (runRounds edges k initial).get v := by
  induction k with
  | zero => exact multiDist_le_seed _ _
  | succ k ih =>
      rw [runRounds_succ]
      apply relaxEdges_preserves_lower edges _ _
        (multiDist (graphOfEdges edges) initial.get) ih
      intro e he
      exact (multiDist_edge (graphOfEdges edges) initial.get e.source e.target).trans
        (add_le_add (ih e.source) (graphOfEdges_le_edge edges he))

theorem upper_path (edges : List (Edge n)) (initial : DistanceArray n) (k : ℕ)
    {u v : Fin n} {xs : List (Fin n)} (he : Graph.Endpoints xs u v)
    (hl : xs.length ≤ k + 1) :
    (runRounds edges k initial).get v ≤ initial.get u + (graphOfEdges edges).pathCost xs := by
  induction k generalizing v xs with
  | zero =>
      obtain ⟨x, tail, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty he)
      cases tail with
      | nil =>
          obtain ⟨rfl, rfl⟩ := (Graph.endpoints_singleton u v x).mp he
          simp [runRounds]
      | cons y ys =>
          simp only [List.length_cons] at hl
          omega
  | succ k ih =>
      obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp he.2
      cases pre with
      | nil =>
          have hv : v = u := by simpa [Graph.Endpoints] using he.1
          subst v
          simpa using runRounds_le_initial edges (k + 1) initial u
      | cons x pre =>
          obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp
            (List.getLast?_eq_none_iff.not.mpr (List.cons_ne_nil x pre))
          have hp : Graph.Endpoints (x :: pre) u a := by
            refine ⟨?_, ha⟩
            simpa [Graph.Endpoints] using he.1
          have hpl : (x :: pre).length ≤ k + 1 := by
            simp only [List.length_append, List.length_singleton] at hl
            omega
          rw [runRounds_succ]
          calc
            (relaxRound edges (runRounds edges k initial)).get v ≤
                (runRounds edges k initial).get a + graphOfEdges edges a v :=
              relaxRound_le_add_graph edges _ a v
            _ ≤ (initial.get u + (graphOfEdges edges).pathCost (x :: pre)) +
                graphOfEdges edges a v := add_le_add (ih hp hpl) le_rfl
            _ = initial.get u + (graphOfEdges edges).pathCost ((x :: pre) ++ [v]) := by
              rw [Graph.pathCost_append_of_getLast _ ha]
              simp [add_assoc]

theorem correct (edges : List (Edge n)) (initial : DistanceArray n) (v : Fin n) :
    (run edges initial).get v = multiDist (graphOfEdges edges) initial.get v := by
  apply le_antisymm _ (lower edges initial (n - 1) v)
  apply Finset.le_inf
  intro u _
  by_cases hu : (graphOfEdges edges).dist u v = ⊤
  · simp [hu]
  obtain ⟨xs, _, he, hl, hc⟩ := Graph.exists_dist_path _ hu
  have hn : 0 < n := Nat.zero_lt_of_lt v.isLt
  have hl' : xs.length ≤ (n - 1) + 1 := by
    simpa only [Fintype.card_fin, Nat.sub_add_cancel hn] using hl
  simpa only [run, hc] using upper_path edges initial (n - 1) he hl'

theorem memory (edges : List (Edge n)) (initial : DistanceArray n) (round scanned : ℕ) :
    workspaceCells edges (runRounds edges round initial)
      (relaxEdges (edges.take scanned) (runRounds edges round initial)
        (runRounds edges round initial)) = 3 * edges.length + 2 * n :=
  workspaceCells_eq edges _ _

end StoredSearch

end StreamingReachability.Core
