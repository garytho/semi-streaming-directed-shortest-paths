module

public import StreamingSSSP.Core.RoundingGraph
public import StreamingSSSP.Core.Scheduling
public import StreamingSSSP.Core.LabelOperations

@[expose] public section

namespace StreamingSSSP.Core

open scoped Classical

theorem distance_coe_untop {d : Distance} (hd : d ≠ ⊤) :
    ((d.untopD 0 : ℕ) : Distance) = d := by
  induction d using WithTop.recTopCoe with
  | top => contradiction
  | coe k => rfl

theorem distance_succ_le {r : ℕ} {d : Distance} (h : (r : Distance) < d) :
    ((r + 1 : ℕ) : Distance) ≤ d := by
  induction d using WithTop.recTopCoe with
  | top => exact le_top
  | coe k =>
      change ((r + 1 : ℕ) : WithTop ℕ) ≤ (k : WithTop ℕ)
      exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp h))

theorem distance_lt_succ_iff (d : Distance) (r : ℕ) :
    d < ((r + 1 : ℕ) : Distance) ↔ d ≤ (r : Distance) := by
  induction d using WithTop.recTopCoe with
  | top => simp
  | coe k =>
      change (k : WithTop ℕ) < ((r + 1 : ℕ) : WithTop ℕ) ↔
        (k : WithTop ℕ) ≤ (r : WithTop ℕ)
      norm_cast
      omega

namespace Query

open StoredEdges

variable {n : ℕ}

theorem edge_split (edges : List (Edge n)) (blocks : List (Finset (Fin n))) (A : ℕ)
    {u v : Fin n} (hf : queryGraph edges blocks A u v ≠ ⊤) :
    roundDistance A (graphOfEdges edges u v) ≤ queryGraph edges blocks A u v ∨
      ∃ B ∈ blocks, u ∈ B ∧ v ∈ B ∧ u ≠ v ∧
        roundDistance A ((BlockSearch.blockGraph edges B).dist u v) ≤
          queryGraph edges blocks A u v := by
  let c : Distance := blocks.toFinset.inf fun B =>
    if u ∈ B ∧ v ∈ B ∧ u ≠ v
    then roundDistance A ((BlockSearch.blockGraph edges B).dist u v) else ⊤
  by_cases ho : roundDistance A (graphOfEdges edges u v) ≤ c
  · exact Or.inl (by change _ ≤ min _ c; rw [min_eq_left ho])
  have he : queryGraph edges blocks A u v = c := min_eq_right (le_of_not_ge ho)
  have hne : blocks.toFinset.Nonempty := by
    by_contra h
    have hn := Finset.not_nonempty_iff_eq_empty.mp h
    exact hf (he.trans (by simp [c, hn]))
  obtain ⟨B, hB, hmin⟩ := Finset.exists_mem_eq_inf blocks.toFinset hne
    (fun B => if u ∈ B ∧ v ∈ B ∧ u ≠ v
      then roundDistance A ((BlockSearch.blockGraph edges B).dist u v) else ⊤)
  have hmem : u ∈ B ∧ v ∈ B ∧ u ≠ v := by
    by_contra h
    exact hf (he.trans (by simpa only [c, h, ↓reduceIte] using hmin))
  refine Or.inr ⟨B, List.mem_toFinset.mp hB, hmem.1, hmem.2.1, hmem.2.2, ?_⟩
  rw [he]
  exact (by simpa [c, hmem.1, hmem.2.1, hmem.2.2] using hmin.symm.le)

theorem predecessor_split (edges : List (Edge n)) (hp : ∀ e ∈ edges, 0 < e.weight)
    (blocks : List (Finset (Fin n))) (A : ℕ) (hA : 0 < A)
    (s v : Fin n) (r : ℕ) (hd : (queryGraph edges blocks A).dist s v = (r : Distance)) :
    (v = s ∧ r = 0) ∨ ∃ u,
      (queryGraph edges blocks A).dist s u < (r : Distance) ∧
      ((∃ e ∈ edges, e.source = u ∧ e.target = v ∧
        (queryGraph edges blocks A).dist s u + (ceilNat A e.weight : Distance) ≤ (r : Distance)) ∨
       ∃ B ∈ blocks, u ∈ B ∧ v ∈ B ∧
        (queryGraph edges blocks A).dist s u +
          roundDistance A ((BlockSearch.blockGraph edges B).dist u v) ≤ (r : Distance)) := by
  by_cases hvs : v = s
  · subst v
    left
    refine ⟨rfl, ?_⟩
    have hh : (r : Distance) = ((0 : ℕ) : Distance) := by
      simpa only [Graph.dist_self, Nat.cast_zero] using hd.symm
    exact_mod_cast hh
  have hfinite : (queryGraph edges blocks A).dist s v ≠ ⊤ := by rw [hd]; exact WithTop.natCast_ne_top r
  obtain ⟨u, _, he, hlt⟩ := Graph.exists_shortest_predecessor_of_pos
    (queryGraph edges blocks A) (positive edges hp blocks A hA) (Ne.symm hvs) hfinite
  have hed : queryGraph edges blocks A u v ≠ ⊤ := by
    intro ht
    rw [ht, add_top] at he
    exact hfinite he.symm
  refine Or.inr ⟨u, by simpa only [hd] using hlt, ?_⟩
  rcases edge_split edges blocks A hed with ho | ⟨B, hB, hu, hv, _, hw⟩
  · left
    have hg : graphOfEdges edges u v ≠ ⊤ := by
      intro ht
      simp only [ht, roundDistance_top] at ho
      exact hed (top_le_iff.mp ho)
    obtain ⟨e, hee, hs, ht, hw⟩ := exists_edge_eq edges hg
    refine ⟨e, hee, hs, ht, ?_⟩
    calc
      _ = (queryGraph edges blocks A).dist s u + roundDistance A (graphOfEdges edges u v) := by
        rw [← hw]; rfl
      _ ≤ (queryGraph edges blocks A).dist s u + queryGraph edges blocks A u v := add_le_add le_rfl ho
      _ = (r : Distance) := he.trans hd
  · exact Or.inr ⟨B, hB, hu, hv, (add_le_add le_rfl hw).trans (he.trans hd).le⟩

end Query

end StreamingSSSP.Core
