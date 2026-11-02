module

public import StreamingReachability.Core.Rounding

@[expose] public section

namespace StreamingReachability.Core

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def scaledSeeds (A : ℕ) (known : Finset V) (d : V → ℕ) : V → Distance :=
  fun u => if u ∈ known then ((A * d u : ℕ) : Distance) else ⊤

theorem multiDist_supported (G : Graph V) (K : Finset V) (seed : V → Distance)
    (v : V) :
    multiDist G (fun u => if u ∈ K then seed u else ⊤) v =
      K.inf (fun u => seed u + G.dist u v) := by
  apply le_antisymm
  · apply Finset.le_inf
    intro u hu
    simpa only [hu, ↓reduceIte] using
      multiDist_le G (fun u => if u ∈ K then seed u else ⊤) u v
  · apply Finset.le_inf
    intro u _
    by_cases hu : u ∈ K
    · simpa only [hu, ↓reduceIte] using
        (Finset.inf_le hu : K.inf (fun u => seed u + G.dist u v) ≤ _)
    · simp [hu]

theorem closure_rounding_once (G : Graph V) (A : ℕ) (hA : 0 < A)
    (known : Finset V) (d : V → ℕ) (v : V) :
    roundDistance A (multiDist G (scaledSeeds A known d) v) =
      known.inf (fun u => (d u : Distance) + roundDistance A (G.dist u v)) := by
  unfold scaledSeeds
  rw [multiDist_supported, roundDistance_inf A hA]
  apply Finset.inf_congr rfl
  intro u _
  exact roundDistance_add_multiple hA (d u) (G.dist u v)

theorem positive_dist {G : Graph V} (hp : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    {s t : V} (hst : s ≠ t) : (1 : Distance) ≤ G.dist s t := by
  apply (G.le_dist_iff s t 1).mpr
  intro xs he
  obtain ⟨u, tail, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty he)
  have hu : u = s := by simpa [Graph.Endpoints] using he.1
  subst u
  induction tail generalizing s with
  | nil =>
      have heq : s = t := by simpa [Graph.Endpoints] using he.2
      exact False.elim (hst heq)
  | cons u tail ih =>
      by_cases hsu : s = u
      · subst s
        have he' : Graph.Endpoints (u :: tail) u t :=
          ⟨rfl, by simpa [Graph.Endpoints] using he.2⟩
        exact (ih hst he').trans (G.pathCost_tail_le u (u :: tail))
      · exact (hp s u hsu).trans (by
          rw [Graph.pathCost_cons_cons]
          exact le_add_of_nonneg_right bot_le)

theorem rounded_positive (A : ℕ) (hA : 0 < A) {w : Distance}
    (hw : (1 : Distance) ≤ w) : (1 : Distance) ≤ roundDistance A w := by
  have hn : 1 ≤ ceilNat A 1 := by
    by_contra h
    have hz : ceilNat A 1 ≤ 0 := by omega
    have hh : (1 : ℕ) ≤ A * 0 := (ceilNat_le_iff hA).mp hz
    omega
  have h1 : (1 : Distance) ≤ roundDistance A 1 := by
    change (1 : WithTop ℕ) ≤ (ceilNat A 1 : WithTop ℕ)
    exact WithTop.coe_le_coe.mpr hn
  exact h1.trans (roundDistance_mono hA hw)

namespace Query

open StoredEdges

variable {n : ℕ}

theorem le_ordinary (edges : List (Edge n)) (blocks : List (Finset (Fin n))) (A : ℕ)
    (u v : Fin n) :
    queryGraph edges blocks A u v ≤ roundDistance A (graphOfEdges edges u v) :=
  min_le_left _ _

theorem le_closure (edges : List (Edge n)) (blocks : List (Finset (Fin n))) (A : ℕ)
    {B : Finset (Fin n)} (hB : B ∈ blocks) {u v : Fin n}
    (hu : u ∈ B) (hv : v ∈ B) (hne : u ≠ v) :
    queryGraph edges blocks A u v ≤
      roundDistance A ((BlockSearch.blockGraph edges B).dist u v) := by
  apply (min_le_right _ _).trans
  exact Finset.inf_le_of_le (List.mem_toFinset.mpr hB)
    (by simp [hu, hv, hne])

theorem base_positive (edges : List (Edge n)) (hp : ∀ e ∈ edges, 0 < e.weight)
    (u v : Fin n) : (1 : Distance) ≤ graphOfEdges edges u v := by
  apply (le_graphOfEdges_iff edges u v 1).mpr
  intro e he _ _
  exact WithTop.coe_le_coe.mpr (hp e he)

theorem block_positive (edges : List (Edge n)) (hp : ∀ e ∈ edges, 0 < e.weight)
    (B : Finset (Fin n)) (u v : Fin n) : (1 : Distance) ≤ BlockSearch.blockGraph edges B u v := by
  unfold BlockSearch.blockGraph
  split_ifs
  · exact base_positive edges hp u v
  · exact le_top

theorem positive (edges : List (Edge n)) (hp : ∀ e ∈ edges, 0 < e.weight)
    (blocks : List (Finset (Fin n))) (A : ℕ) (hA : 0 < A)
    (u v : Fin n) : (1 : Distance) ≤ queryGraph edges blocks A u v := by
  apply le_min (rounded_positive A hA (base_positive edges hp u v))
  apply Finset.le_inf
  intro B _
  split_ifs with h
  · apply rounded_positive A hA
    exact positive_dist (fun a b _ => block_positive edges hp B a b) h.2.2
  · exact le_top

theorem block_sound (edges : List (Edge n)) (blocks : List (Finset (Fin n)))
    (A : ℕ) (hA : 0 < A) (s : Fin n) {B : Finset (Fin n)} (hB : B ∈ blocks)
    (K : Finset (Fin n)) (d : Fin n → ℕ) (hK : K ⊆ B)
    (hd : ∀ u ∈ K, (queryGraph edges blocks A).dist s u = (d u : Distance))
    {v : Fin n} (hv : v ∈ B) :
    (queryGraph edges blocks A).dist s v ≤
      roundDistance A (multiDist (BlockSearch.blockGraph edges B) (scaledSeeds A K d) v) := by
  rw [closure_rounding_once _ A hA K d v]
  apply Finset.le_inf
  intro u hu
  by_cases huv : u = v
  · subst u
    simp only [Graph.dist_self]
    have hzero : roundDistance A 0 = 0 := by
      change (ceilNat A 0 : Distance) = 0
      rw [ceilNat_zero hA]
      rfl
    rw [hzero, add_zero, hd v hu]
  · calc
      (queryGraph edges blocks A).dist s v ≤
          (queryGraph edges blocks A).dist s u + queryGraph edges blocks A u v :=
        Graph.dist_le_dist_add_edge _ _ _ _
      _ ≤ (d u : Distance) +
          roundDistance A ((BlockSearch.blockGraph edges B).dist u v) := by
        rw [hd u hu]
        exact add_le_add le_rfl (le_closure edges blocks A hB (hK hu) hv huv)

end Query

end StreamingReachability.Core
