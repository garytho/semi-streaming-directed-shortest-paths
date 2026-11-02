module

public import StreamingSSSP.Graph

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*}

theorem finite_of_le {x : Distance} {k : ℕ} (h : x ≤ k) :
    ∃ j : ℕ, x = j ∧ j ≤ k := by
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
  lift x to ℕ using hx with j
  exact ⟨j, rfl, WithTop.coe_le_coe.mp h⟩

theorem finite_add {x y : Distance} {k : ℕ} (h : x + y = k) :
    ∃ a b : ℕ, x = a ∧ y = b ∧ a + b = k := by
  obtain ⟨a, ha, _⟩ := finite_of_le
    (show x ≤ (k : Distance) from h ▸ le_add_of_nonneg_right bot_le)
  obtain ⟨b, hb, _⟩ := finite_of_le
    (show y ≤ (k : Distance) from h ▸ le_add_of_nonneg_left bot_le)
  refine ⟨a, b, ha, hb, ?_⟩
  rw [ha, hb] at h
  change (a : WithTop ℕ) + (b : WithTop ℕ) = (k : WithTop ℕ) at h
  exact WithTop.coe_eq_coe.mp ((WithTop.coe_add a b).trans h)

/-- A finite path, with its actual (not merely upper-bounded) integer cost. -/
structure Route (G : Graph V) (s t : V) where
  vertices : List V
  endpoints : Graph.Endpoints vertices s t
  cost : ℕ
  cost_eq : G.pathCost vertices = cost

namespace Route

def refl (G : Graph V) (v : V) : Route G v v :=
  ⟨[v], by simp, 0, rfl⟩

def edge {G : Graph V} {u v : V} {w : ℕ} (h : G u v = w) :
    Route G u v :=
  ⟨[u, v], by simp [Graph.Endpoints], w, by simp [h]⟩

theorem dist_le [Fintype V] {G : Graph V} {s t : V} (p : Route G s t) :
    G.dist s t ≤ p.cost := by
  rw [← p.cost_eq]
  exact G.dist_le_pathCost p.endpoints

end Route

noncomputable def shortestRoute [Fintype V] (G : Graph V) {s t : V} {d : ℕ}
    (hd : G.dist s t = d) : Route G s t := by
  let h := G.exists_dist_path (s := s) (t := t) (by simp [hd])
  exact ⟨Classical.choose h, (Classical.choose_spec h).2.1, d,
    (Classical.choose_spec h).2.2.2.trans hd⟩

/-- The usual path telescoping argument also permits signed potentials. -/
theorem potential_le_path {G : Graph V} (f : V → ℤ)
    (hedge : ∀ u v (w : ℕ), G u v = (w : Distance) → f v ≤ f u + w)
    {xs : List V} {s t : V} {c : ℕ}
    (he : Graph.Endpoints xs s t) (hc : G.pathCost xs = c) :
    f t ≤ f s + c := by
  induction xs generalizing s c with
  | nil => simp [Graph.Endpoints] at he
  | cons u xs ih =>
      have hu : u = s := by simpa [Graph.Endpoints] using he.1
      subst u
      cases xs with
      | nil =>
          have ht : s = t := by simpa [Graph.Endpoints] using he.2
          subst t
          have hc0 : c = 0 := by simpa using hc.symm
          simp [hc0]
      | cons v xs =>
          obtain ⟨a, b, ha, hb, hab⟩ := finite_add hc
          have he' : Graph.Endpoints (v :: xs) v t := by
            exact ⟨rfl, by simpa [Graph.Endpoints] using he.2⟩
          have hi := ih he' hb
          have hj := hedge s v a ha
          have hab' : (a : ℤ) + b = c := by exact_mod_cast hab
          omega

theorem pathCost_prefix_le (G : Graph V) (xs ys : List V) :
    G.pathCost xs ≤ G.pathCost (xs ++ ys) := by
  induction xs with
  | nil => simp
  | cons u xs ih =>
      cases xs with
      | nil => exact bot_le
      | cons v xs =>
          simp only [List.cons_append, Graph.pathCost_cons_cons] at *
          exact add_le_add le_rfl ih

/-- Prefixes and suffixes of a finite path never cost more than the path. -/
theorem route_vertex_bounds [Fintype V] {G : Graph V} {s t x : V}
    (p : Route G s t) (hx : x ∈ p.vertices) :
    ∃ a b : ℕ, G.dist s x ≤ a ∧ G.dist x t ≤ b ∧ a ≤ p.cost ∧ b ≤ p.cost := by
  classical
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hx
  have hsuf : G.pathCost (x :: post) ≤ p.cost := by
    rw [← p.cost_eq, hsplit]
    exact G.pathCost_suffix_le pre (x :: post)
  obtain ⟨b, hb, hbc⟩ := finite_of_le hsuf
  have hpre : G.pathCost (pre ++ [x]) ≤ p.cost := by
    rw [← p.cost_eq, hsplit]
    simpa [List.append_assoc] using pathCost_prefix_le G (pre ++ [x]) post
  obtain ⟨a, ha, hac⟩ := finite_of_le hpre
  refine ⟨a, b, ?_, ?_, hac, hbc⟩
  · rw [← ha]
    apply G.dist_le_pathCost
    constructor
    · have hp := p.endpoints.1
      rw [hsplit] at hp
      cases pre <;> simpa using hp
    · simp [Graph.Endpoints]
  · rw [← hb]
    exact G.dist_le_pathCost ⟨rfl, by
      have hp := p.endpoints.2
      simpa [hsplit] using hp⟩

end StreamingSSSP.Exact
