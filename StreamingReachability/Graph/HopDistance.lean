module

public import StreamingReachability.Graph

@[expose] public section

namespace StreamingReachability.Graph

open scoped Classical

variable {V : Type*} [Fintype V]

/-- Walks have at most `hops` edges, hence at most `hops + 1` vertices. -/
noncomputable def hopDist (G : Graph V) (hops : ℕ) (s t : V) : Distance :=
  (routes (V := V) (hops + 1)).inf fun xs =>
    if Endpoints xs s t then G.pathCost xs else ⊤

theorem hopDist_le_pathCost (G : Graph V) {hops : ℕ} {s t : V} {xs : List V}
    (he : Endpoints xs s t) (hl : xs.length ≤ hops + 1) :
    G.hopDist hops s t ≤ G.pathCost xs := by
  classical
  exact Finset.inf_le_of_le ((mem_routes _ _).mpr hl) (by simp [he])

theorem le_hopDist_iff (G : Graph V) (hops : ℕ) (s t : V) (d : Distance) :
    d ≤ G.hopDist hops s t ↔
      ∀ xs, Endpoints xs s t → xs.length ≤ hops + 1 → d ≤ G.pathCost xs := by
  classical
  refine ⟨fun h xs he hl => h.trans (G.hopDist_le_pathCost he hl), ?_⟩
  intro h
  exact Finset.le_inf fun xs hx => by
    split_ifs with he
    · exact h xs he ((mem_routes _ _).mp hx)
    · exact le_top

theorem exists_hopDist_path (G : Graph V) {hops : ℕ} {s t : V}
    (h : G.hopDist hops s t ≠ ⊤) :
    ∃ xs : List V, xs.Nodup ∧ Endpoints xs s t ∧
      xs.length ≤ hops + 1 ∧ G.pathCost xs = G.hopDist hops s t := by
  classical
  obtain ⟨xs, hm, hx⟩ := Finset.exists_mem_eq_inf
    (routes (V := V) (hops + 1))
    ⟨[], (mem_routes _ _).mpr (by simp)⟩
    (fun xs => if Endpoints xs s t then G.pathCost xs else ⊤)
  have he : Endpoints xs s t := by
    by_contra hn
    exact h (by simpa [hopDist, hn] using hx)
  have hc : G.hopDist hops s t = G.pathCost xs := by simpa [hopDist, he] using hx
  have hl := (mem_routes _ _).mp hm
  obtain ⟨_, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty he)
  obtain ⟨ys, hn, hh, ht, hsub, hcost⟩ := G.exists_simple_path _ tail
  have hends : Endpoints ys s t := ⟨hh.trans he.1, ht.trans he.2⟩
  have hlen : ys.length ≤ hops + 1 := hsub.length_le.trans hl
  exact ⟨ys, hn, hends, hlen,
    le_antisymm (hcost.trans hc.ge) (G.hopDist_le_pathCost hends hlen)⟩

@[simp] theorem hopDist_self (G : Graph V) (hops : ℕ) (s : V) :
    G.hopDist hops s s = 0 := by
  exact le_antisymm (G.hopDist_le_pathCost (xs := [s]) (by simp) (by simp)) bot_le

theorem dist_le_hopDist (G : Graph V) (hops : ℕ) (s t : V) :
    G.dist s t ≤ G.hopDist hops s t := by
  exact (G.le_hopDist_iff hops s t _).mpr fun _ he _ => G.dist_le_pathCost he

theorem hopDist_antitone (G : Graph V) (s t : V) :
    Antitone (fun hops => G.hopDist hops s t) := by
  intro h k hhk
  apply (G.le_hopDist_iff h s t _).mpr
  intro xs he hl
  exact G.hopDist_le_pathCost he (hl.trans (Nat.add_le_add_right hhk 1))

theorem hopDist_mono_weights {G F : Graph V} (h : ∀ u v, G u v ≤ F u v)
    (hops : ℕ) (s t : V) : G.hopDist hops s t ≤ F.hopDist hops s t := by
  apply (F.le_hopDist_iff hops s t _).mpr
  intro xs he hl
  exact (G.hopDist_le_pathCost he hl).trans (pathCost_mono h xs)

theorem hopDist_eq_dist_of_card_le (G : Graph V) (hops : ℕ) (s t : V)
    (h : Fintype.card V ≤ hops + 1) : G.hopDist hops s t = G.dist s t := by
  refine le_antisymm ?_ (G.dist_le_hopDist hops s t)
  apply (G.le_dist_iff s t _).mpr
  intro xs he
  obtain ⟨_, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty he)
  obtain ⟨ys, hn, hh, ht, _, hc⟩ := G.exists_simple_path _ tail
  exact (G.hopDist_le_pathCost ⟨hh.trans he.1, ht.trans he.2⟩
    ((simple_length_le hn).trans h)).trans hc

@[simp] theorem hopDist_card_sub_one (G : Graph V) (s t : V) :
    G.hopDist (Fintype.card V - 1) s t = G.dist s t := by
  apply G.hopDist_eq_dist_of_card_le
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  omega

theorem hopDist_le_edge (G : Graph V) (s t : V) :
    G.hopDist 1 s t ≤ G s t := by
  simpa using G.hopDist_le_pathCost (xs := [s, t]) (by simp [Endpoints]) (by simp)

theorem hopDist_triangle (G : Graph V) (h k : ℕ) (s u t : V) :
    G.hopDist (h + k) s t ≤ G.hopDist h s u + G.hopDist k u t := by
  by_cases hsu : G.hopDist h s u = ⊤
  · simp [hsu]
  by_cases hut : G.hopDist k u t = ⊤
  · simp [hut]
  obtain ⟨xs, _, hx, hlx, hcx⟩ := G.exists_hopDist_path hsu
  obtain ⟨ys, _, hy, hly, hcy⟩ := G.exists_hopDist_path hut
  obtain ⟨v, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty hy)
  have hv : v = u := by simpa [Endpoints] using hy.1
  subst v
  calc
    G.hopDist (h + k) s t ≤ G.pathCost (xs ++ tail) :=
      G.hopDist_le_pathCost (endpoints_append hx hy) (by
        simp only [List.length_append]
        simp only [List.length_cons] at hly
        omega)
    _ = G.pathCost xs + G.pathCost (u :: tail) := G.pathCost_append_of_getLast hx.2 tail
    _ = G.hopDist h s u + G.hopDist k u t := by rw [hcx, hcy]

theorem hopDist_succ_le_add_edge (G : Graph V) (hops : ℕ) (s u t : V) :
    G.hopDist (hops + 1) s t ≤ G.hopDist hops s u + G u t :=
  (G.hopDist_triangle hops 1 s u t).trans (add_le_add le_rfl (G.hopDist_le_edge u t))

end StreamingReachability.Graph
