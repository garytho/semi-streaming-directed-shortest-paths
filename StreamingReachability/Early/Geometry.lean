module

public import StreamingReachability.Graph

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

variable {V : Type*} [Fintype V]

/-- A real search radius is measured in the integer distance units of the graph.
Unreachable pairs are never in a ball, including at a negative radius. -/
def Bounded (d : Distance) (R : ℝ) : Prop :=
  ∃ n : ℕ, d = n ∧ (n : ℝ) ≤ R

def Within (G : Graph V) (u v : V) (R : ℝ) : Prop :=
  Bounded (G.dist u v) R

theorem bounded_mono_radius {d : Distance} {R S : ℝ}
    (h : Bounded d R) (hRS : R ≤ S) : Bounded d S := by
  obtain ⟨n, hn, hR⟩ := h
  exact ⟨n, hn, hR.trans hRS⟩

theorem bounded_mono_distance {d e : Distance} {R : ℝ}
    (hde : d ≤ e) (he : Bounded e R) : Bounded d R := by
  obtain ⟨n, rfl, hn⟩ := he
  have hd : d ≠ ⊤ := by
    intro ht
    simp [ht] at hde
  lift d to ℕ using hd with m hm
  have hmn : m ≤ n := WithTop.coe_le_coe.mp hde
  exact ⟨m, rfl, (by exact_mod_cast hmn : (m : ℝ) ≤ n).trans hn⟩

theorem bounded_add {d e : Distance} {R S : ℝ}
    (hd : Bounded d R) (he : Bounded e S) : Bounded (d + e) (R + S) := by
  obtain ⟨m, rfl, hm⟩ := hd
  obtain ⟨n, rfl, hn⟩ := he
  exact ⟨m + n, by simp, by exact_mod_cast add_le_add hm hn⟩

theorem within_mono {G : Graph V} {u v : V} {R S : ℝ}
    (h : Within G u v R) (hRS : R ≤ S) : Within G u v S :=
  bounded_mono_radius h hRS

theorem within_trans {G : Graph V} {u v w : V} {R S : ℝ}
    (huv : Within G u v R) (hvw : Within G v w S) :
    Within G u w (R + S) :=
  bounded_mono_distance (G.dist_triangle u v w) (bounded_add huv hvw)

theorem within_self (G : Graph V) (v : V) {R : ℝ} (hR : 0 ≤ R) :
    Within G v v R := ⟨0, G.dist_self v, by simpa using hR⟩

theorem within_reverse (G : Graph V) (u v : V) (R : ℝ) :
    Within G.reverse v u R ↔ Within G u v R := by
  simp [Within]

theorem within_restrict (G : Graph V) (S : Set V) [Fintype S]
    {u v : S} {R : ℝ} (h : Within (G.restrict S) u v R) :
    Within G u.val v.val R :=
  bounded_mono_distance (G.dist_restrict_le S u v) h

theorem dist_head_mem_le (G : Graph V) (u : V) (xs : List V) {v : V}
    (hv : v ∈ u :: xs) : G.dist u v ≤ G.pathCost (u :: xs) := by
  induction xs generalizing u with
  | nil =>
      have he : v = u := by simpa using hv
      simp [he]
  | cons x xs ih =>
      rcases List.mem_cons.mp hv with rfl | hv
      · simp
      · exact (G.dist_triangle u x v).trans
          (add_le_add (G.dist_le_edge u x) (ih x hv))

theorem dist_get_le_cost (G : Graph V) (xs : List V)
    (i j : Fin xs.length) (hij : i ≤ j) :
    G.dist (xs.get i) (xs.get j) ≤ G.pathCost xs := by
  induction xs with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
      revert j
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j _
        simpa using dist_head_mem_le G x xs (List.get_mem (x :: xs) j)
      · intro j
        refine Fin.cases ?_ (fun j hij => ?_) j
        · intro h
          simp at h
        · exact (ih i j (by simpa using hij)).trans (G.pathCost_tail_le x xs)

/-- The data are an actual finite walk and its finite cost, not pairwise
reachability assumptions. Simplicity is unnecessary for the local lemmas. -/
structure ShortPath (G : Graph V) (D : ℝ) where
  vertices : List V
  nonempty : vertices ≠ []
  cost : ℕ
  cost_eq : G.pathCost vertices = cost
  cost_le : (cost : ℝ) ≤ D

namespace ShortPath

variable {G : Graph V} {D : ℝ}

def size (Q : ShortPath G D) : ℕ := Q.vertices.length

def vertex (Q : ShortPath G D) (i : Fin Q.size) : V := Q.vertices.get i

omit [Fintype V] in
theorem size_pos (Q : ShortPath G D) : 0 < Q.size :=
  List.length_pos_iff.mpr Q.nonempty

theorem forward (Q : ShortPath G D) {i j : Fin Q.size} (hij : i ≤ j) :
    Within G (Q.vertex i) (Q.vertex j) D := by
  apply bounded_mono_distance (dist_get_le_cost G Q.vertices i j hij)
  exact ⟨Q.cost, Q.cost_eq, Q.cost_le⟩

omit [Fintype V] in
theorem scale_nonneg (Q : ShortPath G D) : 0 ≤ D :=
  (Nat.cast_nonneg Q.cost).trans Q.cost_le

end ShortPath

def bothBall (G : Graph V) (p : V) (R : ℝ) : Finset V :=
  Finset.univ.filter fun v => Within G p v R ∨ Within G v p R

def fringe (G : Graph V) (p : V) (rho D : ℝ) : Finset V :=
  bothBall G p (rho + D) \ bothBall G p (rho - D)

@[simp] theorem mem_bothBall (G : Graph V) (p v : V) (R : ℝ) :
    v ∈ bothBall G p R ↔ Within G p v R ∨ Within G v p R := by
  simp [bothBall]

@[simp] theorem mem_fringe (G : Graph V) (p v : V) (rho D : ℝ) :
    v ∈ fringe G p rho D ↔
      (Within G p v (rho + D) ∨ Within G v p (rho + D)) ∧
      ¬ (Within G p v (rho - D) ∨ Within G v p (rho - D)) := by
  simp [fringe]

def labels (G : Graph V) (P : Finset V) (rho : V → ℝ) (v : V) :
    Finset V × Finset V :=
  (P.filter fun p => Within G v p (rho p),
   P.filter fun p => Within G p v (rho p))

def remaining (G : Graph V) (P : Finset V) (rho : V → ℝ) (v : V) : Prop :=
  ∀ p ∈ P, ¬ (Within G v p (rho p) ∧ Within G p v (rho p))

def coreClass (G : Graph V) (P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) : Set V :=
  {v | remaining G P rho v ∧ labels G P rho v = L}

def Bridge {G : Graph V} {D : ℝ} (Q : ShortPath G D) (p : V) (R : ℝ) : Prop :=
  (∃ i : Fin Q.size, Within G p (Q.vertex i) R) ∧
  (∃ i : Fin Q.size, Within G (Q.vertex i) p R)

theorem no_bridge_remaining {G : Graph V} {D R : ℝ}
    (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ)
    (hrho : ∀ p ∈ P, rho p ≤ R) (hnb : ∀ p ∈ P, ¬ Bridge Q p R)
    (i : Fin Q.size) : remaining G P rho (Q.vertex i) := by
  intro p hp h
  exact hnb p hp ⟨⟨i, within_mono h.2 (hrho p hp)⟩,
    ⟨i, within_mono h.1 (hrho p hp)⟩⟩

end

end StreamingReachability.Early
