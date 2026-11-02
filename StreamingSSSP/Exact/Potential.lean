module

public import StreamingSSSP.Exact.Rounding

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*}

def Feasible (G : Graph V) (potential : V → ℕ) : Prop :=
  ∀ u v (w : ℕ), G u v = w → potential v ≤ potential u + w

def reweight (G : Graph V) (potential : V → ℕ) : Graph V :=
  fun u v => WithTop.map (fun (w : ℕ) => (w + potential u - potential v : ℕ)) (G u v)

theorem reweight_coe (G : Graph V) (potential : V → ℕ)
    {u v : V} {w : ℕ} (h : G u v = w) :
    reweight G potential u v = ((w + potential u - potential v : ℕ) : Distance) := by
  unfold reweight
  rw [h]
  rfl

theorem reweight_path_finite (G : Graph V) (potential : V → ℕ) (xs : List V) :
    (reweight G potential).pathCost xs ≠ ⊤ ↔ G.pathCost xs ≠ ⊤ := by
  rw [Graph.pathCost_ne_top_iff, Graph.pathCost_ne_top_iff]
  exact List.IsChain.iff (fun u v => mapWeights_ne_top G _ u v)

theorem reweight_pathCost (G : Graph V) (potential : V → ℕ)
    (hfeasible : Feasible G potential) {xs : List V} {s t : V} {c : ℕ}
    (he : Graph.Endpoints xs s t) (hc : G.pathCost xs = c) :
    ∃ r : ℕ, (reweight G potential).pathCost xs = r ∧
      r + potential t = c + potential s := by
  induction xs generalizing s c with
  | nil => simp [Graph.Endpoints] at he
  | cons u xs ih =>
      have hu : u = s := by simpa [Graph.Endpoints] using he.1
      subst u
      cases xs with
      | nil =>
          have ht : s = t := by simpa [Graph.Endpoints] using he.2
          have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
          subst t
          exact ⟨0, rfl, by simp [hc0]⟩
      | cons v xs =>
          obtain ⟨a, b, ha, hb, hab⟩ := finite_add hc
          have he' : Graph.Endpoints (v :: xs) v t :=
            ⟨rfl, by simpa [Graph.Endpoints] using he.2⟩
          obtain ⟨r, hr, hrt⟩ := ih he' hb
          have hf := hfeasible s v a ha
          let edgeCost := a + potential s - potential v
          have hec : edgeCost + potential v = a + potential s := by dsimp [edgeCost]; omega
          refine ⟨edgeCost + r, ?_, ?_⟩
          · simp only [Graph.pathCost_cons_cons]
            rw [reweight_coe G potential ha, hr]
            exact (Nat.cast_add _ _).symm
          · omega

theorem reweight_dist [Fintype V] (G : Graph V) (potential : V → ℕ)
    (hfeasible : Feasible G potential) {s v : V} {d : ℕ}
    (hd : G.dist s v = d) :
    ∃ r : ℕ, (reweight G potential).dist s v = r ∧
      r + potential v = d + potential s := by
  obtain ⟨xs, _, he, _, hc⟩ := G.exists_dist_path (s := s) (t := v) (by simp [hd])
  obtain ⟨a, ha, hat⟩ := reweight_pathCost G potential hfeasible he (hc.trans hd)
  have hrle : (reweight G potential).dist s v ≤ a := by
    rw [← ha]
    exact (reweight G potential).dist_le_pathCost he
  obtain ⟨r, hr, hra⟩ := finite_of_le hrle
  refine ⟨r, hr, ?_⟩
  obtain ⟨ys, _, hey, _, hcy⟩ :=
    (reweight G potential).exists_dist_path (s := s) (t := v) (by simp [hr])
  have hfinite : G.pathCost ys ≠ ⊤ :=
    (reweight_path_finite G potential ys).mp (by simp [hcy, hr])
  lift G.pathCost ys to ℕ using hfinite with c hcost
  have hdc : d ≤ c := WithTop.coe_le_coe.mp (by simpa [hd, ← hcost] using G.dist_le_pathCost hey)
  obtain ⟨b, hb, hbt⟩ := reweight_pathCost G potential hfeasible hey hcost.symm
  have hbr : b = r := WithTop.coe_eq_coe.mp (hb.symm.trans (hcy.trans hr))
  omega

theorem feasible_le_dist [Fintype V] (G : Graph V) (potential : V → ℕ)
    (hfeasible : Feasible G potential) {s v : V} {d : ℕ}
    (hs : potential s = 0) (hd : G.dist s v = d) : potential v ≤ d := by
  obtain ⟨r, _, he⟩ := reweight_dist G potential hfeasible hd
  omega

theorem feasible_add (G : Graph V) (potential update : V → ℕ)
    (hpotential : Feasible G potential) (hupdate : Feasible (reweight G potential) update) :
    Feasible G (fun v => potential v + update v) := by
  intro u v w hw
  have hp := hpotential u v w hw
  have hq := hupdate u v (w + potential u - potential v) (reweight_coe G potential hw)
  change potential v + update v ≤ potential u + update u + w
  omega

theorem zero_feasible (G : Graph V) : Feasible G (fun _ => 0) := by
  intro u v w _
  simp

@[simp] theorem reweight_zero (G : Graph V) : reweight G (fun _ => 0) = G := by
  funext u v
  by_cases hn : G u v = ⊤
  · simp [reweight, hn]
  · lift G u v to ℕ using hn with w hw
    rw [reweight_coe G _ hw.symm]
    simpa using hw

theorem reweight_add (G : Graph V) (potential update : V → ℕ)
    (hpotential : Feasible G potential) (hupdate : Feasible (reweight G potential) update) :
    reweight G (fun v => potential v + update v) =
      reweight (reweight G potential) update := by
  funext u v
  by_cases hn : G u v = ⊤
  · simp [reweight, hn]
  · lift G u v to ℕ using hn with w hw
    have he := reweight_coe G potential hw.symm
    have hp := hpotential u v w hw.symm
    have hq := hupdate u v _ he
    rw [reweight_coe G _ hw.symm, reweight_coe _ update he]
    apply congrArg (fun x : ℕ => (x : Distance))
    omega

end StreamingSSSP.Exact
