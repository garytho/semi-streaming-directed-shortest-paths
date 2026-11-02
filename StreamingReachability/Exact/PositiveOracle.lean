module

public import StreamingReachability.Exact.Smoothing

@[expose] public section

namespace StreamingReachability.Exact

open scoped Classical

variable {V : Type*}

def affineGraph (G : Graph V) (scale offset : ℕ) : Graph V :=
  mapWeights G (fun w => scale * w + offset)

theorem mapWeights_ne_top (G : Graph V) (f : ℕ → ℕ) (u v : V) :
    mapWeights G f u v ≠ ⊤ ↔ G u v ≠ ⊤ := by
  by_cases h : G u v = ⊤
  · simp [h]
  · lift G u v to ℕ using h with w hw
    simp [mapWeights, ← hw]

theorem affine_path_finite (G : Graph V) (scale offset : ℕ) (xs : List V) :
    (affineGraph G scale offset).pathCost xs ≠ ⊤ ↔ G.pathCost xs ≠ ⊤ := by
  rw [Graph.pathCost_ne_top_iff, Graph.pathCost_ne_top_iff]
  exact List.IsChain.iff (fun u v => mapWeights_ne_top G _ u v)

theorem affine_pathCost (G : Graph V) (scale offset : ℕ)
    (xs : List V) (c : ℕ) (hc : G.pathCost xs = c) :
    (affineGraph G scale offset).pathCost xs =
      ((scale * c + offset * (xs.length - 1) : ℕ) : Distance) := by
  induction xs generalizing c with
  | nil =>
      have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
      simp [hc0]
  | cons u xs ih =>
      cases xs with
      | nil =>
          have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
          simp [hc0]
      | cons v xs =>
          obtain ⟨a, b, ha, hb, hab⟩ := finite_add hc
          have ht := ih b hb
          simp only [Graph.pathCost_cons_cons]
          rw [show affineGraph G scale offset u v =
            ((scale * a + offset : ℕ) : Distance) by simp [affineGraph, ha], ht]
          calc
            ((scale * a + offset : ℕ) : Distance) +
                ((scale * b + offset * ((v :: xs).length - 1) : ℕ) : Distance) =
                ((scale * a + offset + (scale * b + offset * ((v :: xs).length - 1)) : ℕ) :
                  Distance) := (Nat.cast_add _ _).symm
            _ = _ := by
              apply congrArg (fun n : ℕ => (n : Distance))
              simp only [List.length_cons, Nat.add_sub_cancel]
              rw [← hab]
              ring

theorem affine_dist_bounds [Fintype V] (G : Graph V) (scale offset : ℕ)
    {s v : V} {d : ℕ} (hd : G.dist s v = d) :
    ∃ e : ℕ, (affineGraph G scale offset).dist s v = e ∧
      scale * d ≤ e ∧ e ≤ scale * d + offset * (Fintype.card V - 1) := by
  obtain ⟨xs, _, he, hlen, hc⟩ := G.exists_dist_path (s := s) (t := v) (by simp [hd])
  have hcx : G.pathCost xs = d := hc.trans hd
  have hupper : (affineGraph G scale offset).dist s v ≤
      ((scale * d + offset * (Fintype.card V - 1) : ℕ) : Distance) := by
    have hp := (affineGraph G scale offset).dist_le_pathCost he
    rw [affine_pathCost G scale offset xs d hcx] at hp
    exact hp.trans (WithTop.coe_le_coe.mpr (by gcongr))
  obtain ⟨e, heq, hele⟩ := finite_of_le hupper
  refine ⟨e, heq, ?_, hele⟩
  obtain ⟨ys, _, hey, _, hcy⟩ :=
    (affineGraph G scale offset).exists_dist_path (s := s) (t := v) (by simp [heq])
  have hfinite : G.pathCost ys ≠ ⊤ := by
    apply (affine_path_finite G scale offset ys).mp
    simp [hcy, heq]
  lift G.pathCost ys to ℕ using hfinite with c hcost
  have horig : d ≤ c := WithTop.coe_le_coe.mp (by simpa [hd, ← hcost] using G.dist_le_pathCost hey)
  have ha := affine_pathCost G scale offset ys c hcost.symm
  have hnum : scale * c + offset * (ys.length - 1) = e := by
    apply WithTop.coe_eq_coe.mp
    exact ha.symm.trans (hcy.trans heq)
  nlinarith [Nat.mul_le_mul_left scale horig]

def positiveAnswer (n denominator : ℕ) (answer : V → ℕ) : V → ℕ :=
  fun v =>
    let theta := 3 * n * denominator
    if answer v < theta then 0 else answer v / theta

theorem positive_oracle_numeric (n k d e answer : ℕ)
    (hn : 0 < n) (hk : 0 < k)
    (hlower : (3 * n * k) * d ≤ e)
    (hupper : e < (3 * n * k) * d + n)
    (ha : e ≤ answer)
    (hacc : (3 * k) * answer ≤ (3 * k + 1) * e) :
    let out := if answer < 3 * n * k then 0 else answer / (3 * n * k)
    d ≤ out ∧ k * out ≤ (k + 1) * d := by
  let theta := 3 * n * k
  have ht : 0 < theta := by dsimp [theta]; positivity
  change theta * d ≤ e at hlower
  change e < theta * d + n at hupper
  change d ≤ (if answer < theta then 0 else answer / theta) ∧
    k * (if answer < theta then 0 else answer / theta) ≤ (k + 1) * d
  by_cases hd : d = 0
  · subst d
    have he : e < n := by simpa using hupper
    have hans : answer < theta := by
      have hstrict : (3 * k) * answer < (3 * k + 1) * n :=
        hacc.trans_lt (Nat.mul_lt_mul_of_pos_left he (by omega))
      have hk1 : 1 ≤ k := hk
      have htheta : 3 * n ≤ theta := by dsimp [theta]; nlinarith
      nlinarith
    simp [hans]
  · have hd1 : 1 ≤ d := by omega
    have hans : ¬answer < theta := by nlinarith
    rw [if_neg hans]
    have hlowout : d ≤ answer / theta := by
      apply (Nat.le_div_iff_mul_le ht).2
      nlinarith
    have hextra : (3 * k + 1) * n ≤ 2 * theta * d := by
      have htheta : (3 * k + 1) * n ≤ 2 * theta := by
        dsimp [theta]
        nlinarith
      exact htheta.trans (by nlinarith)
    have heweak : e ≤ theta * d + n := Nat.le_of_lt hupper
    have hb : (3 * k) * answer ≤ (3 * k + 1) * (theta * d + n) :=
      hacc.trans (Nat.mul_le_mul_left _ heweak)
    have hfinal : k * answer ≤ (k + 1) * theta * d := by nlinarith
    have hfloor : theta * (answer / theta) ≤ answer := by
      exact Nat.mul_div_le _ _
    constructor
    · exact hlowout
    · nlinarith

theorem positive_oracle [Fintype V] (G : Graph V) (s : V) (k : ℕ)
    (hk : 0 < k) (answer : V → ℕ)
    (hanswer : IntegerApprox (affineGraph G (3 * Fintype.card V * k) 1) s (3 * k) answer) :
    IntegerApprox G s k (positiveAnswer (Fintype.card V) k answer) := by
  intro v d hd
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨s⟩
  obtain ⟨e, he, hl, hu⟩ := affine_dist_bounds G (3 * Fintype.card V * k) 1 hd
  have hu' : e < (3 * Fintype.card V * k) * d + Fintype.card V := by omega
  have ha := hanswer v e he
  exact positive_oracle_numeric _ _ _ _ _ hn hk hl hu' ha.1 ha.2

end StreamingReachability.Exact
