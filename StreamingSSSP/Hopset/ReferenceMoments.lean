module

public import StreamingSSSP.Hopset.ReferenceFacts
public import StreamingSSSP.Hopset.FringeProbability
public import StreamingSSSP.Hopset.CopyMoments

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators
open Early

noncomputable section

variable {n : ℕ}

theorem radius_grid (G : Graph (Fin n)) (D : ℝ) (cfg : Config)
    (p : Fin n) (z : Fin cfg.groups × Fin cfg.shifts) :
    Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos p z =
      lambda cfg.k cfg.groups * D + (D / cfg.shifts) *
        Shifts.pointIndex (4 * cfg.k) cfg.groups cfg.shifts
          (Late.candidate G D cfg.k cfg.groups cfg.shifts cfg.k_pos p) z.1 z.2 := by
  have hN : (cfg.shifts : ℝ) ≠ 0 := by exact_mod_cast cfg.shifts_pos.ne'
  simp only [Late.radius, candidateRadius, shiftValue, Shifts.pointIndex,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hN]
  ring

theorem owner_fringe_probability (G : Graph (Fin n)) (cfg : Config)
    (hnum : 0 < cfg.initialNumerator) (r : ℕ) (p v : Fin n) :
    (ownerLaw n cfg).prob (fun owners =>
      v ∈ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ≤ 4 / cfg.groups := by
  let D := distanceScale cfg r
  let inside := fun z : Fin cfg.groups × Fin cfg.shifts =>
    v ∈ Early.fringe G p (Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos p z) D
  have hmarginal :
      (ownerLaw n cfg).prob (fun owners =>
        v ∈ Early.fringe G p (radii cfg r G owners p) D) =
        (Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos).prob inside :=
    Law.family_marginal_probability n
      (fun _ => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos) p inside
  rw [hmarginal]
  have h := fringe_probability G p v (4 * cfg.k) cfg.groups cfg.shifts (by have := cfg.k_pos; omega)
    cfg.groups_pos cfg.shifts_pos (Late.candidate G D cfg.k cfg.groups cfg.shifts cfg.k_pos p)
    (lambda cfg.k cfg.groups * D) D (distanceScale_pos cfg hnum r)
  have he : inside = fun z =>
      v ∈ Early.fringe G p
        (lambda cfg.k cfg.groups * D + (D / cfg.shifts) *
          Shifts.pointIndex (4 * cfg.k) cfg.groups cfg.shifts
            (Late.candidate G D cfg.k cfg.groups cfg.shifts cfg.k_pos p) z.1 z.2) D := by
    funext z
    simp only [inside, radius_grid]
  rw [he]
  exact h

theorem fringe_center_near (G : Graph (Fin n)) (cfg : Config)
    (hnum : 0 < cfg.initialNumerator) (r : ℕ) (owners : Owners n cfg)
    (p v : Fin n) (hv : v ∈ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) :
    p ∈ Early.bothBall G v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r)) := by
  let D := distanceScale cfg r
  have hD := distanceScale_pos cfg hnum r
  have hupper := (Late.radius_bounds G D cfg.k cfg.groups cfg.shifts cfg.k_pos hD p (owners p)).2
  have houter : radii cfg r G owners p + D ≤ Early.searchRadius cfg.k cfg.groups D := by
    unfold nearRadius at hupper
    unfold Early.searchRadius
    change Late.radius G D cfg.k cfg.groups cfg.shifts cfg.k_pos p (owners p) + D ≤ _
    linarith
  have hboth := (Early.mem_fringe G p v _ D).mp hv |>.1
  apply (Early.mem_bothBall G v p _).mpr
  rcases hboth with h | h
  · exact Or.inr (Early.within_mono h houter)
  · exact Or.inl (Early.within_mono h houter)

theorem radii_outer_le_search (G : Graph (Fin n)) (cfg : Config)
    (hnum : 0 < cfg.initialNumerator) (r : ℕ) (owners : Owners n cfg) (p : Fin n) :
    radii cfg r G owners p + distanceScale cfg r ≤
      Early.searchRadius cfg.k cfg.groups (distanceScale cfg r) := by
  have hD := distanceScale_pos cfg hnum r
  have hupper := (Late.radius_bounds G (distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos
    hD p (owners p)).2
  unfold nearRadius at hupper
  unfold Early.searchRadius
  change Late.radius G (distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos p (owners p) +
    distanceScale cfg r ≤ _
  linarith

theorem selected_fringe_bound (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (cfg : Config)
    (hnum : 0 < cfg.initialNumerator) (r : ℕ) (hr : r < ps.length)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (p v : Fin n) (hpS : p ∈ S) :
    ((CopyHistory.law ps history).bind fun ranks =>
      (ownerLaw n cfg).map fun owners =>
        if ranks p = r ∧ v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
        then (1 : ℝ) else 0).expect id ≤
      (Ranks.rate ps r).value * (4 / cfg.groups) := by
  have hinside : (ownerLaw n cfg).prob (fun owners =>
      v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ≤ 4 / cfg.groups := by
    apply (Law.prob_mono _ ?_).trans (owner_fringe_probability G cfg hnum r p v)
    intro owners h
    exact (Finset.mem_inter.mp h).2
  have hbound := CopyHistory.expected_selected_fringe_le ps history S p hpS r hr hc hp hs
    (ownerLaw n cfg)
    (fun owners => v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r))
    (4 / cfg.groups) hinside
  convert hbound using 1
  rw [Law.expect_bind, Law.expect_bind]
  congr 1
  funext ranks
  rw [Law.expect_map, Law.expect_map]
  congr 1
  funext owners
  by_cases h : ranks p = r ∧
      v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r) <;> simp [h]

def fringeCount (G : Graph (Fin n)) (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (v : Fin n) (ranks : Fin n → ℕ) (owners : Owners n cfg) : ℝ :=
  ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
    (distanceScale cfg r)).map fun T => if v ∈ T then (1 : ℝ) else 0).sum

theorem fringeCount_eq (G : Graph (Fin n)) (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (v : Fin n) (ranks : Fin n → ℕ) (owners : Owners n cfg) :
    fringeCount G cfg r S v ranks owners =
      ∑ p ∈ S, if ranks p = r ∧
        v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
        then (1 : ℝ) else 0 := by
  let P := CopyHistory.pivots S r ranks
  let f := fun p => if v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
    then (1 : ℝ) else 0
  have hsum : ((members P).map f).sum = ∑ p ∈ P, f p := by
    have h := List.sum_toFinset f (members_nodup P)
    rw [members_toFinset] at h
    exact h.symm
  dsimp only [fringeCount, Geometry.fringes]
  simp only [List.map_map, Function.comp_def]
  change ((members P).map f).sum = _
  rw [hsum]
  dsimp only [P, CopyHistory.pivots]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ranks p = r <;> simp [f, hp]

theorem fringeCount_mixed_mean (mu : Law (Fin n → ℕ)) (G : Graph (Fin n)) (cfg : Config)
    (r : ℕ) (S : Finset (Fin n)) (v : Fin n) :
    mu.expect (fun ranks => (ownerLaw n cfg).expect (fringeCount G cfg r S v ranks)) =
      ∑ p ∈ S, (mu.bind fun ranks => (ownerLaw n cfg).map fun owners =>
        if ranks p = r ∧
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
        then (1 : ℝ) else 0).expect id := by
  have he (ranks : Fin n → ℕ) :
      (ownerLaw n cfg).expect (fringeCount G cfg r S v ranks) =
        ∑ p ∈ S, (ownerLaw n cfg).expect (fun owners =>
          if ranks p = r ∧
            v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
          then (1 : ℝ) else 0) := by
    have hfn : fringeCount G cfg r S v ranks = fun owners => ∑ p ∈ S,
        if ranks p = r ∧
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
        then (1 : ℝ) else 0 :=
      funext (fun owners => fringeCount_eq G cfg r S v ranks owners)
    rw [hfn, Law.expect_finset_sum]
  simp_rw [he]
  rw [Law.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Law.expect_bind]
  simp_rw [Law.expect_map]
  rfl

theorem expected_fringe_count (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (cfg : Config)
    (hnum : 0 < cfg.initialNumerator) (r : ℕ) (hr : r < ps.length)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (v : Fin n) (b : ℕ)
    (hin : (searchIn G v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b)
    (hout : (searchOut G v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b) :
    (CopyHistory.law ps history).expect
        (fun ranks => (ownerLaw n cfg).expect (fringeCount G cfg r S v ranks)) ≤
      8 * (b : ℝ) * (Ranks.rate ps r).value / cfg.groups := by
  let mu := CopyHistory.law ps history
  let nu := ownerLaw n cfg
  let A := S ∩ Early.bothBall G v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))
  let f : Fin n → ℝ := fun p => mu.expect fun ranks => nu.expect fun owners =>
    if ranks p = r ∧
      v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
    then 1 else 0
  have he (ranks : Fin n → ℕ) :
      nu.expect (fringeCount G cfg r S v ranks) = ∑ p ∈ S, nu.expect (fun owners =>
        if ranks p = r ∧
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
        then 1 else 0) := by
    have hfn : fringeCount G cfg r S v ranks = fun owners => ∑ p ∈ S,
        if ranks p = r ∧
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
        then (1 : ℝ) else 0 :=
      funext (fun owners => fringeCount_eq G cfg r S v ranks owners)
    rw [hfn, Law.expect_finset_sum]
  change mu.expect (fun ranks => nu.expect (fringeCount G cfg r S v ranks)) ≤ _
  simp_rw [he]
  rw [Law.expect_finset_sum]
  change (∑ p ∈ S, f p) ≤ _
  have hzero (p : Fin n) (hpS : p ∈ S) (hpA : p ∉ A) : f p = 0 := by
    have hfalse (ranks : Fin n → ℕ) (owners : Owners n cfg) :
        ¬ (ranks p = r ∧
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) := by
      rintro ⟨_, hv⟩
      apply hpA
      exact Finset.mem_inter.mpr ⟨hpS,
        fringe_center_near G cfg hnum r owners p v (Finset.mem_inter.mp hv).2⟩
    simp only [f, hfalse, ↓reduceIte, Law.expect_const]
  rw [← Finset.sum_subset (Finset.inter_subset_left : A ⊆ S) hzero]
  have hC : 0 ≤ (Ranks.rate ps r).value * (4 / (cfg.groups : ℝ)) :=
    mul_nonneg (Ranks.rate ps r).value_nonneg (by positivity)
  have hcard : (A.card : ℝ) ≤ 2 * b := by
    have h := (Finset.card_le_card (Finset.inter_subset_right : A ⊆ _)).trans
      (bothBall_card_le G v _)
    exact_mod_cast h.trans (by omega : _ ≤ 2 * b)
  calc
    _ ≤ ∑ _p ∈ A, (Ranks.rate ps r).value * (4 / cfg.groups) := by
      apply Finset.sum_le_sum
      intro p hpA
      have h := selected_fringe_bound ps history S G cfg hnum r hr hc hp hs p v
        (Finset.mem_inter.mp hpA).1
      simpa only [Law.expect_bind, Law.expect_map, id_eq] using h
    _ = (A.card : ℝ) * ((Ranks.rate ps r).value * (4 / cfg.groups)) := by simp
    _ ≤ (2 * b) * ((Ranks.rate ps r).value * (4 / cfg.groups)) :=
      mul_le_mul_of_nonneg_right hcard hC
    _ = _ := by ring

end

end StreamingSSSP.Hopset.Reference
