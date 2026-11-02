module

public import StreamingReachability.Late.Choice
public import StreamingReachability.Late.Geometry

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical
open Early Implicit

noncomputable section

variable {n : ℕ} {R : Representation n} {G H : Graph (Fin n)}
variable {S : Finset (Fin n)} {p u v : Fin n}

theorem restricted_incident_top (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (u v : Fin n) (hout : ¬ (u ∈ S ∧ v ∈ S)) :
    R.restricted G S u v = ⊤ := by
  have hblock (B : Finset (Fin n)) :
      closure (induced (R.base G) S) (B ∩ S) u v = ⊤ := by
    have hn : ¬ (u ∈ B ∩ S ∧ v ∈ B ∩ S ∧ u ≠ v) := by
      intro h
      exact hout ⟨(Finset.mem_inter.mp h.1).2, (Finset.mem_inter.mp h.2.1).2⟩
    simp only [Implicit.closure, ite_eq_right hn]
  have hall (Bs : List (Finset (Fin n))) :
      closures (induced (R.base G) S) (Bs.map (· ∩ S)) u v = ⊤ := by
    induction Bs with
    | nil => simp [closures, induced, hout]
    | cons B Bs ih => simp only [List.map_cons, closures, Graph.union_apply, hblock, ih, min_self]
  exact hall R.blocks

theorem search_induced (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (A : ℕ) :
    induced (rounded A (R.restricted G S)) S = rounded A (R.restricted G S) := by
  funext u v
  by_cases hin : u ∈ S ∧ v ∈ S
  · simp [induced, hin]
  · simp [induced, hin, rounded, restricted_incident_top R G S u v hin]

theorem within_mem_of_induced (H : Graph (Fin n)) (S : Finset (Fin n))
    (hH : induced H S = H) {p v : Fin n} (hp : p ∈ S) {radius : ℝ}
    (h : Within H p v radius) : v ∈ S := by
  obtain ⟨d, hd, _⟩ := h
  have hf : H.dist p v ≠ ⊤ := by simp [hd]
  obtain ⟨xs, _, he, _, hc⟩ := H.exists_dist_path hf
  have hcost : (induced H S).pathCost xs ≠ ⊤ := by rwa [hH, hc]
  obtain ⟨q, qs, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty he)
  have hq : q = p := by simpa [Graph.Endpoints] using he.1
  subst q
  exact induced_path_members H S p qs hp hcost v (endpoints_mem he).2

theorem bothBall_subset_of_induced (H : Graph (Fin n)) (S : Finset (Fin n))
    (hH : induced H S = H) {p : Fin n} (hp : p ∈ S) (radius : ℝ) :
    Early.bothBall H p radius ⊆ S := by
  have hrev : induced H.reverse S = H.reverse := by
    funext u v
    have h := congrFun (congrFun hH v) u
    simpa [induced, Graph.reverse, and_comm] using h
  intro v hv
  rcases (mem_bothBall _ _ _ _).mp hv with h | h
  · exact within_mem_of_induced H S hH hp h
  · exact within_mem_of_induced H.reverse S hrev hp ((within_reverse H v p radius).mpr h)

theorem withinFraction_iff_bounded (d : Distance) (num den : ℕ) (hden : 0 < den) :
    Hopset.withinFraction d num den = true ↔ Bounded d ((num : ℝ) / den) := by
  have hden' : (0 : ℝ) < den := by exact_mod_cast hden
  induction d using WithTop.recTopCoe with
  | top => simp [Hopset.withinFraction, Bounded]
  | coe q =>
      simp only [Hopset.withinFraction, decide_eq_true_eq]
      constructor
      · intro h
        have hn : q ≤ num / den := WithTop.coe_le_coe.mp h
        have hm := (Nat.le_div_iff_mul_le hden).mp hn
        exact ⟨q, rfl, (le_div_iff₀ hden').mpr (by exact_mod_cast hm)⟩
      · rintro ⟨q', he, h⟩
        have hq : q' = q := WithTop.coe_eq_coe.mp he.symm
        subst q'
        apply WithTop.coe_le_coe.mpr
        apply (Nat.le_div_iff_mul_le hden).mpr
        exact_mod_cast (le_div_iff₀ hden').mp h

theorem fraction_radius (cfg : Hopset.Config) (r eta : ℕ) (phi : Fin cfg.shifts) :
    ((((eta * cfg.shifts + phi.val) * cfg.initialNumerator : ℕ) : ℝ) /
      ((cfg.shifts * cfg.denominatorAt r : ℕ) : ℝ)) =
      ((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) := by
  have hN : (cfg.shifts : ℝ) ≠ 0 := by exact_mod_cast cfg.shifts_pos.ne'
  have hd : (cfg.denominatorAt r : ℝ) ≠ 0 := by
    exact_mod_cast (cfg.denominatorAt_pos r).ne'
  simp only [shiftValue, Nat.cast_add, Nat.cast_mul]
  field_simp

theorem actual_bothBall_eq (cfg : Hopset.Config) (r eta : ℕ) (phi : Fin cfg.shifts)
    (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n) (hp : p ∈ S)
    (hH : induced H S = H) (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ)
    (hf : ∀ v ∈ S, Hopset.lookup reply forward v = H.dist p v)
    (hb : ∀ v ∈ S, Hopset.lookup reply backward v = H.dist v p) :
    Hopset.bothBall cfg r eta phi.val S reply forward backward =
      Early.bothBall H p (((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)) := by
  have hden : 0 < cfg.shifts * cfg.denominatorAt r :=
    Nat.mul_pos cfg.shifts_pos (cfg.denominatorAt_pos r)
  ext v
  by_cases hv : v ∈ S
  · simp only [Hopset.bothBall, Finset.mem_filter, hv, true_and, Bool.or_eq_true,
      mem_bothBall, hf v hv, hb v hv]
    simp only [withinFraction_iff_bounded _ _ _ hden, fraction_radius]
    rfl
  · have hn : v ∉ Early.bothBall H p (((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)) :=
      fun h => hv (bothBall_subset_of_induced H S hH hp _ h)
    simp [Hopset.bothBall, hv, hn]

theorem actual_fringe_eq (cfg : Hopset.Config) (r eta : ℕ) (heta : 1 ≤ eta)
    (phi : Fin cfg.shifts) (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n)
    (hp : p ∈ S) (hH : induced H S = H) (reply : Core.BatchAPI.SparseReply n)
    (forward backward : ℕ)
    (hf : ∀ v ∈ S, Hopset.lookup reply forward v = H.dist p v)
    (hb : ∀ v ∈ S, Hopset.lookup reply backward v = H.dist v p) :
    Hopset.fringe cfg r eta phi.val S reply forward backward =
      Early.fringe H p (((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r))
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) := by
  rw [Hopset.fringe,
    actual_bothBall_eq cfg r (eta + 1) phi H S p hp hH reply forward backward hf hb,
    actual_bothBall_eq cfg r (eta - 1) phi H S p hp hH reply forward backward hf hb]
  have hplus : (((eta + 1 : ℕ) : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) =
      ((eta : ℝ) + shiftValue phi) * ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) +
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) := by push_cast; ring
  have hminus : (((eta - 1 : ℕ) : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) =
      ((eta : ℝ) + shiftValue phi) * ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) -
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) := by
    rw [Nat.cast_sub heta]
    push_cast
    ring
  rw [hplus, hminus]
  ext v
  simp only [Early.fringe, Finset.mem_sdiff]

/-- Once actual batch lookups are correct, the exact executable `chooseEta`
equals our radius candidate, including the first-minimum tie breaker. -/
theorem chooseEta_eq_candidate (cfg : Hopset.Config) (r : ℕ) (H : Graph (Fin n))
    (S : Finset (Fin n)) (p : Fin n) (hp : p ∈ S) (hH : induced H S = H)
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ)
    (hf : ∀ v ∈ S, Hopset.lookup reply forward v = H.dist p v)
    (hb : ∀ v ∈ S, Hopset.lookup reply backward v = H.dist v p)
    (sigma : Fin cfg.groups) (phi : Fin cfg.shifts) (hk : 0 < cfg.k) :
    Hopset.chooseEta cfg r S reply forward backward sigma phi =
      cfg.lambda + cfg.width * sigma.val +
        (candidate H ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)
          cfg.k cfg.groups cfg.shifts hk p sigma phi).val := by
  let D : ℝ := (cfg.initialNumerator : ℝ) / cfg.denominatorAt r
  let score := fun j => (Hopset.fringe cfg r (cfg.lambda + cfg.width * sigma.val + j)
    phi.val S reply forward backward).card
  have hscore (j : ℕ) (_hj : j < 4 * cfg.k) :
      shellScore H D cfg.k cfg.groups cfg.shifts p sigma phi j = score j := by
    have heta : 1 ≤ cfg.lambda + cfg.width * sigma.val + j := by
      have h := Nat.mul_pos cfg.width_pos cfg.groups_pos
      change 0 < cfg.lambda at h
      omega
    have hfringe := actual_fringe_eq cfg r (cfg.lambda + cfg.width * sigma.val + j)
      heta phi H S p hp hH reply forward backward hf hb
    dsimp only [score]
    rw [hfringe]
    unfold shellScore
    congr 2
    simp only [Hopset.Config.lambda, Hopset.Config.width, lambda, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    rfl
  have hc := candidate_eq_actual_argmin H D cfg.k cfg.groups cfg.shifts hk p sigma phi
    score hscore
  exact congrArg (fun j => cfg.lambda + cfg.width * sigma.val + j) hc.symm

/-- Accuracy only inside the requested search cap. Sparse replies need not
give the true finite distance to vertices beyond that cap. -/
def AccurateBalls (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n)
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ) (cap : ℝ) : Prop :=
  ∀ v ∈ S, ∀ radius ≤ cap,
    (Bounded (Hopset.lookup reply forward v) radius ↔ Within H p v radius) ∧
    (Bounded (Hopset.lookup reply backward v) radius ↔ Within H v p radius)

def clippedDistance (d : Distance) (cap : ℕ) : Distance :=
  if d ≤ (cap : Distance) then d else ⊤

theorem bounded_clippedDistance (d : Distance) (cap : ℕ) (radius : ℝ)
    (hcap : radius ≤ cap) :
    Bounded (clippedDistance d cap) radius ↔ Bounded d radius := by
  by_cases hd : d ≤ (cap : Distance)
  · simp [clippedDistance, hd]
  · simp only [clippedDistance, ite_eq_right hd]
    constructor
    · rintro ⟨q, hq, _⟩
      simp at hq
    · rintro ⟨q, hq, hr⟩
      apply False.elim
      apply hd
      rw [hq]
      apply WithTop.coe_le_coe.mpr
      exact_mod_cast hr.trans hcap

theorem accurateBalls_of_clipped (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n)
    (reply : Core.BatchAPI.SparseReply n) (forward backward cap : ℕ)
    (hf : ∀ v ∈ S, Hopset.lookup reply forward v = clippedDistance (H.dist p v) cap)
    (hb : ∀ v ∈ S, Hopset.lookup reply backward v = clippedDistance (H.dist v p) cap) :
    AccurateBalls H S p reply forward backward cap := by
  intro v hv radius hr
  rw [hf v hv, hb v hv]
  exact ⟨bounded_clippedDistance _ cap radius hr, bounded_clippedDistance _ cap radius hr⟩

theorem actual_bothBall_eq_of_accurate (cfg : Hopset.Config) (r eta : ℕ)
    (phi : Fin cfg.shifts) (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n)
    (hp : p ∈ S) (hH : induced H S = H) (reply : Core.BatchAPI.SparseReply n)
    (forward backward : ℕ) (cap : ℝ) (ha : AccurateBalls H S p reply forward backward cap)
    (hradius : ((eta : ℝ) + shiftValue phi) *
      ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) ≤ cap) :
    Hopset.bothBall cfg r eta phi.val S reply forward backward =
      Early.bothBall H p (((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)) := by
  have hden : 0 < cfg.shifts * cfg.denominatorAt r :=
    Nat.mul_pos cfg.shifts_pos (cfg.denominatorAt_pos r)
  ext v
  by_cases hv : v ∈ S
  · have h := ha v hv _ hradius
    simp only [Hopset.bothBall, Finset.mem_filter, hv, true_and, Bool.or_eq_true,
      mem_bothBall, withinFraction_iff_bounded _ _ _ hden, fraction_radius]
    exact or_congr h.1 h.2
  · have hn : v ∉ Early.bothBall H p (((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)) :=
      fun h => hv (bothBall_subset_of_induced H S hH hp _ h)
    simp [Hopset.bothBall, hv, hn]

theorem actual_fringe_eq_of_accurate (cfg : Hopset.Config) (r eta : ℕ) (heta : 1 ≤ eta)
    (phi : Fin cfg.shifts) (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n)
    (hp : p ∈ S) (hH : induced H S = H) (reply : Core.BatchAPI.SparseReply n)
    (forward backward : ℕ) (cap : ℝ) (ha : AccurateBalls H S p reply forward backward cap)
    (houter : (((eta + 1 : ℕ) : ℝ) + shiftValue phi) *
      ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) ≤ cap) :
    Hopset.fringe cfg r eta phi.val S reply forward backward =
      Early.fringe H p (((eta : ℝ) + shiftValue phi) *
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r))
        ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) := by
  let D : ℝ := (cfg.initialNumerator : ℝ) / cfg.denominatorAt r
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hplus : (((eta + 1 : ℕ) : ℝ) + shiftValue phi) * D =
      ((eta : ℝ) + shiftValue phi) * D + D := by push_cast; ring
  have hminus : (((eta - 1 : ℕ) : ℝ) + shiftValue phi) * D =
      ((eta : ℝ) + shiftValue phi) * D - D := by
    rw [Nat.cast_sub heta]
    push_cast
    ring
  have hinner : (((eta - 1 : ℕ) : ℝ) + shiftValue phi) * D ≤ cap := by
    change (((eta + 1 : ℕ) : ℝ) + shiftValue phi) * D ≤ cap at houter
    rw [hplus] at houter
    rw [hminus]
    linarith
  rw [Hopset.fringe,
    actual_bothBall_eq_of_accurate cfg r (eta + 1) phi H S p hp hH reply forward backward
      cap ha houter,
    actual_bothBall_eq_of_accurate cfg r (eta - 1) phi H S p hp hH reply forward backward
      cap ha hinner]
  change Early.bothBall H p _ \ Early.bothBall H p _ =
    Early.fringe H p (((eta : ℝ) + shiftValue phi) * D) D
  rw [hplus, hminus]
  ext v
  simp only [Early.fringe, Finset.mem_sdiff]

theorem chooseEta_eq_candidate_of_accurate (cfg : Hopset.Config) (r : ℕ)
    (H : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n) (hp : p ∈ S)
    (hH : induced H S = H) (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ)
    (cap : ℝ) (ha : AccurateBalls H S p reply forward backward cap)
    (hD : 0 < (cfg.initialNumerator : ℝ) / cfg.denominatorAt r)
    (hcap : searchRadius cfg.k cfg.groups
      ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) ≤ cap)
    (sigma : Fin cfg.groups) (phi : Fin cfg.shifts) (hk : 0 < cfg.k) :
    Hopset.chooseEta cfg r S reply forward backward sigma phi =
      cfg.lambda + cfg.width * sigma.val +
        (candidate H ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r)
          cfg.k cfg.groups cfg.shifts hk p sigma phi).val := by
  let D : ℝ := (cfg.initialNumerator : ℝ) / cfg.denominatorAt r
  let score := fun j => (Hopset.fringe cfg r (cfg.lambda + cfg.width * sigma.val + j)
    phi.val S reply forward backward).card
  have hscore (j : ℕ) (hj : j < 4 * cfg.k) :
      shellScore H D cfg.k cfg.groups cfg.shifts p sigma phi j = score j := by
    let eta := cfg.lambda + cfg.width * sigma.val + j
    have heta : 1 ≤ eta := by
      have h := Nat.mul_pos cfg.width_pos cfg.groups_pos
      change 0 < cfg.lambda at h
      dsimp [eta]
      omega
    have hradius : (((eta + 1 : ℕ) : ℝ) + shiftValue phi) * D =
        candidateRadius (lambda cfg.k cfg.groups) (4 * cfg.k) sigma ⟨j, hj⟩
          (shiftValue phi) D + D := by
      simp only [eta, Hopset.Config.lambda, Hopset.Config.width, lambda, candidateRadius,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hr := (early_candidate_bounds cfg.k cfg.groups cfg.shifts hk hD sigma phi ⟨j, hj⟩).2
    have houter : (((eta + 1 : ℕ) : ℝ) + shiftValue phi) * D ≤ cap := by
      rw [hradius]
      have hm : nearRadius cfg.k cfg.groups D + D ≤ searchRadius cfg.k cfg.groups D := by
        unfold nearRadius searchRadius
        nlinarith
      exact (by linarith : _ ≤ nearRadius cfg.k cfg.groups D + D).trans (hm.trans hcap)
    have hfringe := actual_fringe_eq_of_accurate cfg r eta heta phi H S p hp hH reply
      forward backward cap ha houter
    dsimp only [score]
    rw [hfringe]
    unfold shellScore
    congr 2
    simp only [eta, Hopset.Config.lambda, Hopset.Config.width, lambda, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat]
    rfl
  have hc := candidate_eq_actual_argmin H D cfg.k cfg.groups cfg.shifts hk p sigma phi
    score hscore
  exact congrArg (fun j => cfg.lambda + cfg.width * sigma.val + j) hc.symm

end

end StreamingReachability.Late
