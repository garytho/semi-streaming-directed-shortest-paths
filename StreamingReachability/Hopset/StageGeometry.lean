module

public import StreamingReachability.Hopset.PairStage

@[expose] public section

namespace StreamingReachability.Parameters

theorem ceilDiv_le_iff {a b r : ℕ} (hb : 0 < b) : ceilDiv a b ≤ r ↔ a ≤ b * r :=
  Core.ceilNat_le_iff hb

theorem ceilDiv_comp (a b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    ceilDiv (ceilDiv a b) c = ceilDiv a (b * c) := by
  apply Nat.le_antisymm
  · apply (ceilDiv_le_iff hc).mpr
    apply (ceilDiv_le_iff hb).mpr
    simpa only [Nat.mul_assoc] using le_mul_ceilDiv a (b * c) (by positivity)
  · apply (ceilDiv_le_iff (by positivity : 0 < b * c)).mpr
    have h := Nat.mul_le_mul_left b (le_mul_ceilDiv (ceilDiv a b) c hc)
    exact (le_mul_ceilDiv a b hb).trans (by simpa only [Nat.mul_assoc] using h)

theorem ceilDiv_add_two (a : ℕ) : ceilDiv (a + 2) 2 = ceilDiv a 2 + 1 := by
  have h := Core.ceilNat_add_multiple (A := 2) (by decide) 1 a
  simpa only [ceilDiv, Core.ceilNat, Nat.mul_one, Nat.add_comm] using h

theorem ceilDiv_pow_succ (n i : ℕ) :
    ceilDiv (ceilDiv n (2 ^ i)) 2 = ceilDiv n (2 ^ (i + 1)) := by
  rw [ceilDiv_comp n (2 ^ i) 2 (by positivity) (by decide), pow_succ]

theorem ceilDiv_eq_one {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : ceilDiv a b = 1 := by
  have hp := ceilDiv_pos a b ha hb
  have hl : ceilDiv a b ≤ 1 := (ceilDiv_le_iff hb).mpr (by simpa only [Nat.mul_one] using hab)
  omega

theorem stretch_power_bound (n accuracy : ℕ) (ha : 0 < accuracy) (i : ℕ) (hi : i ≤ ell n) :
    (1 + 2 / (accuracyDenominator n accuracy : ℝ)) ^ i ≤ 1 + 1 / (5 * (accuracy : ℝ)) ∧
      (1 + 2 / (accuracyDenominator n accuracy : ℝ)) ^ i ≤ 2 := by
  let den : ℝ := accuracyDenominator n accuracy
  let eps : ℝ := 2 / den
  have hd : 0 < den := by dsimp only [den]; exact_mod_cast accuracyDenominator_pos n accuracy ha
  have he : (0 : ℝ) < ell n := by exact_mod_cast ell_pos n
  have haR : (1 : ℝ) ≤ accuracy := by exact_mod_cast (show 1 ≤ accuracy from ha)
  have heps : 0 ≤ eps := by dsimp only [eps]; positivity
  have hed : eps * den = 2 := div_mul_cancel₀ _ hd.ne'
  have hlog : 4 * (ell n : ℝ) ≤ den := by
    change 4 * (ell n : ℝ) ≤ ((20 * accuracy * ell n : ℕ) : ℝ)
    push_cast
    have hp := mul_le_mul_of_nonneg_right haR he.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlog heps
  have hbudget : 2 * (ell n : ℝ) * eps ≤ 1 := by nlinarith
  have hind (j : ℕ) (hj : j ≤ ell n) : (1 + eps) ^ j ≤ 1 + 2 * (j : ℝ) * eps := by
    induction j with
    | zero => simp only [pow_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero, le_refl]
    | succ j ih =>
        have hj' : j ≤ ell n := by omega
        have hprev := ih hj'
        have hindex : (j : ℝ) ≤ ell n := by exact_mod_cast hj'
        have hprod := mul_le_mul_of_nonneg_right hindex (show 0 ≤ 2 * eps by positivity)
        have hsmall : 2 * (j : ℝ) * eps ≤ 1 := by nlinarith
        have hsquare := mul_le_mul_of_nonneg_right hsmall heps
        have hgrow := mul_le_mul_of_nonneg_right hprev (show 0 ≤ 1 + eps by linarith)
        rw [pow_succ]
        push_cast
        nlinarith
  have hiR : (i : ℝ) ≤ ell n := by exact_mod_cast hi
  have hindex := mul_le_mul_of_nonneg_right hiR (show 0 ≤ 2 * eps by positivity)
  have heq : 2 * (ell n : ℝ) * eps = 1 / (5 * (accuracy : ℝ)) := by
    dsimp only [eps, den, accuracyDenominator]
    push_cast
    field_simp [he.ne', (by exact_mod_cast ha.ne' : (accuracy : ℝ) ≠ 0)]
    norm_num
  have hmain : (1 + eps) ^ i ≤ 1 + 1 / (5 * (accuracy : ℝ)) := by
    have h := hind i hi
    nlinarith only [h, hindex, heq]
  have hfrac : 1 / (5 * (accuracy : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 5 * (accuracy : ℝ))).mpr
    linarith
  exact ⟨hmain, hmain.trans (by linarith)⟩

end StreamingReachability.Parameters

namespace StreamingReachability.Graph

open scoped Classical

theorem dist_lower_bound {V : Type*} [Fintype V] (G : Graph V) (bound : Distance)
    (hG : ∀ u v, u ≠ v → bound ≤ G u v) {s t : V} (hst : s ≠ t) : bound ≤ G.dist s t := by
  apply (G.le_dist_iff s t bound).mpr
  intro xs he
  obtain ⟨u, tail, rfl⟩ := List.exists_cons_of_ne_nil (endpoints_nonempty he)
  have hu : u = s := by simpa [Endpoints] using he.1
  subst u
  induction tail generalizing s with
  | nil =>
      have heq : s = t := by simpa [Endpoints] using he.2
      exact False.elim (hst heq)
  | cons u tail ih =>
      by_cases hsu : s = u
      · subst s
        have he' : Endpoints (u :: tail) u t := ⟨rfl, by simpa [Endpoints] using he.2⟩
        exact (ih hst he').trans (G.pathCost_tail_le u (u :: tail))
      · exact (hG s u hsu).trans (by
          rw [pathCost_cons_cons]
          exact le_add_of_nonneg_right bot_le)

end StreamingReachability.Graph

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem ShortRoute.mono_hops {F : Graph (Fin n)} {s t : Fin n} {h k : ℕ} {budget : ℝ}
    (route : ShortRoute F s t h budget) (hh : h ≤ k) : ShortRoute F s t k budget := by
  obtain ⟨cost, hc, P, hp⟩ := route
  exact ⟨cost, hc, P, hp.trans hh⟩

theorem ShortRoute.append {F : Graph (Fin n)} {s u t : Fin n} {h k : ℕ} {a b : ℝ}
    (left : ShortRoute F s u h a) (right : ShortRoute F u t k b) :
    ShortRoute F s t (h + k) (a + b) := by
  obtain ⟨c, hc, P, hp⟩ := left
  obtain ⟨d, hd, Q, hq⟩ := right
  exact ⟨c + d, by exact_mod_cast add_le_add hc hd, P.append Q,
    (P.hops_append Q).trans (Nat.add_le_add hp hq)⟩

theorem ShortRoute.hopDist {F : Graph (Fin n)} {s t : Fin n} {h : ℕ} {budget : ℝ}
    (route : ShortRoute F s t h budget) :
    ∃ d : ℕ, F.hopDist h s t = (d : Distance) ∧ (d : ℝ) ≤ budget := by
  obtain ⟨cost, hc, P, hp⟩ := route
  have hlen : P.vertices.length ≤ h + 1 := by unfold Late.Route.hops at hp; omega
  have hd := (F.hopDist_le_pathCost P.endpoints hlen).trans P.cost_le
  obtain ⟨d, he, hdc⟩ := Exact.finite_of_le hd
  have hreal : (d : ℝ) ≤ cost := by exact_mod_cast hdc
  exact ⟨d, he, hreal.trans hc⟩

theorem stage_one_chunk (frozen committed : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hops low high : ℕ) (stretch : ℝ) (hstretch : 0 ≤ stretch)
    (hmin : ∀ u v, u ≠ v → (low : Distance) ≤ frozen.graph (StoredEdges.graphOfEdges input) u v)
    (hquality : StageQuality frozen committed input hops low high stretch)
    {s t : Fin n} (Q : Late.Path frozen (StoredEdges.graphOfEdges input) s t)
    (hlength : Q.length ≤ 2 * hops) (hweight : Q.micro ≤ high) :
    ShortRoute (committed.graph (StoredEdges.graphOfEdges input)) s t hops (stretch * Q.micro) := by
  by_cases hst : s = t
  · subst t
    refine ⟨0, ?_, .nil s, ?_⟩
    · simpa only [Nat.cast_zero] using mul_nonneg hstretch (Nat.cast_nonneg Q.micro : (0 : ℝ) ≤ Q.micro)
    · simp only [Late.Route.hops_nil, Nat.zero_le]
  · have hlen : Q.vertices.length ≤ 2 * hops + 1 := by rw [Q.length_vertices]; omega
    have hh := ((frozen.graph (StoredEdges.graphOfEdges input)).hopDist_le_pathCost Q.endpoints hlen).trans_eq Q.original_cost
    obtain ⟨d, hd, hdm⟩ := Exact.finite_of_le hh
    have hlo : low ≤ d := by
      have h := ((frozen.graph (StoredEdges.graphOfEdges input)).dist_lower_bound low hmin hst).trans
        ((frozen.graph (StoredEdges.graphOfEdges input)).dist_le_hopDist (2 * hops) s t)
      rw [hd] at h
      exact WithTop.coe_le_coe.mp h
    have hroute := hquality (s, t) d hd hlo (hdm.trans hweight)
    exact hroute.mono_budget (mul_le_mul_of_nonneg_left (by exact_mod_cast hdm) hstretch)

theorem stage_chunks (frozen committed : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hops low high : ℕ) (stretch : ℝ) (hstretch : 0 ≤ stretch)
    (hmin : ∀ u v, u ≠ v → (low : Distance) ≤ frozen.graph (StoredEdges.graphOfEdges input) u v)
    (hquality : StageQuality frozen committed input hops low high stretch)
    (quota : ℕ) {s t : Fin n} (Q : Late.Path frozen (StoredEdges.graphOfEdges input) s t)
    (hlength : Q.length ≤ hops * quota) (hweight : Q.micro ≤ high) :
    ShortRoute (committed.graph (StoredEdges.graphOfEdges input)) s t
      (hops * Parameters.ceilDiv quota 2) (stretch * Q.micro) := by
  induction quota using Nat.strong_induction_on generalizing s t with
  | h quota ih =>
      by_cases hz : quota = 0
      · have hzero : Q.length = 0 := by rw [hz, Nat.mul_zero] at hlength; omega
        cases Q with
        | nil => exact ⟨0, by simp only [Late.Path.micro, Nat.cast_zero, mul_zero, le_refl],
            .nil _, by simp only [Late.Route.hops_nil, Nat.zero_le]⟩
        | cons e Q => simp only [Late.Path.length] at hzero; omega
      · by_cases hshort : Q.length ≤ 2 * hops
        · have hroute := stage_one_chunk frozen committed input hops low high stretch hstretch hmin hquality Q hshort hweight
          have hceil : 1 ≤ Parameters.ceilDiv quota 2 :=
            Parameters.ceilDiv_pos quota 2 (by omega) (by decide)
          exact hroute.mono_hops (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left hops hceil)
        · have hquota : 2 < quota := by
            by_contra hn
            have hm := Nat.mul_le_mul_left hops (show quota ≤ 2 by omega)
            apply hshort
            nlinarith
          have hlong : 2 * hops < Q.length := by omega
          have hsuf := Q.length_suffix (2 * hops)
          have hjoin := congrArg (fun P : Late.Path frozen (StoredEdges.graphOfEdges input) s t => P.length)
            (Q.rejoin (2 * hops))
          simp only [Late.Path.length_append] at hjoin
          have htailLength : (Q.suffix (2 * hops)).length + 2 * hops = Q.length := by omega
          have hprefixLength : (Q.take (2 * hops)).length ≤ 2 * hops := by omega
          have hquotaEq : quota - 2 + 2 = quota := Nat.sub_add_cancel (by omega)
          have hmul := congrArg (fun q : ℕ => hops * q) hquotaEq
          have htailBound : (Q.suffix (2 * hops)).length ≤ hops * (quota - 2) := by
            nlinarith only [htailLength, hmul, hlength]
          have hsplit := Q.micro_split (2 * hops)
          have hprefixWeight : (Q.take (2 * hops)).micro ≤ high := by omega
          have htailWeight : (Q.suffix (2 * hops)).micro ≤ high := by omega
          have hleft := stage_one_chunk frozen committed input hops low high stretch hstretch hmin hquality
            (Q.take (2 * hops)) hprefixLength hprefixWeight
          have hright := ih (quota - 2) (by omega) (s := Q.vertex (2 * hops)) (t := t)
            (Q.suffix (2 * hops)) htailBound htailWeight
          have hceil : Parameters.ceilDiv quota 2 = Parameters.ceilDiv (quota - 2) 2 + 1 := by
            simpa only [hquotaEq] using Parameters.ceilDiv_add_two (quota - 2)
          have hhops : hops + hops * Parameters.ceilDiv (quota - 2) 2 = hops * Parameters.ceilDiv quota 2 := by
            rw [hceil]
            ring
          have hsplitR : ((Q.take (2 * hops)).micro : ℝ) + (Q.suffix (2 * hops)).micro = (Q.micro : ℝ) := by
            exact_mod_cast hsplit
          have hbudget : stretch * ((Q.take (2 * hops)).micro : ℝ) +
              stretch * (Q.suffix (2 * hops)).micro = stretch * Q.micro := by
            rw [← mul_add, hsplitR]
          exact ((hleft.append hright).mono_hops hhops.le).mono_budget hbudget.le

end

end StreamingReachability.Hopset
