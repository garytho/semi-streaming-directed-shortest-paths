module

public import StreamingReachability.Early
public import StreamingReachability.Late.Choice

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators
open Early

noncomputable section

variable {n : ℕ} {G : Graph (Fin n)} {D : ℝ}

theorem runtime_radius_range (G : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (hD : 0 < D) (v : Fin n) (z : Fin M × Fin N) :
    groupLower (lambda k M) (4 * k) z.1 (shiftValue z.2) D ≤
        Late.radius G D k M N hk v z ∧
      Late.radius G D k M N hk v z <
        groupUpper (lambda k M) (4 * k) z.1 (shiftValue z.2) D :=
  candidate_in_group _ _ _ _ hD _ _

theorem runtime_minimum_card (G : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (v : Fin n) (z : Fin M × Fin N) :
    (Early.fringe G v (Late.radius G D k M N hk v z) D).card =
      (Early.fringe G v (earlyRadius G D k M N hk v z) D).card := by
  apply Nat.le_antisymm
  · exact Late.candidate_minimal G D k M N hk v z
      (minimumShellIndex G v (lambda k M) D (shiftValue z.2) (4 * k) (by omega) z.1)
  · have h := minimumIndex_le (by omega : 0 < 4 * k)
      (fun j : Fin (4 * k) =>
        (Early.fringe G v (candidateRadius (lambda k M) (4 * k) z.1 j
          (shiftValue z.2) D) D).card)
      (Late.candidate G D k M N hk v z.1 z.2)
    exact h

theorem expected_runtime_shell (G : Graph (Fin n)) (v : Fin n)
    (k M N b : ℕ) (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (hb : (Early.bothBall G v (Early.searchRadius k M D)).card ≤ 2 * b) :
    (ownerLaw M N hM hN).expect (fun z =>
      ((Early.fringe G v (Late.radius G D k M N hk v z) D).card : ℝ)) ≤
        (b : ℝ) / ((k : ℝ) * M) := by
  have he : (fun z : Fin M × Fin N =>
      ((Early.fringe G v (Late.radius G D k M N hk v z) D).card : ℝ)) =
        fun z => ((Early.fringe G v (earlyRadius G D k M N hk v z) D).card : ℝ) := by
    funext z
    rw [runtime_minimum_card]
  rw [he]
  exact expected_early_shell G v k M N b hk hM hN hD hb

theorem expected_runtime_fringe (Q : ShortPath G D) (E : Finset (Fin n))
    (k M N b : ℕ) (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (hin : ∀ v, (searchIn G v (Early.searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (searchOut G v (Early.searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : Fin n => ownerLaw M N hM hN) p hp hp1 E.toList).expect
      (fun xs => (fringeTotal Q (Sampling.pivots xs)
        (radiusFor (Late.radius G D k M N hk) (⟨0, hM⟩, ⟨0, hN⟩) xs)
        (Early.searchRadius k M D) : ℝ)) ≤
      2 * (b : ℝ) * b * p / ((k : ℝ) * M) := by
  have hc : (nearPivots Q E (nearRadius k M D)).card ≤ 2 * b := by
    have hh := near_card_le_endpoint_balls Q E (nearRadius k M D) (Early.searchRadius k M D)
      (by unfold nearRadius Early.searchRadius; linarith)
    have hi := hin (Q.vertex ⟨Q.size - 1, by have := Q.size_pos; omega⟩)
    have ho := hout (Q.vertex ⟨0, Q.size_pos⟩)
    omega
  have hb (v : Fin n) : (Early.bothBall G v (Early.searchRadius k M D)).card ≤ 2 * b :=
    (bothBall_card_le G v _).trans (by have := hin v; have := hout v; omega)
  have hs := expected_fringe_total Q E (fun _ : Fin n => ownerLaw M N hM hN)
    (Late.radius G D k M N hk) (⟨0, hM⟩, ⟨0, hN⟩) (Early.searchRadius k M D)
    (nearRadius k M D) ((b : ℝ) / ((k : ℝ) * M))
    (fun v z => (Late.radius_bounds G D k M N hk hD v z).2.le)
    (fun v _ => expected_runtime_shell G v k M N b hk hM hN hD (hb v)) p hp hp1
  apply hs.trans
  have hcr : ((nearPivots Q E (nearRadius k M D)).card : ℝ) ≤ 2 * b := by exact_mod_cast hc
  calc
    _ ≤ p * (2 * b) * ((b : ℝ) / ((k : ℝ) * M)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcr hp) (by positivity)
    _ = _ := by ring

theorem expected_runtime_related (Q : ShortPath G D) (E : Finset (Fin n))
    (k M N b : ℕ) (hk : 0 < k) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (hin : ∀ v, (searchIn G v (Early.searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (searchOut G v (Early.searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : 2 * (b : ℝ) * b * p ^ 2 ≤ (k : ℝ) * M) :
    (Sampling.marked (fun _ : Fin n => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => (actualRelatedTotal Q E (Sampling.pivots xs)
        (radiusFor (Late.radius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
        (Early.searchRadius k M D) (nextSearchBound k M D) : ℝ)) ≤ 17 / p := by
  have hR (v : Fin n) (z : Fin M × Fin N) :
      Late.radius G D k M N hk v z ≤ Early.searchRadius k M D := by
    have h := (Late.radius_bounds G D k M N hk hD v z).2
    unfold nearRadius Early.searchRadius at *
    linarith
  have hmin (v : Fin n) (z : Fin M × Fin N) :
      nextSearchBound k M D + D ≤ Late.radius G D k M N hk v z := by
    have h := (Late.radius_bounds G D k M N hk hD v z).1
    unfold nextSearchBound
    nlinarith
  have hsep : nextSearchBound k M D ≤ Early.searchRadius k M D := by
    have hl : 0 ≤ lambda k M := by unfold lambda; positivity
    unfold nextSearchBound Early.searchRadius
    nlinarith
  have ha := expected_core_ancestors Q E (lambda k M) (Early.searchRadius k M D)
    (nextSearchBound k M D) (4 * k) M N (by omega) hM hN hD
    (Late.radius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩)
    hsep hR hmin (runtime_radius_range G D k M N hk hD) p hp hp1
  have hd := expected_core_descendants Q E (lambda k M) (Early.searchRadius k M D)
    (nextSearchBound k M D) (4 * k) M N (by omega) hM hN hD
    (Late.radius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩)
    hsep hR hmin (runtime_radius_range G D k M N hk hD) p hp hp1
  have hf := expected_runtime_fringe Q E k M N b hk (by omega) hN hD hin hout p hp.le hp1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hfringe : 2 * (b : ℝ) * b * p / ((k : ℝ) * M) ≤ 1 / p := by
    apply (div_le_div_iff₀ (mul_pos hkR hMR) hp).mpr
    nlinarith
  have htotal :
      (Sampling.marked (fun _ : Fin n => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
        (fun xs => (relatedTotal Q E (Sampling.pivots xs)
          (radiusFor (Late.radius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
          (Early.searchRadius k M D) (nextSearchBound k M D) : ℝ)) ≤ 17 / p := by
    simp only [relatedTotal, Nat.cast_add, Law.expect_add]
    calc
      _ ≤ 8 / p + 8 / p + 2 * (b : ℝ) * b * p / ((k : ℝ) * M) :=
        add_le_add (add_le_add ha hd) hf
      _ ≤ 8 / p + 8 / p + 1 / p := add_le_add le_rfl hfringe
      _ = 17 / p := by ring
  apply (Law.expect_mono _ (fun xs => ?_)).trans htotal
  exact_mod_cast actual_related_le Q E (Sampling.pivots xs)
    (radiusFor (Late.radius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
    (Early.searchRadius k M D) (nextSearchBound k M D)

end

end StreamingReachability.Hopset
