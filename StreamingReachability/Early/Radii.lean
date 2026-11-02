module

public import StreamingReachability.Early.Local

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

theorem shiftValue_nonneg {N : ℕ} (phi : Fin N) : 0 ≤ shiftValue phi := by
  unfold shiftValue
  positivity

theorem shiftValue_lt_one {N : ℕ} (phi : Fin N) : shiftValue phi < 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le phi.val).trans_lt phi.isLt
  rw [shiftValue, div_lt_one hN]
  exact_mod_cast phi.isLt

def lambda (k M : ℕ) : ℝ := 4 * (k : ℝ) * M

def searchRadius (k M : ℕ) (D : ℝ) : ℝ := (2 * lambda k M + 2) * D

def nearRadius (k M : ℕ) (D : ℝ) : ℝ := 2 * lambda k M * D

def nextSearchBound (k M : ℕ) (D : ℝ) : ℝ := (lambda k M - 1) * D

/-- This is exactly the joint group/shift minimum-shell rule. -/
def earlyRadius (G : Graph V) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (v : V) (z : Fin M × Fin N) : ℝ :=
  candidateRadius (lambda k M) (4 * k) z.1
    (minimumShellIndex G v (lambda k M) D (shiftValue z.2) (4 * k) (by omega) z.1)
    (shiftValue z.2) D

theorem early_candidate_bounds (k M N : ℕ) (hk : 0 < k) (hD : 0 < D)
    (sigma : Fin M) (phi : Fin N) (j : Fin (4 * k)) :
    lambda k M * D ≤ candidateRadius (lambda k M) (4 * k) sigma j (shiftValue phi) D ∧
      candidateRadius (lambda k M) (4 * k) sigma j (shiftValue phi) D <
        nearRadius k M D := by
  have hphi := shiftValue_nonneg phi
  have hphi1 := shiftValue_lt_one phi
  have hs : (sigma.val : ℝ) + 1 ≤ M := by exact_mod_cast sigma.isLt
  have hj : (j.val : ℝ) + 1 ≤ (4 : ℝ) * k := by exact_mod_cast j.isLt
  have hs0 : (0 : ℝ) ≤ sigma.val := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 4 * k)
  have hlo : 4 * (k : ℝ) * M ≤
      4 * (k : ℝ) * M + 4 * k * sigma.val + j.val + shiftValue phi := by
    have hprod : (0 : ℝ) ≤ 4 * k * sigma.val := by positivity
    linarith
  have hhi : 4 * (k : ℝ) * M + 4 * k * sigma.val + j.val + shiftValue phi <
      2 * (4 * (k : ℝ) * M) := by nlinarith
  simp only [candidateRadius, nearRadius, lambda, Nat.cast_mul, Nat.cast_ofNat]
  exact ⟨mul_le_mul_of_nonneg_right hlo hD.le, mul_lt_mul_of_pos_right hhi hD⟩

theorem early_radius_bounds (G : Graph V) (k M N : ℕ) (hk : 0 < k) (hD : 0 < D)
    (v : V) (z : Fin M × Fin N) :
    lambda k M * D ≤ earlyRadius G D k M N hk v z ∧
      earlyRadius G D k M N hk v z < nearRadius k M D :=
  early_candidate_bounds k M N hk hD z.1 z.2 _

theorem early_radius_range (G : Graph V) (k M N : ℕ) (hk : 0 < k) (hD : 0 < D)
    (v : V) (z : Fin M × Fin N) :
    groupLower (lambda k M) (4 * k) z.1 (shiftValue z.2) D ≤
      earlyRadius G D k M N hk v z ∧
      earlyRadius G D k M N hk v z <
        groupUpper (lambda k M) (4 * k) z.1 (shiftValue z.2) D :=
  candidate_in_group _ _ _ _ hD _ _

theorem expected_early_core (Q : ShortPath G D) (E : Finset V)
    (k M N : ℕ) (hk : 0 < k) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : V => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => (coreAncestorTotal Q E (Sampling.pivots xs)
        (radiusFor (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
        (searchRadius k M D) (nextSearchBound k M D) : ℝ)) ≤ 8 / p := by
  have hl : 0 ≤ lambda k M := by unfold lambda; positivity
  apply expected_core_ancestors Q E (lambda k M) (searchRadius k M D)
    (nextSearchBound k M D) (4 * k) M N (by omega) hM hN hD
    (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩)
    (by unfold searchRadius nextSearchBound; nlinarith) ?_ ?_ ?_ p hp hp1
  · intro v z
    have hb := (early_radius_bounds G k M N hk hD v z).2
    unfold nearRadius searchRadius at *
    linarith
  · intro v z
    have hb := (early_radius_bounds G k M N hk hD v z).1
    unfold nextSearchBound
    nlinarith
  · exact early_radius_range G k M N hk hD

theorem expected_early_pieces (Q : ShortPath G D) (E : Finset V)
    (k M N : ℕ) (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : V => ownerLaw M N hM hN) p hp hp1 E.toList).expect
      (fun xs => (pieceNumber Q (Sampling.pivots xs)
        (radiusFor (earlyRadius G D k M N hk) (⟨0, hM⟩, ⟨0, hN⟩) xs)
        (searchRadius k M D) : ℝ)) ≤
      1 + 2 * p * ((nearPivots Q E (nearRadius k M D)).card : ℝ) :=
  expected_piece_number Q E _ _ _ _ _
    (fun v z => (early_radius_bounds G k M N hk hD v z).2.le) p hp hp1

def searchIn (G : Graph V) (v : V) (R : ℝ) : Finset V :=
  Finset.univ.filter fun u => Within G u v R

def searchOut (G : Graph V) (v : V) (R : ℝ) : Finset V :=
  Finset.univ.filter fun u => Within G v u R

theorem bothBall_card_le (G : Graph V) (v : V) (R : ℝ) :
    (bothBall G v R).card ≤ (searchIn G v R).card + (searchOut G v R).card := by
  have he : bothBall G v R = searchIn G v R ∪ searchOut G v R := by
    ext u
    simp [bothBall, searchIn, searchOut, or_comm]
  rw [he]
  exact Finset.card_union_le _ _

theorem near_card_le_endpoint_balls (Q : ShortPath G D) (E : Finset V)
    (T R : ℝ) (hR : T + D ≤ R) :
    (nearPivots Q E T).card ≤
      (searchIn G (Q.vertex ⟨Q.size - 1, by have := Q.size_pos; omega⟩) R).card +
      (searchOut G (Q.vertex ⟨0, Q.size_pos⟩) R).card := by
  apply (Finset.card_le_card (t :=
    searchIn G (Q.vertex ⟨Q.size - 1, by have := Q.size_pos; omega⟩) R ∪
      searchOut G (Q.vertex ⟨0, Q.size_pos⟩) R) ?_).trans (Finset.card_union_le _ _)
  intro v hv
  have hn := (Finset.mem_filter.mp hv).2
  rcases hn with ⟨i, hi⟩ | ⟨i, hi⟩
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, within_mono (within_trans hi (Q.forward ?_)) hR⟩
    change i.val ≤ Q.size - 1
    have := i.isLt
    omega
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have ht := within_trans (Q.forward (i := ⟨0, Q.size_pos⟩) (j := i)
      (by change 0 ≤ i.val; omega)) hi
    exact within_mono ht (by linarith)

theorem expected_early_shell (G : Graph V) (v : V)
    (k M N b : ℕ) (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (hb : (bothBall G v (searchRadius k M D)).card ≤ 2 * b) :
    (ownerLaw M N hM hN).expect (fun z =>
      ((fringe G v (earlyRadius G D k M N hk v z) D).card : ℝ)) ≤
        (b : ℝ) / ((k : ℝ) * M) := by
  have hs := expected_shifted_minimum_shell G v (lambda k M) D (searchRadius k M D)
    (4 * k) M N (by omega) hM hN hD (by
      intro sigma phi j
      have hh := (early_candidate_bounds k M N hk hD sigma phi j).2
      unfold searchRadius nearRadius at *
      linarith)
  change (ownerLaw M N hM hN).expect (fun z =>
    ((fringe G v (earlyRadius G D k M N hk v z) D).card : ℝ)) ≤ _ at hs
  apply hs.trans
  have hbr : ((bothBall G v (searchRadius k M D)).card : ℝ) ≤ 2 * b := by exact_mod_cast hb
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hden : (0 : ℝ) < (4 * k : ℕ) * M := by positivity
  apply (div_le_div_of_nonneg_right (by nlinarith : 2 *
    ((bothBall G v (searchRadius k M D)).card : ℝ) ≤ 4 * b) hden.le).trans_eq
  push_cast
  field_simp

theorem expected_early_fringe (Q : ShortPath G D) (E : Finset V)
    (k M N b : ℕ) (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (hin : ∀ v, (searchIn G v (searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (searchOut G v (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : V => ownerLaw M N hM hN) p hp hp1 E.toList).expect
      (fun xs => (fringeTotal Q (Sampling.pivots xs)
        (radiusFor (earlyRadius G D k M N hk) (⟨0, hM⟩, ⟨0, hN⟩) xs)
        (searchRadius k M D) : ℝ)) ≤
      2 * (b : ℝ) * b * p / ((k : ℝ) * M) := by
  have hc : (nearPivots Q E (nearRadius k M D)).card ≤ 2 * b := by
    have hh := near_card_le_endpoint_balls Q E (nearRadius k M D) (searchRadius k M D)
      (by unfold nearRadius searchRadius; linarith)
    have hi := hin (Q.vertex ⟨Q.size - 1, by have := Q.size_pos; omega⟩)
    have ho := hout (Q.vertex ⟨0, Q.size_pos⟩)
    omega
  have hb (v : V) : (bothBall G v (searchRadius k M D)).card ≤ 2 * b :=
    (bothBall_card_le G v _).trans (by have := hin v; have := hout v; omega)
  have hs := expected_fringe_total Q E (fun _ : V => ownerLaw M N hM hN)
    (earlyRadius G D k M N hk) (⟨0, hM⟩, ⟨0, hN⟩) (searchRadius k M D)
    (nearRadius k M D) ((b : ℝ) / ((k : ℝ) * M))
    (fun v z => (early_radius_bounds G k M N hk hD v z).2.le)
    (fun v _ => expected_early_shell G v k M N b hk hM hN hD (hb v)) p hp hp1
  apply hs.trans
  have hcr : ((nearPivots Q E (nearRadius k M D)).card : ℝ) ≤ 2 * b := by exact_mod_cast hc
  calc
    _ ≤ p * (2 * b) * ((b : ℝ) / ((k : ℝ) * M)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcr hp) (by positivity)
    _ = _ := by ring

end

end StreamingReachability.Early
