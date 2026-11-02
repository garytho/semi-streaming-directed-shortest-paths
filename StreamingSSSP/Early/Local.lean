module

public import StreamingSSSP.Early.Cover
public import StreamingSSSP.Early.Sampling

@[expose] public section

namespace StreamingSSSP.Early

open scoped Classical BigOperators

noncomputable section

variable {V O : Type*} [Fintype V] {G : Graph V} {D : ℝ}

def radiusFor (radius : V → O → ℝ) (fallback : O) (xs : List (V × O)) : V → ℝ :=
  fun v => radius v (Sampling.ownerFor fallback xs v)

def stopped (Q : ShortPath G D) (P : Finset V) (R : ℝ) : Prop :=
  ∃ p ∈ P, Bridge Q p R

def coreCandidates (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) : Finset V :=
  if stopped Q P R then ∅ else
    E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size,
      Within G w (Q.vertex i) Rmin ∧ labels G P rho w = labels G P rho (Q.vertex i)

theorem core_candidates_survive (Q : ShortPath G D) (E : Finset V)
    (radius : V → O → ℝ) (fallback : O) (R Rmin : ℝ)
    (hmin : Rmin ≤ R) (hR : ∀ v o, radius v o ≤ R)
    (xs : List (V × O)) (hn : (xs.map Prod.fst).Nodup) :
    coreCandidates Q E (Sampling.pivots xs) (radiusFor radius fallback xs) R Rmin ⊆
      Sampling.survivors (ancestorSet Q E Rmin)
        (fun w v o => v ∈ ancestorSet Q E Rmin →
          KeepsAncestor Q v w (radius v o) Rmin) xs := by
  intro w hw
  unfold coreCandidates at hw
  split_ifs at hw with hs
  · simp at hw
  · obtain ⟨hwE, _, i, hwi, he⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hwE, i, hwi⟩, ?_⟩
    intro z hz hvA
    have hvP : z.1 ∈ Sampling.pivots xs :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩)
    have hvAnc := (Finset.mem_filter.mp hvA).2
    have hk := core_ancestor_keeps Q (Sampling.pivots xs) (radiusFor radius fallback xs)
      R Rmin (fun p hp hb => hs ⟨p, hp, hb⟩) hmin
      (fun p _ => hR p _) hvP hvAnc hwi he
    simpa only [radiusFor, Sampling.ownerFor_mem fallback hn hz] using hk

theorem expected_core_candidates (Q : ShortPath G D) (E : Finset V)
    (base R Rmin : ℝ) (width M N : ℕ)
    (hw : 0 < width) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (radius : V → Fin M × Fin N → ℝ) (fallback : Fin M × Fin N)
    (hminR : Rmin ≤ R)
    (hR : ∀ v z, radius v z ≤ R)
    (hmin : ∀ v z, Rmin + D ≤ radius v z)
    (hrange : ∀ v (z : Fin M × Fin N),
      groupLower base width z.1 (shiftValue z.2) D ≤ radius v z ∧
      radius v z < groupUpper base width z.1 (shiftValue z.2) D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : V => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => ((coreCandidates Q E (Sampling.pivots xs)
        (radiusFor radius fallback xs) R Rmin).card : ℝ)) ≤ 8 / p := by
  let A := ancestorSet Q E Rmin
  let owner := fun _ : V => ownerLaw M N (by omega) hN
  let K := fun w v z => v ∈ A → KeepsAncestor Q v w (radius v z) Rmin
  have hAE : A ⊆ E := Finset.filter_subset _ _
  have hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      (owner v).prob (K u v) + (owner u).prob (K v u) ≤ (3 : ℝ) / 2 := by
    intro u hu v hv _
    have huA := (Finset.mem_filter.mp hu).2
    have hvA := (Finset.mem_filter.mp hv).2
    have hb := keeps_probability_pair Q v u base Rmin width M N hw (by omega) hN hD
      radius hvA huA hmin hrange
    have hm : (1 : ℝ) / M ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hM)
    have he :
        (owner v).prob (K u v) + (owner u).prob (K v u) =
          (ownerLaw M N (by omega) hN).prob (fun z =>
            KeepsAncestor Q v u (radius v z) Rmin) +
          (ownerLaw M N (by omega) hN).prob (fun z =>
            KeepsAncestor Q u v (radius u z) Rmin) := by
      simp only [owner, K, hu, hv, true_implies]
    rw [he]
    linarith
  apply (Sampling.expect_mono_on
    (Sampling.marked owner p hp.le hp1 E.toList) ?_).trans
      (Sampling.expected_survivors_le owner p hp hp1 E A hAE K hpair)
  refine Sampling.holds_mono (Sampling.marked_keys_sublist owner p hp.le hp1 E.toList)
    (fun xs hsub => ?_)
  have hn := (Finset.nodup_toList E).sublist hsub
  exact_mod_cast Finset.card_le_card
    (core_candidates_survive Q E radius fallback R Rmin hminR hR xs hn)

def coreRelated (Q : ShortPath G D) (E P : Finset V) (rho : V → ℝ)
    (R Rmin : ℝ) (I : ℕ × ℕ) : Finset V :=
  let S := coreClass G P rho (smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1)
  E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
    ∃ hw : w ∈ S, ∃ hi : Q.vertex i ∈ S,
      Within (G.restrict S) ⟨w, hw⟩ ⟨Q.vertex i, hi⟩ Rmin

def coreAncestorTotal (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) : ℕ :=
  if stopped Q P R then 0 else
    ∑ I ∈ corePieces Q P rho R, (coreRelated Q E P rho R Rmin I).card

theorem core_total_le_candidates (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) :
    coreAncestorTotal Q E P rho R Rmin ≤ (coreCandidates Q E P rho R Rmin).card := by
  by_cases hs : stopped Q P R
  · simp [coreAncestorTotal, coreCandidates, hs]
  · rw [coreAncestorTotal, ite_eq_right hs]
    have hsub (I : ℕ × ℕ) (_hI : I ∈ corePieces Q P rho R) :
        coreRelated Q E P rho R Rmin I ⊆ coreCandidates Q E P rho R Rmin := by
      intro w hw
      obtain ⟨hwE, hwP, i, _, hwm, him, hd⟩ := Finset.mem_filter.mp hw
      rw [coreCandidates, ite_eq_right hs]
      exact Finset.mem_filter.mpr ⟨hwE, hwP, i, within_restrict G _ hd,
        hwm.2.trans him.2.symm⟩
    rw [sum_card_eq_count (corePieces Q P rho R) (coreCandidates Q E P rho R Rmin) _ hsub]
    calc
      _ ≤ ∑ _w ∈ coreCandidates Q E P rho R Rmin, 1 := by
        apply Finset.sum_le_sum
        intro w _
        apply Finset.card_le_one.mpr
        intro I hI J hJ
        obtain ⟨hIp, hwI⟩ := Finset.mem_filter.mp hI
        obtain ⟨hJp, hwJ⟩ := Finset.mem_filter.mp hJ
        obtain ⟨_, _, i, _, hwm, _, _⟩ := Finset.mem_filter.mp hwI
        obtain ⟨_, _, j, _, hwj, _, _⟩ := Finset.mem_filter.mp hwJ
        exact core_piece_classes_distinct Q P rho R hIp hJp (hwm.2.symm.trans hwj.2)
      _ = _ := by simp

theorem expected_core_ancestors (Q : ShortPath G D) (E : Finset V)
    (base R Rmin : ℝ) (width M N : ℕ)
    (hw : 0 < width) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (radius : V → Fin M × Fin N → ℝ) (fallback : Fin M × Fin N)
    (hminR : Rmin ≤ R) (hR : ∀ v z, radius v z ≤ R)
    (hmin : ∀ v z, Rmin + D ≤ radius v z)
    (hrange : ∀ v (z : Fin M × Fin N),
      groupLower base width z.1 (shiftValue z.2) D ≤ radius v z ∧
      radius v z < groupUpper base width z.1 (shiftValue z.2) D)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : V => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => (coreAncestorTotal Q E (Sampling.pivots xs)
        (radiusFor radius fallback xs) R Rmin : ℝ)) ≤ 8 / p := by
  apply (Law.expect_mono _ (fun xs => ?_)).trans
    (expected_core_candidates Q E base R Rmin width M N hw hM hN hD radius fallback
      hminR hR hmin hrange p hp hp1)
  exact_mod_cast core_total_le_candidates Q E (Sampling.pivots xs)
    (radiusFor radius fallback xs) R Rmin

def pieceNumber (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) : ℕ :=
  if stopped Q P R then 0 else
    (corePieces Q P rho R).card + (fringeOwners Q P rho R).card

omit [Fintype V] in
theorem pivot_filter_card_le (xs : List (V × O)) (P : V → Prop) :
    (((Sampling.pivots xs).filter P).card : ℝ) ≤
      (xs.map fun z => if P z.1 then (1 : ℝ) else 0).sum := by
  have he : (Sampling.pivots xs).filter P =
      ((xs.filter fun z => P z.1).map Prod.fst).toFinset := by
    ext v
    simp only [Sampling.pivots, Finset.mem_filter, List.mem_toFinset, List.mem_map,
      List.mem_filter]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hp⟩
      exact ⟨z, ⟨hz, decide_eq_true hp⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hp⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, of_decide_eq_true hp⟩
  rw [he]
  have hc := List.toFinset_card_le ((xs.filter fun z => P z.1).map Prod.fst)
  rw [List.length_map] at hc
  have heq : (((xs.filter fun z => P z.1).length : ℕ) : ℝ) =
      (xs.map fun z => if P z.1 then (1 : ℝ) else 0).sum := by
    clear he hc
    induction xs with
    | nil => simp
    | cons z xs ih => by_cases h : P z.1 <;> simp [h, ih, add_comm]
  have hcr : (((xs.filter fun z => P z.1).map Prod.fst).toFinset.card : ℝ) ≤
      ((xs.filter fun z => P z.1).length : ℝ) := by exact_mod_cast hc
  exact hcr.trans_eq heq

theorem expected_piece_number (Q : ShortPath G D) (E : Finset V)
    (owner : V → Law O) (radius : V → O → ℝ) (fallback : O) (R T : ℝ)
    (hrho : ∀ v o, radius v o ≤ T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Sampling.marked owner p hp hp1 E.toList).expect
      (fun xs => (pieceNumber Q (Sampling.pivots xs)
        (radiusFor radius fallback xs) R : ℝ)) ≤
      1 + 2 * p * ((nearPivots Q E T).card : ℝ) := by
  have hpoint (xs : List (V × O)) :
      (pieceNumber Q (Sampling.pivots xs) (radiusFor radius fallback xs) R : ℝ) ≤
        1 + 2 * (xs.map fun z => if Near Q z.1 T then (1 : ℝ) else 0).sum := by
    have hc := grouped_type1_count_at Q (Sampling.pivots xs)
      (radiusFor radius fallback xs) R T (fun v _ => hrho v _)
    have hpiv := pivot_filter_card_le xs (fun v => Near Q v T)
    change (((nearPivots Q (Sampling.pivots xs) T).card : ℕ) : ℝ) ≤ _ at hpiv
    have hc' : ((corePieces Q (Sampling.pivots xs) (radiusFor radius fallback xs) R).card : ℝ) +
        ((fringeOwners Q (Sampling.pivots xs) (radiusFor radius fallback xs) R).card : ℝ) ≤
          2 * ((nearPivots Q (Sampling.pivots xs) T).card : ℝ) + 1 := by exact_mod_cast hc
    unfold pieceNumber
    split_ifs
    · have h0 : 0 ≤ (xs.map fun z => if Near Q z.1 T then (1 : ℝ) else 0).sum :=
        List.sum_nonneg (by intro a ha; obtain ⟨z, _, rfl⟩ := List.mem_map.mp ha; split_ifs <;> norm_num)
      norm_num
      linarith
    · push_cast
      linarith
  apply (Law.expect_mono _ hpoint).trans_eq
  rw [Law.expect_add, Law.expect_const, Law.expect_mul,
    Sampling.expected_total_finset owner p hp hp1 E
      (fun v _ => if Near Q v T then (1 : ℝ) else 0)]
  have he : (∑ v ∈ E, (owner v).expect
      (fun _ => if Near Q v T then (1 : ℝ) else 0)) = ((nearPivots Q E T).card : ℝ) := by
    simp only [Law.expect_const, nearPivots, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [he]
  ring

def fringeTotal (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) : ℕ :=
  if stopped Q P R then 0 else
    ∑ v ∈ fringeOwners Q P rho R, (fringe G v (rho v) D).card

theorem fringe_total_le (Q : ShortPath G D) (radius : V → O → ℝ) (fallback : O)
    (R T : ℝ) (hrho : ∀ v o, radius v o ≤ T)
    (xs : List (V × O)) (hn : (xs.map Prod.fst).Nodup) :
    (fringeTotal Q (Sampling.pivots xs) (radiusFor radius fallback xs) R : ℝ) ≤
      (xs.map fun z => if Near Q z.1 T then
        ((fringe G z.1 (radius z.1 z.2) D).card : ℝ) else 0).sum := by
  rw [← Sampling.sum_pivots fallback xs hn
    (fun v o => if Near Q v T then ((fringe G v (radius v o) D).card : ℝ) else 0)]
  unfold fringeTotal
  split_ifs
  · simp only [Nat.cast_zero]
    change (0 : ℝ) ≤ ∑ v ∈ Sampling.pivots xs,
      if Near Q v T then ((fringe G v
        (radius v (Sampling.ownerFor fallback xs v)) D).card : ℝ) else 0
    exact Finset.sum_nonneg (by intro v _; split_ifs <;> positivity)
  · push_cast
    have hs : fringeOwners Q (Sampling.pivots xs) (radiusFor radius fallback xs) R ⊆
        Sampling.pivots xs := Finset.filter_subset _ _
    calc
      _ = ∑ v ∈ fringeOwners Q (Sampling.pivots xs) (radiusFor radius fallback xs) R,
          if Near Q v T then ((fringe G v (radiusFor radius fallback xs v) D).card : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        simp only [fringe_owner_near Q _ _ R T (fun v _ => hrho v _) hv, ↓reduceIte]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (by
        intro v _ _
        split_ifs <;> positivity)

theorem expected_fringe_total (Q : ShortPath G D) (E : Finset V)
    (owner : V → Law O) (radius : V → O → ℝ) (fallback : O)
    (R T C : ℝ) (hrho : ∀ v o, radius v o ≤ T)
    (hC : ∀ v ∈ E, (owner v).expect
      (fun o => ((fringe G v (radius v o) D).card : ℝ)) ≤ C)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Sampling.marked owner p hp hp1 E.toList).expect
      (fun xs => (fringeTotal Q (Sampling.pivots xs) (radiusFor radius fallback xs) R : ℝ)) ≤
        p * ((nearPivots Q E T).card : ℝ) * C := by
  apply (Sampling.expect_mono_on _ ?_).trans
    (show (Sampling.marked owner p hp hp1 E.toList).expect
      (fun xs => (xs.map fun z => if Near Q z.1 T then
        ((fringe G z.1 (radius z.1 z.2) D).card : ℝ) else 0).sum) ≤ _ from ?_)
  · refine Sampling.holds_mono (Sampling.marked_keys_sublist owner p hp hp1 E.toList)
      (fun xs hsub => ?_)
    exact fringe_total_le Q radius fallback R T hrho xs ((Finset.nodup_toList E).sublist hsub)
  · rw [Sampling.expected_total_finset owner p hp hp1 E
      (fun v o => if Near Q v T then ((fringe G v (radius v o) D).card : ℝ) else 0)]
    have hsum : (∑ v ∈ E, (owner v).expect (fun o => if Near Q v T then
          ((fringe G v (radius v o) D).card : ℝ) else 0)) ≤
        ((nearPivots Q E T).card : ℝ) * C := by
      calc
        _ ≤ ∑ v ∈ E, if Near Q v T then C else 0 := by
          apply Finset.sum_le_sum
          intro v hv
          by_cases h : Near Q v T
          · simpa only [h, ↓reduceIte] using hC v hv
          · simp only [h, ↓reduceIte, Law.expect_const, le_refl]
        _ = _ := by
          rw [← Finset.sum_filter]
          simp [nearPivots]
    exact (mul_le_mul_of_nonneg_left hsum hp).trans_eq (by ring)

end

end StreamingSSSP.Early
