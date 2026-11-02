module

public import StreamingReachability.Early.Radii

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

namespace ShortPath

def reversed (Q : ShortPath G D) : ShortPath G.reverse D where
  vertices := Q.vertices.reverse
  nonempty := by simpa using Q.nonempty
  cost := Q.cost
  cost_eq := by rw [Graph.pathCost_reverse, Q.cost_eq]
  cost_le := Q.cost_le

omit [Fintype V] in
theorem reversed_exists (Q : ShortPath G D) (P : V → Prop) :
    (∃ i : Fin Q.reversed.size, P (Q.reversed.vertex i)) ↔
      ∃ i : Fin Q.size, P (Q.vertex i) := by
  change (∃ i : Fin Q.vertices.reverse.length, P (Q.vertices.reverse.get i)) ↔
    ∃ i : Fin Q.vertices.length, P (Q.vertices.get i)
  rw [← List.exists_mem_iff_get, ← List.exists_mem_iff_get]
  simp

end ShortPath

theorem labels_reverse (G : Graph V) (P : Finset V) (rho : V → ℝ) (v : V) :
    labels G.reverse P rho v = (labels G P rho v).swap := by
  apply Prod.ext
  · change (P.filter fun p => Within G.reverse v p (rho p)) =
      P.filter fun p => Within G p v (rho p)
    apply Finset.filter_congr
    intro p _
    exact within_reverse G p v (rho p)
  · change (P.filter fun p => Within G.reverse p v (rho p)) =
      P.filter fun p => Within G v p (rho p)
    apply Finset.filter_congr
    intro p _
    exact within_reverse G v p (rho p)

theorem bridge_reverse (Q : ShortPath G D) (p : V) (R : ℝ) :
    Bridge Q.reversed p R ↔ Bridge Q p R := by
  unfold Bridge
  rw [Q.reversed_exists (fun v => Within G.reverse p v R),
    Q.reversed_exists (fun v => Within G.reverse v p R)]
  simp only [Within, Graph.dist_reverse]
  exact and_comm

theorem stopped_reverse (Q : ShortPath G D) (P : Finset V) (R : ℝ) :
    stopped Q.reversed P R ↔ stopped Q P R := by
  simp only [stopped, bridge_reverse]

def coreDescCandidates (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) : Finset V :=
  if stopped Q P R then ∅ else
    E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size,
      Within G (Q.vertex i) w Rmin ∧ labels G P rho w = labels G P rho (Q.vertex i)

theorem core_candidates_reverse (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) :
    coreCandidates Q.reversed E P rho R Rmin = coreDescCandidates Q E P rho R Rmin := by
  have hs : stopped Q.reversed P R = stopped Q P R := propext (stopped_reverse Q P R)
  simp only [coreCandidates, coreDescCandidates, hs]
  split_ifs
  · rfl
  · ext w
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    rw [Q.reversed_exists (fun v => Within G.reverse w v Rmin ∧
      labels G.reverse P rho w = labels G.reverse P rho v)]
    simp only [labels_reverse, Within, Graph.dist_reverse, Prod.swap_inj]

def coreDescRelated (Q : ShortPath G D) (E P : Finset V) (rho : V → ℝ)
    (R Rmin : ℝ) (I : ℕ × ℕ) : Finset V :=
  let S := coreClass G P rho (smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1)
  E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size, Cells.Contains I i.val ∧
    ∃ hw : w ∈ S, ∃ hi : Q.vertex i ∈ S,
      Within (G.restrict S) ⟨Q.vertex i, hi⟩ ⟨w, hw⟩ Rmin

def coreDescendantTotal (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) : ℕ :=
  if stopped Q P R then 0 else
    ∑ I ∈ corePieces Q P rho R, (coreDescRelated Q E P rho R Rmin I).card

theorem core_desc_total_le_candidates (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) :
    coreDescendantTotal Q E P rho R Rmin ≤ (coreDescCandidates Q E P rho R Rmin).card := by
  by_cases hs : stopped Q P R
  · simp [coreDescendantTotal, coreDescCandidates, hs]
  · rw [coreDescendantTotal, ite_eq_right hs]
    have hsub (I : ℕ × ℕ) (_hI : I ∈ corePieces Q P rho R) :
        coreDescRelated Q E P rho R Rmin I ⊆ coreDescCandidates Q E P rho R Rmin := by
      intro w hw
      obtain ⟨hwE, hwP, i, _, hwm, him, hd⟩ := Finset.mem_filter.mp hw
      rw [coreDescCandidates, ite_eq_right hs]
      exact Finset.mem_filter.mpr ⟨hwE, hwP, i, within_restrict G _ hd,
        hwm.2.trans him.2.symm⟩
    rw [sum_card_eq_count (corePieces Q P rho R) (coreDescCandidates Q E P rho R Rmin) _ hsub]
    calc
      _ ≤ ∑ _w ∈ coreDescCandidates Q E P rho R Rmin, 1 := by
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

theorem expected_core_descendants (Q : ShortPath G D) (E : Finset V)
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
      (fun xs => (coreDescendantTotal Q E (Sampling.pivots xs)
        (radiusFor radius fallback xs) R Rmin : ℝ)) ≤ 8 / p := by
  have hrev := expected_core_candidates Q.reversed E base R Rmin width M N hw hM hN hD
    radius fallback hminR hR hmin hrange p hp hp1
  simp_rw [core_candidates_reverse] at hrev
  apply (Law.expect_mono _ (fun xs => ?_)).trans hrev
  exact_mod_cast core_desc_total_le_candidates Q E (Sampling.pivots xs)
    (radiusFor radius fallback xs) R Rmin

/-- Core occurrences count only eligible vertices not selected at this level.
Fringes are deliberately charged by their full size: old pivots and current
pivots remain vertices of other pivots' fringe graphs. -/
def relatedTotal (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) : ℕ :=
  coreAncestorTotal Q E P rho R Rmin + coreDescendantTotal Q E P rho R Rmin +
    fringeTotal Q P rho R

theorem expected_early_related (Q : ShortPath G D) (E : Finset V)
    (k M N b : ℕ) (hk : 0 < k) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (hin : ∀ v, (searchIn G v (searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (searchOut G v (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : V => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => (relatedTotal Q E (Sampling.pivots xs)
        (radiusFor (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
        (searchRadius k M D) (nextSearchBound k M D) : ℝ)) ≤
      16 / p + 2 * (b : ℝ) * b * p / ((k : ℝ) * M) := by
  have ha := expected_early_core Q E k M N hk hM hN hD p hp hp1
  have hf := expected_early_fringe Q E k M N b hk (by omega) hN hD hin hout p hp.le hp1
  have hl : 0 ≤ lambda k M := by unfold lambda; positivity
  have hd := expected_core_descendants Q E (lambda k M) (searchRadius k M D)
    (nextSearchBound k M D) (4 * k) M N (by omega) hM hN hD
    (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩)
    (by unfold searchRadius nextSearchBound; nlinarith)
    (fun v z => (early_radius_bounds G k M N hk hD v z).2.le.trans (by
      unfold nearRadius searchRadius; linarith))
    (fun v z => by
      have hb := (early_radius_bounds G k M N hk hD v z).1
      unfold nextSearchBound
      nlinarith)
    (early_radius_range G k M N hk hD) p hp hp1
  simp only [relatedTotal, Nat.cast_add, Law.expect_add]
  calc
    _ ≤ 8 / p + 8 / p + 2 * (b : ℝ) * b * p / ((k : ℝ) * M) :=
      add_le_add (add_le_add ha hd) hf
    _ = _ := by ring

theorem expected_early_related_le (Q : ShortPath G D) (E : Finset V)
    (k M N b : ℕ) (hk : 0 < k) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (hin : ∀ v, (searchIn G v (searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (searchOut G v (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : 2 * (b : ℝ) * b * p ^ 2 ≤ (k : ℝ) * M) :
    (Sampling.marked (fun _ : V => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => (relatedTotal Q E (Sampling.pivots xs)
        (radiusFor (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
        (searchRadius k M D) (nextSearchBound k M D) : ℝ)) ≤ 17 / p := by
  have hs := expected_early_related Q E k M N b hk hM hN hD hin hout p hp hp1
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hM' : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hf : 2 * (b : ℝ) * b * p / ((k : ℝ) * M) ≤ 1 / p := by
    apply (div_le_div_iff₀ (mul_pos hk' hM') hp).mpr
    nlinarith
  calc
    _ ≤ 16 / p + 2 * (b : ℝ) * b * p / ((k : ℝ) * M) := hs
    _ ≤ 16 / p + 1 / p := add_le_add le_rfl hf
    _ = _ := by ring

def fringeRelated (Q : ShortPath G D) (E P : Finset V) (rho : V → ℝ)
    (R Rmin : ℝ) (p : V) : Finset V :=
  let S : Set V := ↑(fringe G p (rho p) D)
  E.filter fun w => w ∉ P ∧ ∃ i : Fin Q.size,
    Cells.Contains (fringeInterval Q P rho R p) i.val ∧
    ∃ hw : w ∈ S, ∃ hi : Q.vertex i ∈ S,
      Within (G.restrict S) ⟨w, hw⟩ ⟨Q.vertex i, hi⟩ Rmin ∨
      Within (G.restrict S) ⟨Q.vertex i, hi⟩ ⟨w, hw⟩ Rmin

theorem fringe_related_subset (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) (p : V) :
    fringeRelated Q E P rho R Rmin p ⊆ fringe G p (rho p) D := by
  intro w hw
  obtain ⟨_, _, i, _, hwm, _, _⟩ := Finset.mem_filter.mp hw
  exact hwm

/-- The actual local eligible path-related tally in the induced core and
fringe graphs, before the next type-2 length split. -/
def actualRelatedTotal (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) : ℕ :=
  if stopped Q P R then 0 else
    (∑ I ∈ corePieces Q P rho R,
      (coreRelated Q E P rho R Rmin I ∪ coreDescRelated Q E P rho R Rmin I).card) +
    ∑ p ∈ fringeOwners Q P rho R, (fringeRelated Q E P rho R Rmin p).card

theorem actual_related_le (Q : ShortPath G D) (E P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ) :
    actualRelatedTotal Q E P rho R Rmin ≤ relatedTotal Q E P rho R Rmin := by
  by_cases hs : stopped Q P R
  · simp [actualRelatedTotal, relatedTotal, coreAncestorTotal, coreDescendantTotal,
      fringeTotal, hs]
  · have hc :
        (∑ I ∈ corePieces Q P rho R,
          (coreRelated Q E P rho R Rmin I ∪ coreDescRelated Q E P rho R Rmin I).card) ≤
        (∑ I ∈ corePieces Q P rho R, (coreRelated Q E P rho R Rmin I).card) +
        ∑ I ∈ corePieces Q P rho R, (coreDescRelated Q E P rho R Rmin I).card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun I _ => Finset.card_union_le _ _
    have hf :
        (∑ p ∈ fringeOwners Q P rho R, (fringeRelated Q E P rho R Rmin p).card) ≤
          ∑ p ∈ fringeOwners Q P rho R, (fringe G p (rho p) D).card :=
      Finset.sum_le_sum fun p _ => Finset.card_le_card (fringe_related_subset Q E P rho R Rmin p)
    simp only [actualRelatedTotal, relatedTotal, coreAncestorTotal, coreDescendantTotal,
      fringeTotal, hs, ↓reduceIte]
    exact add_le_add hc hf

theorem expected_actual_early_related (Q : ShortPath G D) (E : Finset V)
    (k M N b : ℕ) (hk : 0 < k) (hM : 2 ≤ M) (hN : 0 < N) (hD : 0 < D)
    (hin : ∀ v, (searchIn G v (searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (searchOut G v (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hbudget : 2 * (b : ℝ) * b * p ^ 2 ≤ (k : ℝ) * M) :
    (Sampling.marked (fun _ : V => ownerLaw M N (by omega) hN) p hp.le hp1 E.toList).expect
      (fun xs => (actualRelatedTotal Q E (Sampling.pivots xs)
        (radiusFor (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
        (searchRadius k M D) (nextSearchBound k M D) : ℝ)) ≤ 17 / p := by
  apply (Law.expect_mono _ (fun xs => ?_)).trans
    (expected_early_related_le Q E k M N b hk hM hN hD hin hout p hp hp1 hbudget)
  exact_mod_cast actual_related_le Q E (Sampling.pivots xs)
    (radiusFor (earlyRadius G D k M N hk) (⟨0, by omega⟩, ⟨0, hN⟩) xs)
    (searchRadius k M D) (nextSearchBound k M D)

end

end StreamingReachability.Early
