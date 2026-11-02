module

public import StreamingReachability.Early.Partition
public import StreamingReachability.Probability.Uniform
public import StreamingReachability.Tournament

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

def ancestorSet (Q : ShortPath G D) (E : Finset V) (Rmin : ℝ) : Finset V :=
  E.filter fun u => ∃ i : Fin Q.size, Within G u (Q.vertex i) Rmin

/-- A necessary condition for `w` to remain an ancestor in a core class
meeting the path after the single pivot `u`. This is an overestimate, not
an assumption that a witness survives the other pivots. -/
def KeepsAncestor (Q : ShortPath G D) (u w : V) (rho Rmin : ℝ) : Prop :=
  ∃ i : Fin Q.size, Within G w (Q.vertex i) Rmin ∧
    ¬ Within G w u rho ∧
    (Within G u w rho ↔ Within G u (Q.vertex i) rho)

theorem core_ancestor_keeps (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R Rmin : ℝ)
    (hnb : ∀ p ∈ P, ¬ Bridge Q p R)
    (hmin : Rmin ≤ R) (hrho : ∀ p ∈ P, rho p ≤ R)
    {u w : V} (hu : u ∈ P)
    (huA : ∃ j : Fin Q.size, Within G u (Q.vertex j) Rmin)
    {i : Fin Q.size} (hwi : Within G w (Q.vertex i) Rmin)
    (he : labels G P rho w = labels G P rho (Q.vertex i)) :
    KeepsAncestor Q u w (rho u) Rmin := by
  have hback : ¬ Within G (Q.vertex i) u (rho u) := by
    intro h
    obtain ⟨j, hj⟩ := huA
    exact hnb u hu ⟨⟨j, within_mono hj hmin⟩, ⟨i, within_mono h (hrho u hu)⟩⟩
  have hin := Finset.ext_iff.mp (congrArg Prod.fst he) u
  have hout := Finset.ext_iff.mp (congrArg Prod.snd he) u
  simp only [labels, Finset.mem_filter, hu, true_and] at hin hout
  exact ⟨i, hwi, fun h => hback (hin.mp h), hout⟩

theorem keeps_far_order (Q : ShortPath G D) (u w : V) (rho Rmin : ℝ)
    (hu : ∃ j : Fin Q.size, Within G u (Q.vertex j) Rmin)
    (hscale : Rmin + D ≤ rho)
    (hfar : ¬ Within G u w rho)
    (hkeep : KeepsAncestor Q u w rho Rmin) :
    Index.first (fun i : Fin Q.size => Within G w (Q.vertex i) Rmin) <
      Index.first (fun i : Fin Q.size => Within G u (Q.vertex i) Rmin) := by
  obtain ⟨i, hwi, _, he⟩ := hkeep
  obtain ⟨j, hj⟩ := hu
  have hfirst := Index.first_le
    (P := fun i : Fin Q.size => Within G u (Q.vertex i) Rmin) hj
  have hklt : Index.first (fun i : Fin Q.size =>
      Within G u (Q.vertex i) Rmin) < Q.size := hfirst.trans_lt j.isLt
  have hk := Index.first_mem hklt
  have hi : i.val < Index.first (fun i : Fin Q.size =>
      Within G u (Q.vertex i) Rmin) := by
    by_contra hn
    have hki : (⟨_, hklt⟩ : Fin Q.size) ≤ i := by
      change Index.first (fun i : Fin Q.size => Within G u (Q.vertex i) Rmin) ≤ i.val
      omega
    exact hfar (he.mpr (within_mono (within_trans hk (Q.forward hki)) hscale))
  exact (Index.first_le
    (P := fun i : Fin Q.size => Within G w (Q.vertex i) Rmin) hwi).trans_lt hi

theorem keeps_pair_far_impossible (Q : ShortPath G D) (u w : V)
    (rhoU rhoW Rmin : ℝ)
    (hu : ∃ j : Fin Q.size, Within G u (Q.vertex j) Rmin)
    (hw : ∃ j : Fin Q.size, Within G w (Q.vertex j) Rmin)
    (hU : Rmin + D ≤ rhoU) (hW : Rmin + D ≤ rhoW)
    (huw : ¬ Within G u w rhoU) (hwu : ¬ Within G w u rhoW) :
    ¬ (KeepsAncestor Q u w rhoU Rmin ∧ KeepsAncestor Q w u rhoW Rmin) := by
  rintro ⟨h1, h2⟩
  have hlt := keeps_far_order Q u w rhoU Rmin hu hU huw h1
  have hgt := keeps_far_order Q w u rhoW Rmin hw hW hwu h2
  omega

theorem bounded_min_iff (d e : Distance) (R : ℝ) :
    Bounded (min d e) R ↔ Bounded d R ∨ Bounded e R := by
  rcases le_total d e with h | h
  · rw [min_eq_left h]
    exact ⟨Or.inl, fun h' => h'.elim id (bounded_mono_distance h)⟩
  · rw [min_eq_right h]
    exact ⟨Or.inr, fun h' => h'.elim (bounded_mono_distance h) id⟩

def pairDistance (G : Graph V) (u w : V) : Distance :=
  min (G.dist u w) (G.dist w u)

def InWindow (d : Distance) (lo hi : ℝ) : Prop :=
  ∃ h : ℕ, d = h ∧ lo ≤ (h : ℝ) ∧ (h : ℝ) < hi

/-- The noisy-knockout geometry. Different vertices may use different
minimizers in the same owner group. No common minimizer is assumed. -/
theorem keeps_pair_window (Q : ShortPath G D) (u w : V)
    (rhoU rhoW Rmin lo hi : ℝ)
    (hu : ∃ j : Fin Q.size, Within G u (Q.vertex j) Rmin)
    (hw : ∃ j : Fin Q.size, Within G w (Q.vertex j) Rmin)
    (hU : Rmin + D ≤ rhoU) (hW : Rmin + D ≤ rhoW)
    (hloU : lo ≤ rhoU) (hloW : lo ≤ rhoW)
    (hhiU : rhoU < hi) (hhiW : rhoW < hi)
    (hkeep : KeepsAncestor Q u w rhoU Rmin ∧ KeepsAncestor Q w u rhoW Rmin) :
    InWindow (pairDistance G u w) lo hi := by
  have hnotlo : ¬ Bounded (pairDistance G u w) lo := by
    rw [pairDistance, bounded_min_iff]
    rintro (h | h)
    · exact hkeep.2.choose_spec.2.1 (within_mono h hloW)
    · exact hkeep.1.choose_spec.2.1 (within_mono h hloU)
  have hsome : Within G u w rhoU ∨ Within G w u rhoW := by
    by_contra hn
    push Not at hn
    exact keeps_pair_far_impossible Q u w rhoU rhoW Rmin hu hw hU hW hn.1 hn.2 hkeep
  have hbound : ∃ h : ℕ, pairDistance G u w = h ∧ (h : ℝ) < hi := by
    rcases hsome with h | h
    · obtain ⟨d, hd, hle⟩ := bounded_mono_distance (min_le_left _ _) h
      exact ⟨d, hd, hle.trans_lt hhiU⟩
    · obtain ⟨d, hd, hle⟩ := bounded_mono_distance (min_le_right _ _) h
      exact ⟨d, hd, hle.trans_lt hhiW⟩
  obtain ⟨h, hh, hhi⟩ := hbound
  exact ⟨h, hh, le_of_not_gt (fun hl => hnotlo ⟨h, hh, hl.le⟩), hhi⟩

def groupLower (base : ℝ) (width : ℕ) {M : ℕ} (sigma : Fin M)
    (shift D : ℝ) : ℝ :=
  (base + (width : ℝ) * sigma.val + shift) * D

def groupUpper (base : ℝ) (width : ℕ) {M : ℕ} (sigma : Fin M)
    (shift D : ℝ) : ℝ :=
  (base + (width : ℝ) * (sigma.val + 1) + shift) * D

theorem group_windows_disjoint (base shift D : ℝ) (width : ℕ)
    (hwidth : 0 < width) (_hD : 0 < D) {M : ℕ}
    {sigma tau : Fin M} {d : Distance}
    (hs : InWindow d (groupLower base width sigma shift D)
      (groupUpper base width sigma shift D))
    (ht : InWindow d (groupLower base width tau shift D)
      (groupUpper base width tau shift D)) : sigma = tau := by
  obtain ⟨a, ha, has, hat⟩ := hs
  obtain ⟨b, hb, hbs, hbt⟩ := ht
  have hab : a = b := WithTop.coe_eq_coe.mp (ha.symm.trans hb)
  subst b
  apply Fin.ext
  have hw : (0 : ℝ) < width := by exact_mod_cast hwidth
  simp only [groupLower, groupUpper] at has hat hbs hbt
  rcases lt_trichotomy sigma.val tau.val with h | h | h
  · have hh : (sigma.val : ℝ) + 1 ≤ tau.val := by exact_mod_cast h
    nlinarith
  · exact h
  · have hh : (tau.val : ℝ) + 1 ≤ sigma.val := by exact_mod_cast h
    nlinarith

theorem group_bad_card_le_one (base shift D : ℝ) (width : ℕ)
    (hwidth : 0 < width) (hD : 0 < D) {M : ℕ} (d : Distance) :
    (Finset.univ.filter fun sigma : Fin M =>
      InWindow d (groupLower base width sigma shift D)
        (groupUpper base width sigma shift D)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro sigma hs tau ht
  exact group_windows_disjoint base shift D width hwidth hD
    (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2

def shiftValue {N : ℕ} (phi : Fin N) : ℝ := phi.val / (N : ℝ)

def candidateRadius (base : ℝ) (width : ℕ) {M : ℕ} (sigma : Fin M)
    (j : Fin width) (shift D : ℝ) : ℝ :=
  (base + (width : ℝ) * sigma.val + j.val + shift) * D

theorem candidate_in_group (base shift D : ℝ) (width : ℕ)
    (hD : 0 < D) {M : ℕ} (sigma : Fin M) (j : Fin width) :
    groupLower base width sigma shift D ≤ candidateRadius base width sigma j shift D ∧
      candidateRadius base width sigma j shift D <
        groupUpper base width sigma shift D := by
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  have hjw : (j.val : ℝ) < width := by exact_mod_cast j.isLt
  simp only [groupLower, groupUpper, candidateRadius]
  constructor <;> nlinarith

/-- The owner is joint-uniform: first the shift, then an independent group.
The order here changes no distribution. -/
def ownerLaw (M N : ℕ) (hM : 0 < M) (hN : 0 < N) : Law (Fin M × Fin N) :=
  (Law.uniform N hN).bind fun phi => (Law.uniform M hM).map fun sigma => (sigma, phi)

theorem expect_owner {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (f : Fin M × Fin N → ℝ) :
    (ownerLaw M N hM hN).expect f =
      (∑ phi, ∑ sigma, f (sigma, phi)) / ((M : ℝ) * N) := by
  rw [ownerLaw, Law.expect_bind]
  simp_rw [Law.expect_map, Law.expect_uniform]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

theorem pair_owner_count (Q : ShortPath G D) (u w : V)
    (base Rmin : ℝ) (width M N : ℕ)
    (hw : 0 < width) (hD : 0 < D)
    (radius : V → Fin M × Fin N → ℝ)
    (hu : ∃ j : Fin Q.size, Within G u (Q.vertex j) Rmin)
    (hv : ∃ j : Fin Q.size, Within G w (Q.vertex j) Rmin)
    (hmin : ∀ v z, Rmin + D ≤ radius v z)
    (hrange : ∀ v (z : Fin M × Fin N),
      groupLower base width z.1 (shiftValue z.2) D ≤ radius v z ∧
      radius v z < groupUpper base width z.1 (shiftValue z.2) D) :
    (∑ phi : Fin N, (Finset.univ.filter fun sigma : Fin M =>
      KeepsAncestor Q u w (radius u (sigma, phi)) Rmin).card) +
    (∑ phi : Fin N, (Finset.univ.filter fun sigma : Fin M =>
      KeepsAncestor Q w u (radius w (sigma, phi)) Rmin).card) ≤ (M + 1) * N := by
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _phi : Fin N, (M + 1) := by
      apply Finset.sum_le_sum
      intro phi _
      let S := Finset.univ.filter fun sigma : Fin M =>
        KeepsAncestor Q u w (radius u (sigma, phi)) Rmin
      let T := Finset.univ.filter fun sigma : Fin M =>
        KeepsAncestor Q w u (radius w (sigma, phi)) Rmin
      let B := Finset.univ.filter fun sigma : Fin M =>
        InWindow (pairDistance G u w) (groupLower base width sigma (shiftValue phi) D)
          (groupUpper base width sigma (shiftValue phi) D)
      have hST : S ∩ T ⊆ B := by
        intro sigma hs
        obtain ⟨hS, hT⟩ := Finset.mem_inter.mp hs
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        exact keeps_pair_window Q u w (radius u (sigma, phi)) (radius w (sigma, phi))
          Rmin (groupLower base width sigma (shiftValue phi) D)
          (groupUpper base width sigma (shiftValue phi) D)
          hu hv (hmin u (sigma, phi)) (hmin w (sigma, phi))
          (hrange u (sigma, phi)).1 (hrange w (sigma, phi)).1
          (hrange u (sigma, phi)).2 (hrange w (sigma, phi)).2
          ⟨(Finset.mem_filter.mp hS).2, (Finset.mem_filter.mp hT).2⟩
      have hB : B.card ≤ 1 := group_bad_card_le_one base (shiftValue phi) D width hw hD _
      have hUnion : (S ∪ T).card ≤ M := by simpa using Finset.card_le_univ (S ∪ T)
      have hInter := (Finset.card_le_card hST).trans hB
      have hcard := Finset.card_union_add_card_inter S T
      change S.card + T.card ≤ M + 1
      omega
    _ = _ := by simp [Nat.mul_comm]

theorem keeps_probability_pair (Q : ShortPath G D) (u w : V)
    (base Rmin : ℝ) (width M N : ℕ)
    (hw : 0 < width) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (radius : V → Fin M × Fin N → ℝ)
    (hu : ∃ j : Fin Q.size, Within G u (Q.vertex j) Rmin)
    (hv : ∃ j : Fin Q.size, Within G w (Q.vertex j) Rmin)
    (hmin : ∀ v z, Rmin + D ≤ radius v z)
    (hrange : ∀ v (z : Fin M × Fin N),
      groupLower base width z.1 (shiftValue z.2) D ≤ radius v z ∧
      radius v z < groupUpper base width z.1 (shiftValue z.2) D) :
    (ownerLaw M N hM hN).prob (fun z => KeepsAncestor Q u w (radius u z) Rmin) +
      (ownerLaw M N hM hN).prob (fun z => KeepsAncestor Q w u (radius w z) Rmin) ≤
        1 + 1 / (M : ℝ) := by
  have he (v t : V) :
      (ownerLaw M N hM hN).prob (fun z => KeepsAncestor Q v t (radius v z) Rmin) =
        (∑ phi : Fin N, ((Finset.univ.filter fun sigma : Fin M =>
          KeepsAncestor Q v t (radius v (sigma, phi)) Rmin).card : ℝ)) /
          ((M : ℝ) * N) := by
    rw [Law.prob, expect_owner]
    congr 1
    apply Finset.sum_congr rfl
    intro phi _
    simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [he, he, ← add_div]
  have hc := pair_owner_count Q u w base Rmin width M N hw hD radius hu hv hmin hrange
  have hcr :
      (∑ phi : Fin N, ((Finset.univ.filter fun sigma : Fin M =>
          KeepsAncestor Q u w (radius u (sigma, phi)) Rmin).card : ℝ)) +
      (∑ phi : Fin N, ((Finset.univ.filter fun sigma : Fin M =>
          KeepsAncestor Q w u (radius w (sigma, phi)) Rmin).card : ℝ)) ≤
        ((M : ℝ) + 1) * N := by exact_mod_cast hc
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ (mul_pos hM' hN')).mpr
  have halg : (1 + 1 / (M : ℝ)) * ((M : ℝ) * N) = ((M : ℝ) + 1) * N := by
    field_simp
  rw [halg]
  exact hcr

end

end StreamingReachability.Early
