module

public import StreamingReachability.Early.Knockout

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

variable {V : Type*} [Fintype V]

theorem bothBall_mono (G : Graph V) (p : V) {R S : ℝ} (hRS : R ≤ S) :
    bothBall G p R ⊆ bothBall G p S := by
  intro v hv
  exact (mem_bothBall _ _ _ _).mpr
    (((mem_bothBall _ _ _ _).mp hv).elim
      (fun h => Or.inl (within_mono h hRS)) (fun h => Or.inr (within_mono h hRS)))

theorem fringe_disjoint_of_gap (G : Graph V) (p : V) (rho tau D : ℝ)
    (hgap : rho + D ≤ tau - D) :
    Disjoint (fringe G p rho D) (fringe G p tau D) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact (Finset.mem_sdiff.mp hw).2
    (bothBall_mono G p hgap (Finset.mem_sdiff.mp hv).1)

theorem candidateIndex_injective (width M : ℕ) :
    Function.Injective (fun z : Fin M × Fin width => width * z.1.val + z.2.val) := by
  intro z t he
  dsimp only at he
  have hfst : z.1.val = t.1.val := by
    rcases lt_trichotomy z.1.val t.1.val with h | h | h
    · have hmul := Nat.mul_le_mul_left width (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hmul
      have hz := z.2.isLt
      omega
    · exact h
    · have hmul := Nat.mul_le_mul_left width (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at hmul
      have ht := t.2.isLt
      omega
  have hsnd : z.2.val = t.2.val := by rw [hfst] at he; omega
  exact Prod.ext (Fin.ext hfst) (Fin.ext hsnd)

/-- This count is independent of the minimization rule and of the shift. -/
theorem shell_membership_count {I : Type*} (S : Finset I) (index : I → ℕ)
    (hinj : Set.InjOn index S) (G : Graph V) (p v : V)
    (base shift D : ℝ) (hD : 0 < D) :
    (S.filter fun i => v ∈ fringe G p ((base + index i + shift) * D) D).card ≤ 2 := by
  let T := S.filter fun i => v ∈ fringe G p ((base + index i + shift) * D) D
  let U := T.image index
  have hcard : U.card = T.card :=
    Finset.card_image_of_injOn (fun i hi j hj he =>
      hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 he)
  by_cases hU : U.Nonempty
  · let a := U.min' hU
    have ha : a ∈ U := Finset.min'_mem _ _
    obtain ⟨i, hi, hie⟩ := Finset.mem_image.mp ha
    have hsub : U ⊆ Finset.Icc a (a + 1) := by
      intro b hb
      have hab : a ≤ b := Finset.min'_le _ _ hb
      refine Finset.mem_Icc.mpr ⟨hab, ?_⟩
      by_contra hn
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hb
      have hgap : (base + index i + shift) * D + D ≤
          (base + index j + shift) * D - D := by
        have hnat : index i + 2 ≤ index j := by omega
        have hreal : (index i : ℝ) + 2 ≤ index j := by exact_mod_cast hnat
        nlinarith
      have hd := fringe_disjoint_of_gap G p _ _ D hgap
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hi).2
        (Finset.mem_filter.mp hj).2
    have hc := Finset.card_le_card hsub
    rw [hcard] at hc
    rw [Nat.card_Icc] at hc
    change T.card ≤ 2
    omega
  · have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    rw [he, Finset.card_empty] at hcard
    change T.card ≤ 2
    omega

omit [Fintype V] in
theorem sum_card_eq_count {I : Type*} (S : Finset I) (B : Finset V)
    (F : I → Finset V) (hF : ∀ i ∈ S, F i ⊆ B) :
    ∑ i ∈ S, (F i).card = ∑ v ∈ B, (S.filter fun i => v ∈ F i).card := by
  have hc (i : I) (hi : i ∈ S) :
      (F i).card = ∑ v ∈ B, if v ∈ F i then 1 else 0 := by
    rw [← Finset.card_filter]
    congr 1
    ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hF i hi h, h⟩, fun h => h.2⟩
  calc
    _ = ∑ i ∈ S, ∑ v ∈ B, if v ∈ F i then 1 else 0 :=
      Finset.sum_congr rfl hc
    _ = ∑ v ∈ B, ∑ i ∈ S, if v ∈ F i then 1 else 0 := Finset.sum_comm
    _ = _ := by simp only [Finset.card_filter]

theorem total_shell_size {I : Type*} (S : Finset I) (index : I → ℕ)
    (hinj : Set.InjOn index S) (G : Graph V) (p : V)
    (base shift D R : ℝ) (hD : 0 < D)
    (hR : ∀ i ∈ S, (base + index i + shift) * D + D ≤ R) :
    ∑ i ∈ S, (fringe G p ((base + index i + shift) * D) D).card ≤
      2 * (bothBall G p R).card := by
  rw [sum_card_eq_count S (bothBall G p R) _ (by
    intro i hi v hv
    exact bothBall_mono G p (hR i hi) (Finset.mem_sdiff.mp hv).1)]
  calc
    _ ≤ ∑ _v ∈ bothBall G p R, 2 :=
      Finset.sum_le_sum fun v _ => shell_membership_count S index hinj G p v base shift D hD
    _ = _ := by simp [Nat.mul_comm]

def minimumIndex {width : ℕ} (hw : 0 < width) (f : Fin width → ℕ) : Fin width :=
  Classical.choose (Finset.exists_min_image Finset.univ f
    ⟨⟨0, hw⟩, Finset.mem_univ _⟩)

theorem minimumIndex_le {width : ℕ} (hw : 0 < width) (f : Fin width → ℕ)
    (j : Fin width) : f (minimumIndex hw f) ≤ f j :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ f
    ⟨⟨0, hw⟩, Finset.mem_univ _⟩)).2 j (Finset.mem_univ j)

def minimumShellIndex (G : Graph V) (p : V) (base D shift : ℝ)
    (width : ℕ) (hw : 0 < width) {M : ℕ} (sigma : Fin M) : Fin width :=
  minimumIndex hw fun j => (fringe G p (candidateRadius base width sigma j shift D) D).card

def minimumShell (G : Graph V) (p : V) (base D shift : ℝ)
    (width : ℕ) (hw : 0 < width) {M : ℕ} (sigma : Fin M) : Finset V :=
  fringe G p (candidateRadius base width sigma
    (minimumShellIndex G p base D shift width hw sigma) shift D) D

theorem minimum_shell_size_sum (G : Graph V) (p : V) (base D shift R : ℝ)
    (width M : ℕ) (hw : 0 < width) (hD : 0 < D)
    (hR : ∀ (sigma : Fin M) (j : Fin width),
      candidateRadius base width sigma j shift D + D ≤ R) :
    width * (∑ sigma : Fin M, (minimumShell G p base D shift width hw sigma).card) ≤
      2 * (bothBall G p R).card := by
  have hall := total_shell_size (Finset.univ : Finset (Fin M × Fin width))
    (fun z => width * z.1.val + z.2.val)
    (fun _ _ _ _ he => candidateIndex_injective width M he) G p base shift D R hD (by
      intro z _
      simpa only [candidateRadius, Nat.cast_add, Nat.cast_mul, add_assoc] using hR z.1 z.2)
  have hmin (sigma : Fin M) (j : Fin width) :
      (minimumShell G p base D shift width hw sigma).card ≤
        (fringe G p (candidateRadius base width sigma j shift D) D).card :=
    minimumIndex_le hw
      (fun j => (fringe G p (candidateRadius base width sigma j shift D) D).card) j
  calc
    _ = ∑ sigma : Fin M, ∑ _j : Fin width,
        (minimumShell G p base D shift width hw sigma).card := by
      simp [Finset.mul_sum]
    _ ≤ ∑ sigma : Fin M, ∑ j : Fin width,
        (fringe G p (candidateRadius base width sigma j shift D) D).card :=
      Finset.sum_le_sum fun sigma _ => Finset.sum_le_sum fun j _ => hmin sigma j
    _ = ∑ z : Fin M × Fin width,
        (fringe G p ((base + (width * z.1.val + z.2.val : ℕ) + shift) * D) D).card := by
      rw [Fintype.sum_prod_type]
      simp only [candidateRadius, Nat.cast_add, Nat.cast_mul, add_assoc]
    _ ≤ _ := hall

theorem expected_minimum_shell (G : Graph V) (p : V) (base D shift R : ℝ)
    (width M : ℕ) (hw : 0 < width) (hM : 0 < M) (hD : 0 < D)
    (hR : ∀ (sigma : Fin M) (j : Fin width),
      candidateRadius base width sigma j shift D + D ≤ R) :
    (Law.uniform M hM).expect
      (fun sigma => ((minimumShell G p base D shift width hw sigma).card : ℝ)) ≤
      2 * (bothBall G p R).card / ((width : ℝ) * M) := by
  rw [Law.expect_uniform]
  have hnat := minimum_shell_size_sum G p base D shift R width M hw hD hR
  have hreal : (width : ℝ) *
      (∑ sigma : Fin M, ((minimumShell G p base D shift width hw sigma).card : ℝ)) ≤
      2 * (bothBall G p R).card := by exact_mod_cast hnat
  have hw' : (0 : ℝ) < width := by exact_mod_cast hw
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  apply (div_le_iff₀ hM').mpr
  have he : (2 * (bothBall G p R).card / ((width : ℝ) * M)) * M =
      2 * (bothBall G p R).card / (width : ℝ) := by
    field_simp
  rw [he]
  exact (le_div_iff₀ hw').mpr (by nlinarith)

theorem expected_shifted_minimum_shell (G : Graph V) (p : V) (base D R : ℝ)
    (width M N : ℕ) (hw : 0 < width) (hM : 0 < M) (hN : 0 < N) (hD : 0 < D)
    (hR : ∀ (sigma : Fin M) (phi : Fin N) (j : Fin width),
      candidateRadius base width sigma j (shiftValue phi) D + D ≤ R) :
    (ownerLaw M N hM hN).expect (fun z =>
      ((minimumShell G p base D (shiftValue z.2) width hw z.1).card : ℝ)) ≤
      2 * (bothBall G p R).card / ((width : ℝ) * M) := by
  rw [ownerLaw, Law.expect_bind]
  calc
    _ ≤ (Law.uniform N hN).expect (fun _ =>
        2 * (bothBall G p R).card / ((width : ℝ) * M)) := by
      apply Law.expect_mono
      intro phi
      rw [Law.expect_map]
      exact expected_minimum_shell G p base D (shiftValue phi) R width M hw hM hD
        (fun sigma j => hR sigma phi j)
    _ = _ := Law.expect_const _ _

end

end StreamingReachability.Early
