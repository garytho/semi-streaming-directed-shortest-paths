module

public import StreamingReachability.Early.Intervals

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

def ancestorCut (Q : ShortPath G D) (p : V) (rho : ℝ) : Cut Q.size where
  lo := Index.first fun i => Within G p (Q.vertex i) rho
  hi := Index.first fun i => Within G p (Q.vertex i) (rho - D)
  ordered := Index.first_mono fun _ h => within_mono h (by linarith [Q.scale_nonneg])
  bounded := Index.first_le_size _
  ancestor := true

def descendantCut (Q : ShortPath G D) (p : V) (rho : ℝ) : Cut Q.size where
  lo := Index.lastPlus fun i => Within G (Q.vertex i) p (rho - D)
  hi := Index.lastPlus fun i => Within G (Q.vertex i) p rho
  ordered := Index.lastPlus_mono fun _ h => within_mono h (by linarith [Q.scale_nonneg])
  bounded := Index.lastPlus_le_size _
  ancestor := false

def pivotCut (Q : ShortPath G D) (p : V) (rho R : ℝ) : Cut Q.size :=
  if ∃ i : Fin Q.size, Within G p (Q.vertex i) R
  then ancestorCut Q p rho else descendantCut Q p rho

theorem ancestor_suffix (Q : ShortPath G D) (p : V) (rho : ℝ)
    {i : Fin Q.size} (hi : (ancestorCut Q p rho).hi ≤ i.val) :
    Within G p (Q.vertex i) rho := by
  have hc : (ancestorCut Q p rho).hi < Q.size := hi.trans_lt i.isLt
  have hk := Index.first_mem (P := fun j => Within G p (Q.vertex j) (rho - D)) hc
  have hki : (⟨(ancestorCut Q p rho).hi, hc⟩ : Fin Q.size) ≤ i := hi
  have ht := within_trans hk (Q.forward hki)
  simpa only [sub_add_cancel] using ht

theorem descendant_prefix (Q : ShortPath G D) (p : V) (rho : ℝ)
    {i : Fin Q.size} (hi : i.val < (descendantCut Q p rho).lo) :
    Within G (Q.vertex i) p rho := by
  change i.val < Index.lastPlus (fun j => Within G (Q.vertex j) p (rho - D)) at hi
  obtain ⟨j, hj, hje⟩ := Index.lastPlus_mem
    (P := fun j => Within G (Q.vertex j) p (rho - D)) (by omega)
  have hij : i ≤ j := by change i.val ≤ j.val; omega
  have ht := within_trans (Q.forward hij) hj
  convert ht using 1
  ring

theorem ancestor_fringe (Q : ShortPath G D) (p : V) (rho R : ℝ)
    (hback : ∀ i : Fin Q.size, ¬ Within G (Q.vertex i) p R)
    (hR : rho - D ≤ R) {i : Fin Q.size}
    (hi : (ancestorCut Q p rho).Contains i.val) :
    Q.vertex i ∈ fringe G p rho D := by
  have hf : (ancestorCut Q p rho).lo < Q.size := hi.1.trans_lt i.isLt
  have hk := Index.first_mem (P := fun j => Within G p (Q.vertex j) rho) hf
  have hki : (⟨(ancestorCut Q p rho).lo, hf⟩ : Fin Q.size) ≤ i := hi.1
  have hout := within_trans hk (Q.forward hki)
  apply (mem_fringe _ _ _ _ _).mpr
  refine ⟨Or.inl hout, ?_⟩
  rintro (hin | hin)
  · exact Index.not_before_first hi.2 hin
  · exact hback i (within_mono hin hR)

theorem descendant_fringe (Q : ShortPath G D) (p : V) (rho R : ℝ)
    (hback : ∀ i : Fin Q.size, ¬ Within G p (Q.vertex i) R)
    (hR : rho - D ≤ R) {i : Fin Q.size}
    (hi : (descendantCut Q p rho).Contains i.val) :
    Q.vertex i ∈ fringe G p rho D := by
  change Index.lastPlus (fun j => Within G (Q.vertex j) p (rho - D)) ≤ i.val ∧
    i.val < Index.lastPlus (fun j => Within G (Q.vertex j) p rho) at hi
  obtain ⟨j, hj, hje⟩ := Index.lastPlus_mem
    (P := fun j => Within G (Q.vertex j) p rho) (by have := hi.2; omega)
  have hij : i ≤ j := by have := hi.2; change i.val ≤ j.val; omega
  have hout := within_trans (Q.forward hij) hj
  apply (mem_fringe _ _ _ _ _).mpr
  refine ⟨Or.inr (by simpa only [add_comm] using hout), ?_⟩
  rintro (hin | hin)
  · exact hback i (within_mono hin hR)
  · exact Index.not_after_lastPlus hi.1 hin

theorem pivot_fringe (Q : ShortPath G D) (p : V) (rho R : ℝ)
    (hnb : ¬ Bridge Q p R) (hR : rho - D ≤ R)
    {i : Fin Q.size} (hi : (pivotCut Q p rho R).Contains i.val) :
    Q.vertex i ∈ fringe G p rho D := by
  unfold pivotCut at hi
  split_ifs at hi with ha
  · apply ancestor_fringe Q p rho R (fun j hj => hnb ⟨ha, ⟨j, hj⟩⟩) hR hi
  · apply descendant_fringe Q p rho R (fun j hj => ha ⟨j, hj⟩) hR hi

theorem pivot_labels (Q : ShortPath G D) (p : V) (rho R : ℝ)
    (hnb : ¬ Bridge Q p R) (hR : rho ≤ R)
    {i : Fin Q.size} (hi : ¬ (pivotCut Q p rho R).Contains i.val) :
    (Within G (Q.vertex i) p rho ↔
      (pivotCut Q p rho R).ancestor = false ∧ (pivotCut Q p rho R).bit i.val) ∧
    (Within G p (Q.vertex i) rho ↔
      (pivotCut Q p rho R).ancestor = true ∧ (pivotCut Q p rho R).bit i.val) := by
  unfold pivotCut at hi ⊢
  split_ifs at hi ⊢ with ha
  · have hn : ¬ Within G (Q.vertex i) p rho :=
      fun h => hnb ⟨ha, ⟨i, within_mono h hR⟩⟩
    have he : Within G p (Q.vertex i) rho ↔ (ancestorCut Q p rho).hi ≤ i.val := by
      constructor
      · intro h
        have hf := Index.first_le (P := fun j => Within G p (Q.vertex j) rho) h
        have := hi
        change ¬ ((ancestorCut Q p rho).lo ≤ i.val ∧
          i.val < (ancestorCut Q p rho).hi) at this
        change (ancestorCut Q p rho).lo ≤ i.val at hf
        omega
      · exact ancestor_suffix Q p rho
    constructor
    · simp [ancestorCut, hn]
    · simpa [ancestorCut, Cut.bit] using he
  · have hn : ¬ Within G p (Q.vertex i) rho :=
      fun h => ha ⟨i, within_mono h hR⟩
    have he : Within G (Q.vertex i) p rho ↔ i.val < (descendantCut Q p rho).lo := by
      constructor
      · intro h
        have hf := Index.lt_lastPlus (P := fun j => Within G (Q.vertex j) p rho) h
        have := hi
        change ¬ ((descendantCut Q p rho).lo ≤ i.val ∧
          i.val < (descendantCut Q p rho).hi) at this
        change i.val < (descendantCut Q p rho).hi at hf
        omega
      · exact descendant_prefix Q p rho
    constructor
    · simpa [descendantCut, Cut.bit] using he
    · simp [descendantCut, hn]

def smoothLabels {n : ℕ} (P : Finset V) (C : V → Cut n) (i : ℕ) :
    Finset V × Finset V :=
  (P.filter fun p => (C p).ancestor = false ∧ (C p).bit i,
   P.filter fun p => (C p).ancestor = true ∧ (C p).bit i)

omit [Fintype V] in
theorem smoothLabels_union {n : ℕ} (P : Finset V) (C : V → Cut n) (i : ℕ) :
    (smoothLabels P C i).1 ∪ (smoothLabels P C i).2 = signature P C i := by
  ext p
  cases h : (C p).ancestor <;> simp [smoothLabels, signature, h]

omit [Fintype V] in
theorem smoothLabels_constant {n : ℕ} {P : Finset V} {C : V → Cut n}
    {I : ℕ × ℕ} (hI : I ∈ Cells.partition (boundaries P C) n)
    {i j : ℕ} (hi : Cells.Contains I i) (hj : Cells.Contains I j) :
    smoothLabels P C i = smoothLabels P C j := by
  apply Prod.ext <;> ext p <;> simp only [smoothLabels, Finset.mem_filter]
  · exact and_congr_right fun hp => and_congr_right fun _ => (cut_constant hI hp hi hj).2
  · exact and_congr_right fun hp => and_congr_right fun _ => (cut_constant hI hp hi hj).2

def type1Pieces (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    Finset (ℕ × ℕ) :=
  Cells.partition (boundaries P fun p => pivotCut Q p (rho p) R) Q.size

def corePieces (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    Finset (ℕ × ℕ) :=
  (type1Pieces Q P rho R).filter fun I => ∀ p ∈ P,
    ¬ (pivotCut Q p (rho p) R).Contains I.1

theorem type1_card (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) :
    (type1Pieces Q P rho R).card ≤ 2 * P.card + 1 :=
  partition_card _ _

theorem type1_cover (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ)
    (i : Fin Q.size) :
    ∃! I, I ∈ type1Pieces Q P rho R ∧ Cells.Contains I i.val := by
  obtain ⟨I, hI, hi⟩ := Cells.cover
    (B := boundaries P fun p => pivotCut Q p (rho p) R)
    (by simp [boundaries]) (by simp [boundaries]) i.isLt
  exact ⟨I, ⟨hI, hi⟩, fun J hJ => Cells.overlap_eq hJ.1 hI hJ.2 hi⟩

theorem core_piece_labels (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ)
    (hnb : ∀ p ∈ P, ¬ Bridge Q p R) (hrho : ∀ p ∈ P, rho p ≤ R)
    {I : ℕ × ℕ} (hI : I ∈ corePieces Q P rho R)
    {i : Fin Q.size} (hi : Cells.Contains I i.val) :
    labels G P rho (Q.vertex i) =
      smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1 := by
  obtain ⟨hIp, hIc⟩ := Finset.mem_filter.mp hI
  have hout (p : V) (hp : p ∈ P) : ¬ (pivotCut Q p (rho p) R).Contains i.val :=
    fun h => hIc p hp ((cut_constant hIp hp
      ⟨le_rfl, (Cells.bounds hIp).1⟩ hi).1.mpr h)
  have he : labels G P rho (Q.vertex i) =
      smoothLabels P (fun p => pivotCut Q p (rho p) R) i.val := by
    apply Prod.ext <;> ext p <;> simp only [labels, smoothLabels, Finset.mem_filter]
    · exact and_congr_right fun hp => (pivot_labels Q p (rho p) R
        (hnb p hp) (hrho p hp) (hout p hp)).1
    · exact and_congr_right fun hp => (pivot_labels Q p (rho p) R
        (hnb p hp) (hrho p hp) (hout p hp)).2
  exact he.trans (smoothLabels_constant hIp hi ⟨le_rfl, (Cells.bounds hIp).1⟩)

theorem core_piece_contained (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ)
    (hnb : ∀ p ∈ P, ¬ Bridge Q p R) (hrho : ∀ p ∈ P, rho p ≤ R)
    {I : ℕ × ℕ} (hI : I ∈ corePieces Q P rho R)
    {i : Fin Q.size} (hi : Cells.Contains I i.val) :
    Q.vertex i ∈ coreClass G P rho
      (smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1) :=
  ⟨no_bridge_remaining Q P rho hrho hnb i, core_piece_labels Q P rho R hnb hrho hI hi⟩

theorem fringe_piece_contained (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ)
    (hnb : ∀ p ∈ P, ¬ Bridge Q p R) (hrho : ∀ p ∈ P, rho p - D ≤ R)
    {I : ℕ × ℕ} (hI : I ∈ type1Pieces Q P rho R)
    (hIc : I ∉ corePieces Q P rho R) :
    ∃ p ∈ P, ∀ i : Fin Q.size, Cells.Contains I i.val →
      Q.vertex i ∈ fringe G p (rho p) D := by
  rcases partition_classify hI with ⟨p, hp, hpf⟩ | hc
  · exact ⟨p, hp, fun i hi => pivot_fringe Q p (rho p) R
      (hnb p hp) (hrho p hp) (hpf i.val hi)⟩
  · exact False.elim (hIc (Finset.mem_filter.mpr
      ⟨hI, fun p hp => hc p hp I.1 ⟨le_rfl, (Cells.bounds hI).1⟩⟩))

theorem core_piece_classes_distinct (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ)
    {I J : ℕ × ℕ} (hI : I ∈ corePieces Q P rho R)
    (hJ : J ∈ corePieces Q P rho R)
    (he : smoothLabels P (fun p => pivotCut Q p (rho p) R) I.1 =
      smoothLabels P (fun p => pivotCut Q p (rho p) R) J.1) : I = J := by
  obtain ⟨hIp, hIc⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJp, hJc⟩ := Finset.mem_filter.mp hJ
  apply core_signatures_distinct hIp hJp hIc hJc
  rw [← smoothLabels_union, ← smoothLabels_union, he]

def Near (Q : ShortPath G D) (p : V) (R : ℝ) : Prop :=
  (∃ i : Fin Q.size, Within G p (Q.vertex i) R) ∨
  (∃ i : Fin Q.size, Within G (Q.vertex i) p R)

def nearPivots (Q : ShortPath G D) (P : Finset V) (R : ℝ) : Finset V :=
  P.filter fun p => Near Q p R

theorem inactive_cut (Q : ShortPath G D) (p : V) (rho R : ℝ)
    (hnear : ¬ Near Q p R) (hrho : rho ≤ R) :
    (pivotCut Q p rho R).lo = 0 ∧ (pivotCut Q p rho R).hi = 0 := by
  have hout : ¬ ∃ i : Fin Q.size, Within G p (Q.vertex i) R :=
    fun h => hnear (Or.inl h)
  have hin : ∀ i : Fin Q.size, ¬ Within G (Q.vertex i) p R :=
    fun i h => hnear (Or.inr ⟨i, h⟩)
  simp only [pivotCut, hout, ↓reduceIte, descendantCut]
  exact ⟨Index.lastPlus_eq_zero (fun i h =>
      hin i (within_mono h (by linarith [Q.scale_nonneg]))),
    Index.lastPlus_eq_zero (fun i h => hin i (within_mono h hrho))⟩

theorem type1_near_card (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ) (hrho : ∀ p ∈ P, rho p ≤ R) :
    (type1Pieces Q P rho R).card ≤ 2 * (nearPivots Q P R).card + 1 := by
  let C := fun p => pivotCut Q p (rho p) R
  have hsub : boundaries P C ⊆ boundaries (nearPivots Q P R) C := by
    intro k hk
    simp only [boundaries, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hk ⊢
    rcases hk with rfl | rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · by_cases hn : Near Q p R
      · exact Or.inr (Or.inr (Or.inl ⟨p, by simp [nearPivots, hp, hn], rfl⟩))
      · exact Or.inl (inactive_cut Q p (rho p) R hn (hrho p hp)).1
    · by_cases hn : Near Q p R
      · exact Or.inr (Or.inr (Or.inr ⟨p, by simp [nearPivots, hp, hn], rfl⟩))
      · exact Or.inl (inactive_cut Q p (rho p) R hn (hrho p hp)).2
  have h1 := Cells.card_le (B := boundaries P C) (n := Q.size) (by simp [boundaries])
  have h2 := Finset.card_le_card hsub
  have h3 := boundaries_card (nearPivots Q P R) C
  change (Cells.partition (boundaries P C) Q.size).card ≤ _
  omega

theorem unrelated_cut_endpoints (Q : ShortPath G D) (p : V) (rho R T : ℝ)
    (hnear : ¬ Near Q p T) (hrho : rho ≤ T) :
    ((pivotCut Q p rho R).lo = 0 ∧ (pivotCut Q p rho R).hi = 0) ∨
      ((pivotCut Q p rho R).lo = Q.size ∧ (pivotCut Q p rho R).hi = Q.size) := by
  have hout : ∀ i : Fin Q.size, ¬ Within G p (Q.vertex i) rho :=
    fun i h => hnear (Or.inl ⟨i, within_mono h hrho⟩)
  have hin : ∀ i : Fin Q.size, ¬ Within G (Q.vertex i) p rho :=
    fun i h => hnear (Or.inr ⟨i, within_mono h hrho⟩)
  unfold pivotCut
  split_ifs
  · right
    exact ⟨Index.first_eq_size hout, Index.first_eq_size
      (fun i h => hout i (within_mono h (by linarith [Q.scale_nonneg])))⟩
  · left
    exact ⟨Index.lastPlus_eq_zero
      (fun i h => hin i (within_mono h (by linarith [Q.scale_nonneg]))),
      Index.lastPlus_eq_zero hin⟩

theorem type1_near_card_at (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R T : ℝ) (hrho : ∀ p ∈ P, rho p ≤ T) :
    (type1Pieces Q P rho R).card ≤ 2 * (nearPivots Q P T).card + 1 := by
  let C := fun p => pivotCut Q p (rho p) R
  have hsub : boundaries P C ⊆ boundaries (nearPivots Q P T) C := by
    intro k hk
    simp only [boundaries, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hk ⊢
    rcases hk with rfl | rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · by_cases hn : Near Q p T
      · exact Or.inr (Or.inr (Or.inl ⟨p, by simp [nearPivots, hp, hn], rfl⟩))
      · rcases unrelated_cut_endpoints Q p (rho p) R T hn (hrho p hp) with h | h
        · exact Or.inl h.1
        · exact Or.inr (Or.inl h.1)
    · by_cases hn : Near Q p T
      · exact Or.inr (Or.inr (Or.inr ⟨p, by simp [nearPivots, hp, hn], rfl⟩))
      · rcases unrelated_cut_endpoints Q p (rho p) R T hn (hrho p hp) with h | h
        · exact Or.inl h.2
        · exact Or.inr (Or.inl h.2)
  have h1 := Cells.card_le (B := boundaries P C) (n := Q.size) (by simp [boundaries])
  have h2 := Finset.card_le_card hsub
  have h3 := boundaries_card (nearPivots Q P T) C
  change (Cells.partition (boundaries P C) Q.size).card ≤ _
  omega

theorem cut_contains_related (Q : ShortPath G D) (p : V) (rho R : ℝ)
    {i : Fin Q.size} (hi : (pivotCut Q p rho R).Contains i.val) : Near Q p rho := by
  unfold pivotCut at hi
  split_ifs at hi
  · left
    have hf : (ancestorCut Q p rho).lo < Q.size := hi.1.trans_lt i.isLt
    exact ⟨⟨_, hf⟩, Index.first_mem hf⟩
  · right
    have hf : 0 < Index.lastPlus (fun j => Within G (Q.vertex j) p rho) := by
      change (descendantCut Q p rho).hi > 0
      have := hi.2
      omega
    obtain ⟨j, hj, _⟩ := Index.lastPlus_mem hf
    exact ⟨j, hj⟩

end

end StreamingReachability.Early
