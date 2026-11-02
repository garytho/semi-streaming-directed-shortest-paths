module

public import StreamingSSSP.Early.Partition

@[expose] public section

namespace StreamingSSSP.Early

open scoped Classical

noncomputable section

namespace Cover

variable {V : Type*} [Fintype V] {n : ℕ}

def priority (C : V → Cut n) (p : V) : ℕ :=
  (C p).hi * (Fintype.card V + 1) + (Fintype.equivFin V p).val

theorem priority_lt (C : V → Cut n) {u v : V} (h : (C u).hi < (C v).hi) :
    priority C u < priority C v := by
  have hm := Nat.mul_le_mul_right (Fintype.card V + 1) (Nat.succ_le_of_lt h)
  have hu := (Fintype.equivFin V u).isLt
  rw [Nat.succ_mul] at hm
  unfold priority
  omega

theorem priority_injective (C : V → Cut n) : Function.Injective (priority C) := by
  intro u v he
  have hhi : (C u).hi = (C v).hi := by
    rcases lt_trichotomy (C u).hi (C v).hi with h | h | h
    · have := priority_lt C h
      omega
    · exact h
    · have := priority_lt C h
      omega
  have hidx : (Fintype.equivFin V u).val = (Fintype.equivFin V v).val := by
    unfold priority at he
    rw [hhi] at he
    omega
  exact (Fintype.equivFin V).injective (Fin.ext hidx)

def owner (P : Finset V) (C : V → Cut n) (i : ℕ) : Option V :=
  if h : (P.filter fun p => (C p).Contains i).Nonempty then
    some (Classical.choose (Finset.exists_max_image
      (P.filter fun p => (C p).Contains i) (priority C) h))
  else none

theorem owner_some_iff (P : Finset V) (C : V → Cut n) (i : ℕ) (p : V) :
    owner P C i = some p ↔ p ∈ P ∧ (C p).Contains i ∧
      ∀ v ∈ P, (C v).Contains i → priority C v ≤ priority C p := by
  unfold owner
  split_ifs with h
  · let a := Classical.choose (Finset.exists_max_image
      (P.filter fun p => (C p).Contains i) (priority C) h)
    have ha := Classical.choose_spec (Finset.exists_max_image
      (P.filter fun p => (C p).Contains i) (priority C) h)
    change some a = some p ↔ _
    constructor
    · intro he
      have hap : a = p := Option.some.inj he
      subst p
      exact ⟨(Finset.mem_filter.mp ha.1).1, (Finset.mem_filter.mp ha.1).2,
        fun v hv hvi => ha.2 v (Finset.mem_filter.mpr ⟨hv, hvi⟩)⟩
    · rintro ⟨hp, hpi, hmax⟩
      have hpa : priority C p ≤ priority C a :=
        ha.2 p (Finset.mem_filter.mpr ⟨hp, hpi⟩)
      have hap : priority C a ≤ priority C p :=
        hmax a (Finset.mem_filter.mp ha.1).1 (Finset.mem_filter.mp ha.1).2
      exact congrArg some (priority_injective C (Nat.le_antisymm hap hpa))
  · simp only [false_iff]
    rintro ⟨hp, hpi, _⟩
    exact h ⟨p, Finset.mem_filter.mpr ⟨hp, hpi⟩⟩

theorem owner_none_iff (P : Finset V) (C : V → Cut n) (i : ℕ) :
    owner P C i = none ↔ ∀ p ∈ P, ¬ (C p).Contains i := by
  unfold owner
  split_ifs with h
  · simp only [false_iff]
    intro hn
    obtain ⟨p, hp⟩ := h
    exact hn p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  · simp only [true_iff]
    intro p hp hpi
    exact h ⟨p, Finset.mem_filter.mpr ⟨hp, hpi⟩⟩

theorem owner_constant (P : Finset V) (C : V → Cut n)
    {I : ℕ × ℕ} (hI : I ∈ Cells.partition (boundaries P C) n)
    {i j : ℕ} (hi : Cells.Contains I i) (hj : Cells.Contains I j) :
    owner P C i = owner P C j := by
  cases he : owner P C i with
  | none =>
      have hn := (owner_none_iff P C i).mp he
      apply Eq.symm
      apply (owner_none_iff P C j).mpr
      intro p hp h
      exact hn p hp ((cut_constant hI hp hi hj).1.mpr h)
  | some p =>
      have hp := (owner_some_iff P C i p).mp he
      apply Eq.symm
      apply (owner_some_iff P C j p).mpr
      exact ⟨hp.1, (cut_constant hI hp.1 hi hj).1.mp hp.2.1,
        fun v hv hvj => hp.2.2 v hv ((cut_constant hI hv hi hj).1.mpr hvj)⟩

/-- Farthest-right ownership, with a fixed tie-breaker, never returns to a
pivot after leaving it. Thus each actual fringe needs at most one piece. -/
theorem owner_convex (P : Finset V) (C : V → Cut n)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) {p : V}
    (hi : owner P C i = some p) (hk : owner P C k = some p) :
    owner P C j = some p := by
  have hpi := (owner_some_iff P C i p).mp hi
  have hpk := (owner_some_iff P C k p).mp hk
  apply (owner_some_iff P C j p).mpr
  refine ⟨hpi.1, ⟨hpi.2.1.1.trans hij, hjk.trans_lt hpk.2.1.2⟩, ?_⟩
  intro v hv hvj
  by_cases hvk : k < (C v).hi
  · exact hpk.2.2 v hv ⟨hvj.1.trans hjk, hvk⟩
  · exact (priority_lt C (by have := hpk.2.1.2; omega)).le

def owners (P : Finset V) (C : V → Cut n) : Finset V :=
  P.filter fun p => ∃ i : Fin n, owner P C i.val = some p

def indices (P : Finset V) (C : V → Cut n) (p : V) : Finset ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun i => owner P C i.val = some p).image Fin.val

theorem indices_nonempty {P : Finset V} {C : V → Cut n} {p : V}
    (hp : p ∈ owners P C) : (indices P C p).Nonempty := by
  obtain ⟨_, i, hi⟩ := Finset.mem_filter.mp hp
  exact ⟨i.val, Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩⟩

def interval (P : Finset V) (C : V → Cut n) (p : V) : ℕ × ℕ :=
  if h : (indices P C p).Nonempty then
    ((indices P C p).min' h, (indices P C p).max' h + 1)
  else (0, 0)

theorem interval_bounds {P : Finset V} {C : V → Cut n} {p : V}
    (hp : p ∈ owners P C) :
    (interval P C p).1 < (interval P C p).2 ∧ (interval P C p).2 ≤ n := by
  have hn := indices_nonempty hp
  rw [interval, dite_eq_left hn]
  have hmin := Finset.min'_mem (indices P C p) hn
  have hmax := Finset.max'_mem (indices P C p) hn
  have hle := Finset.min'_le (indices P C p) _ hmax
  obtain ⟨i, _, hie⟩ := Finset.mem_image.mp hmax
  dsimp only
  constructor
  · omega
  · have := i.isLt
    omega

theorem interval_iff {P : Finset V} {C : V → Cut n} {p : V}
    (hp : p ∈ owners P C) (i : Fin n) :
    Cells.Contains (interval P C p) i.val ↔ owner P C i.val = some p := by
  have hn := indices_nonempty hp
  rw [interval, dite_eq_left hn]
  let a := (indices P C p).min' hn
  let b := (indices P C p).max' hn
  have ha := Finset.min'_mem (indices P C p) hn
  have hb := Finset.max'_mem (indices P C p) hn
  constructor
  · intro hi
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp ha
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hb
    apply owner_convex P C (i := j.val) (k := k.val) (by have := hi.1; omega)
      (by have := hi.2; omega) (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
  · intro hi
    have hm : i.val ∈ indices P C p := Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩
    exact ⟨Finset.min'_le _ _ hm, Nat.lt_succ_of_le (Finset.le_max' _ _ hm)⟩

def coreCells (P : Finset V) (C : V → Cut n) : Finset (ℕ × ℕ) :=
  (Cells.partition (boundaries P C) n).filter fun I => ∀ p ∈ P, ¬ (C p).Contains I.1

theorem owners_card_le_fringe_cells (P : Finset V) (C : V → Cut n) :
    (owners P C).card ≤
      (Cells.partition (boundaries P C) n \ coreCells P C).card := by
  have hsub : (owners P C).image some ⊆
      (Cells.partition (boundaries P C) n \ coreCells P C).image
        (fun I => owner P C I.1) := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨_, i, hi⟩ := Finset.mem_filter.mp hp
    obtain ⟨I, hI, hIi⟩ := Cells.cover
      (B := boundaries P C) (by simp [boundaries]) (by simp [boundaries]) i.isLt
    have he := (owner_constant P C hI ⟨le_rfl, (Cells.bounds hI).1⟩ hIi).trans hi
    apply Finset.mem_image.mpr
    refine ⟨I, Finset.mem_sdiff.mpr ⟨hI, ?_⟩, he⟩
    intro hc
    have hn := (owner_none_iff P C I.1).mpr (Finset.mem_filter.mp hc).2
    rw [he] at hn
    contradiction
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_image_le
    (s := Cells.partition (boundaries P C) n \ coreCells P C) (f := fun I => owner P C I.1)
  rw [Finset.card_image_of_injective _ (Option.some_injective V)] at h1
  omega

theorem piece_count (P : Finset V) (C : V → Cut n) :
    (coreCells P C).card + (owners P C).card ≤ 2 * P.card + 1 := by
  have h1 := owners_card_le_fringe_cells P C
  have hsub : coreCells P C ⊆ Cells.partition (boundaries P C) n :=
    Finset.filter_subset _ _
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  have h3 := partition_card P C
  omega

theorem piece_count_le_cells (P : Finset V) (C : V → Cut n) :
    (coreCells P C).card + (owners P C).card ≤
      (Cells.partition (boundaries P C) n).card := by
  have h1 := owners_card_le_fringe_cells P C
  have hsub : coreCells P C ⊆ Cells.partition (boundaries P C) n :=
    Finset.filter_subset _ _
  have h2 := Finset.card_sdiff_add_card_eq_card hsub
  omega

theorem cover (P : Finset V) (C : V → Cut n) (i : Fin n) :
    (∃ I ∈ coreCells P C, Cells.Contains I i.val) ∨
      ∃ p ∈ owners P C, Cells.Contains (interval P C p) i.val := by
  cases he : owner P C i.val with
  | none =>
      obtain ⟨I, hI, hIi⟩ := Cells.cover
        (B := boundaries P C) (by simp [boundaries]) (by simp [boundaries]) i.isLt
      left
      refine ⟨I, Finset.mem_filter.mpr ⟨hI, ?_⟩, hIi⟩
      apply (owner_none_iff P C I.1).mp
      exact (owner_constant P C hI ⟨le_rfl, (Cells.bounds hI).1⟩ hIi).trans he
  | some p =>
      have hp : p ∈ owners P C := Finset.mem_filter.mpr
        ⟨((owner_some_iff P C i.val p).mp he).1, i, he⟩
      exact Or.inr ⟨p, hp, (interval_iff hp i).mpr he⟩

theorem fringe_disjoint {P : Finset V} {C : V → Cut n} {p q : V}
    (hp : p ∈ owners P C) (hq : q ∈ owners P C) (hne : p ≠ q)
    (i : Fin n) :
    ¬ (Cells.Contains (interval P C p) i.val ∧
      Cells.Contains (interval P C q) i.val) := by
  rintro ⟨hi, hj⟩
  exact hne (Option.some.inj (((interval_iff hp i).mp hi).symm.trans
    ((interval_iff hq i).mp hj)))

theorem core_fringe_disjoint {P : Finset V} {C : V → Cut n}
    {I : ℕ × ℕ} (hI : I ∈ coreCells P C) {p : V} (hp : p ∈ owners P C)
    (i : Fin n) :
    ¬ (Cells.Contains I i.val ∧ Cells.Contains (interval P C p) i.val) := by
  rintro ⟨hi, hj⟩
  obtain ⟨hIp, hIc⟩ := Finset.mem_filter.mp hI
  have hn := (owner_none_iff P C I.1).mpr hIc
  have he := (owner_constant P C hIp ⟨le_rfl, (Cells.bounds hIp).1⟩ hi).symm.trans hn
  rw [(interval_iff hp i).mp hj] at he
  contradiction

end Cover

variable {V : Type*} [Fintype V] {G : Graph V} {D : ℝ}

def fringeOwners (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ) : Finset V :=
  Cover.owners P fun p => pivotCut Q p (rho p) R

def fringeInterval (Q : ShortPath G D) (P : Finset V) (rho : V → ℝ) (R : ℝ)
    (p : V) : ℕ × ℕ :=
  Cover.interval P (fun p => pivotCut Q p (rho p) R) p

theorem grouped_type1_count (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ) (hrho : ∀ p ∈ P, rho p ≤ R) :
    (corePieces Q P rho R).card + (fringeOwners Q P rho R).card ≤
      2 * (nearPivots Q P R).card + 1 :=
  (Cover.piece_count_le_cells P (fun p => pivotCut Q p (rho p) R)).trans
    (type1_near_card Q P rho R hrho)

theorem grouped_type1_count_at (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R T : ℝ) (hrho : ∀ p ∈ P, rho p ≤ T) :
    (corePieces Q P rho R).card + (fringeOwners Q P rho R).card ≤
      2 * (nearPivots Q P T).card + 1 :=
  (Cover.piece_count_le_cells P (fun p => pivotCut Q p (rho p) R)).trans
    (type1_near_card_at Q P rho R T hrho)

theorem fringe_owner_near (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R T : ℝ) (hrho : ∀ p ∈ P, rho p ≤ T)
    {p : V} (hp : p ∈ fringeOwners Q P rho R) : Near Q p T := by
  obtain ⟨hpP, i, hi⟩ := Finset.mem_filter.mp hp
  have hc := (Cover.owner_some_iff P (fun p => pivotCut Q p (rho p) R) i.val p).mp hi
  rcases cut_contains_related Q p (rho p) R hc.2.1 with h | h
  · exact Or.inl (h.imp fun _ hj => within_mono hj (hrho p hpP))
  · exact Or.inr (h.imp fun _ hj => within_mono hj (hrho p hpP))

theorem grouped_type1_cover (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ) (i : Fin Q.size) :
    (∃ I ∈ corePieces Q P rho R, Cells.Contains I i.val) ∨
      ∃ p ∈ fringeOwners Q P rho R, Cells.Contains (fringeInterval Q P rho R p) i.val :=
  Cover.cover P (fun p => pivotCut Q p (rho p) R) i

theorem grouped_fringe_contained (Q : ShortPath G D) (P : Finset V)
    (rho : V → ℝ) (R : ℝ)
    (hnb : ∀ p ∈ P, ¬ Bridge Q p R) (hrho : ∀ p ∈ P, rho p - D ≤ R)
    {p : V} (hp : p ∈ fringeOwners Q P rho R)
    {i : Fin Q.size} (hi : Cells.Contains (fringeInterval Q P rho R p) i.val) :
    Q.vertex i ∈ fringe G p (rho p) D := by
  have he := (Cover.interval_iff hp i).mp hi
  have hs := (Cover.owner_some_iff P (fun p => pivotCut Q p (rho p) R) i.val p).mp he
  exact pivot_fringe Q p (rho p) R (hnb p hs.1) (hrho p hs.1) hs.2.1

end

end StreamingSSSP.Early
