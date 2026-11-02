module

public import StreamingReachability.Early.Geometry

@[expose] public section

namespace StreamingReachability.Early

open scoped Classical BigOperators

noncomputable section

namespace Index

def first {n : ℕ} (P : Fin n → Prop) : ℕ :=
  (insert n ((Finset.univ.filter P).image Fin.val)).min' (by simp)

theorem first_le_size {n : ℕ} (P : Fin n → Prop) : first P ≤ n :=
  Finset.min'_le _ _ (by simp)

theorem first_le {n : ℕ} {P : Fin n → Prop} {i : Fin n} (hi : P i) :
    first P ≤ i.val := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩)

theorem first_mem {n : ℕ} {P : Fin n → Prop} (h : first P < n) :
    P ⟨first P, h⟩ := by
  have hm := Finset.min'_mem (insert n ((Finset.univ.filter P).image Fin.val))
    (by simp)
  rcases Finset.mem_insert.mp hm with he | hm
  · exact False.elim (by unfold first at h; omega)
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    have hie : i = ⟨first P, h⟩ := Fin.ext he
    simpa [hie] using (Finset.mem_filter.mp hi).2

theorem not_before_first {n : ℕ} {P : Fin n → Prop} {i : Fin n}
    (hi : i.val < first P) : ¬ P i :=
  fun h => (Nat.not_lt_of_ge (first_le h)) hi

theorem first_mono {n : ℕ} {P S : Fin n → Prop}
    (h : ∀ i, P i → S i) : first S ≤ first P := by
  by_cases hn : first P < n
  · exact first_le (h _ (first_mem hn))
  · exact (first_le_size S).trans (by have := first_le_size P; omega)

theorem first_eq_size {n : ℕ} {P : Fin n → Prop} (h : ∀ i, ¬ P i) :
    first P = n := by
  have he : Finset.univ.filter P = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact h i
  simp [first, he]

def lastPlus {n : ℕ} (P : Fin n → Prop) : ℕ :=
  (insert 0 ((Finset.univ.filter P).image fun i => i.val + 1)).max' (by simp)

theorem lastPlus_le_size {n : ℕ} (P : Fin n → Prop) : lastPlus P ≤ n := by
  apply Finset.max'_le
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact Nat.zero_le _
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
    exact i.isLt

theorem lt_lastPlus {n : ℕ} {P : Fin n → Prop} {i : Fin n} (hi : P i) :
    i.val < lastPlus P := by
  have hm : i.val + 1 ∈
      insert 0 ((Finset.univ.filter P).image fun j => j.val + 1) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact Or.inr ⟨i, hi, rfl⟩
  have h : i.val + 1 ≤ lastPlus P := Finset.le_max' _ _ hm
  omega

theorem lastPlus_mem {n : ℕ} {P : Fin n → Prop} (h : 0 < lastPlus P) :
    ∃ i : Fin n, P i ∧ i.val + 1 = lastPlus P := by
  have hm := Finset.max'_mem
    (insert 0 ((Finset.univ.filter P).image fun i => i.val + 1)) (by simp)
  rcases Finset.mem_insert.mp hm with he | hm
  · exact False.elim (by unfold lastPlus at h; omega)
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact ⟨i, (Finset.mem_filter.mp hi).2, he⟩

theorem not_after_lastPlus {n : ℕ} {P : Fin n → Prop} {i : Fin n}
    (hi : lastPlus P ≤ i.val) : ¬ P i :=
  fun h => (Nat.not_lt_of_ge hi) (lt_lastPlus h)

theorem lastPlus_mono {n : ℕ} {P S : Fin n → Prop}
    (h : ∀ i, P i → S i) : lastPlus P ≤ lastPlus S := by
  by_cases hz : 0 < lastPlus P
  · obtain ⟨i, hi, he⟩ := lastPlus_mem hz
    have hh := lt_lastPlus (h i hi)
    omega
  · omega

theorem lastPlus_eq_zero {n : ℕ} {P : Fin n → Prop} (h : ∀ i, ¬ P i) :
    lastPlus P = 0 := by
  have he : Finset.univ.filter P = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact h i
  simp [lastPlus, he]

end Index

/-- The half-open fringe interval is `[lo,hi)`. The label transition is
at `hi` for an ancestor and at `lo` for a descendant. -/
structure Cut (n : ℕ) where
  lo : ℕ
  hi : ℕ
  ordered : lo ≤ hi
  bounded : hi ≤ n
  ancestor : Bool

namespace Cut

variable {n : ℕ}

def Contains (C : Cut n) (i : ℕ) : Prop := C.lo ≤ i ∧ i < C.hi

def bit (C : Cut n) (i : ℕ) : Prop :=
  if C.ancestor then C.hi ≤ i else i < C.lo

theorem outside_sides (C : Cut n) {i : ℕ} (hi : ¬ C.Contains i) :
    C.lo ≤ i ↔ C.hi ≤ i := by
  have := C.ordered
  simp only [Contains] at hi
  omega

theorem outside_bit_sides (C : Cut n) {i j : ℕ}
    (hi : ¬ C.Contains i) (hj : ¬ C.Contains j)
    (he : C.bit i ↔ C.bit j) :
    (C.lo ≤ i ↔ C.lo ≤ j) ∧ (C.hi ≤ i ↔ C.hi ≤ j) := by
  have hi' := C.outside_sides hi
  have hj' := C.outside_sides hj
  cases h : C.ancestor <;> simp [bit, h] at he <;> omega

end Cut

namespace Cells

def successor (B : Finset ℕ) (n a : ℕ) : ℕ :=
  (insert n (B.filter (a < ·))).min' (by simp)

def partition (B : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (B.filter (· < n)).image fun a => (a, successor B n a)

def Contains (I : ℕ × ℕ) (i : ℕ) : Prop := I.1 ≤ i ∧ i < I.2

theorem successor_le_size (B : Finset ℕ) (n a : ℕ) : successor B n a ≤ n :=
  Finset.min'_le _ _ (by simp)

theorem successor_mem {B : Finset ℕ} {n a : ℕ} (hn : n ∈ B) :
    successor B n a ∈ B := by
  have hh := Finset.min'_mem (insert n (B.filter (a < ·))) (by simp)
  rcases Finset.mem_insert.mp hh with he | hh
  · change successor B n a = n at he
    rw [he]
    exact hn
  · exact (Finset.mem_filter.mp hh).1

theorem lt_successor {B : Finset ℕ} {n a : ℕ} (ha : a < n) :
    a < successor B n a := by
  have hh := Finset.min'_mem (insert n (B.filter (a < ·))) (by simp)
  rcases Finset.mem_insert.mp hh with he | hh
  · change successor B n a = n at he
    rw [he]
    exact ha
  · exact (Finset.mem_filter.mp hh).2

theorem successor_le {B : Finset ℕ} {n a k : ℕ} (hk : k ∈ B) (ha : a < k) :
    successor B n a ≤ k :=
  Finset.min'_le _ _ (by simp [hk, ha])

theorem bounds {B : Finset ℕ} {n : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ partition B n) : I.1 < I.2 ∧ I.2 ≤ n ∧ I.1 ∈ B := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨haB, han⟩ := Finset.mem_filter.mp ha
  exact ⟨lt_successor han, successor_le_size _ _ _, haB⟩

theorem no_boundary_inside {B : Finset ℕ} {n : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ partition B n) {k : ℕ} (hk : k ∈ B) :
    k ≤ I.1 ∨ I.2 ≤ k := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
  by_cases h : k ≤ a
  · exact Or.inl h
  · exact Or.inr (successor_le hk (by omega))

theorem same_side {B : Finset ℕ} {n : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ partition B n) {i j k : ℕ}
    (hi : Contains I i) (hj : Contains I j) (hk : k ∈ B) :
    (k ≤ i ↔ k ≤ j) := by
  rcases no_boundary_inside hI hk with h | h <;> simp only [Contains] at hi hj <;> omega

theorem cover {B : Finset ℕ} {n i : ℕ} (hzero : 0 ∈ B) (hn : n ∈ B)
    (hi : i < n) : ∃ I ∈ partition B n, Contains I i := by
  let S := B.filter (· ≤ i)
  have hS : S.Nonempty := ⟨0, by simp [S, hzero]⟩
  let a := S.max' hS
  have haS : a ∈ S := Finset.max'_mem _ _
  have haB : a ∈ B := (Finset.mem_filter.mp haS).1
  have hai : a ≤ i := (Finset.mem_filter.mp haS).2
  have han : a < n := hai.trans_lt hi
  refine ⟨(a, successor B n a), Finset.mem_image.mpr
    ⟨a, by simp [haB, han], rfl⟩, hai, ?_⟩
  by_contra h
  have hsi : successor B n a ≤ i := by omega
  have hsS : successor B n a ∈ S := by simp [S, successor_mem hn, hsi]
  have hsa : successor B n a ≤ a := Finset.le_max' _ _ hsS
  have := lt_successor (B := B) han
  omega

theorem overlap_eq {B : Finset ℕ} {n i : ℕ} {I J : ℕ × ℕ}
    (hI : I ∈ partition B n) (hJ : J ∈ partition B n)
    (hi : Contains I i) (hj : Contains J i) : I = J := by
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hJ
  have haB := (Finset.mem_filter.mp ha).1
  have hbB := (Finset.mem_filter.mp hb).1
  have hab : a = b := by
    simp only [Contains] at hi hj
    rcases lt_trichotomy a b with h | h | h
    · have := successor_le (n := n) hbB h
      omega
    · exact h
    · have := successor_le (n := n) haB h
      omega
  simp [hab]

theorem eq_of_sides {B : Finset ℕ} {n i j : ℕ} {I J : ℕ × ℕ}
    (hn : n ∈ B) (hI : I ∈ partition B n) (hJ : J ∈ partition B n)
    (hi : Contains I i) (hj : Contains J j)
    (hs : ∀ k ∈ B, k ≤ i ↔ k ≤ j) : I = J := by
  have hIb := bounds hI
  have hlo : I.1 ≤ j := (hs I.1 hIb.2.2).mp hi.1
  have hhi : j < I.2 := by
    have hmem : I.2 ∈ B := by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hI
      exact successor_mem hn
    have hh := hs I.2 hmem
    have := hi.2
    omega
  exact overlap_eq hI hJ ⟨hlo, hhi⟩ hj

theorem card_le {B : Finset ℕ} {n : ℕ} (hn : n ∈ B) :
    (partition B n).card + 1 ≤ B.card := by
  have hsub : B.filter (· < n) ⊆ B.erase n := by
    intro a ha
    obtain ⟨haB, han⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_erase.mpr ⟨by omega, haB⟩
  have h1 := Finset.card_image_le (s := B.filter (· < n))
    (f := fun a => (a, successor B n a))
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_erase_add_one hn
  unfold partition
  omega

end Cells

variable {A : Type*}

def boundaries {n : ℕ} (P : Finset A) (C : A → Cut n) : Finset ℕ :=
  insert 0 (insert n (P.image (fun p => (C p).lo) ∪ P.image (fun p => (C p).hi)))

def signature {n : ℕ} (P : Finset A) (C : A → Cut n) (i : ℕ) : Finset A :=
  P.filter fun p => (C p).bit i

theorem boundaries_card {n : ℕ} (P : Finset A) (C : A → Cut n) :
    (boundaries P C).card ≤ 2 * P.card + 2 := by
  have h0 := Finset.card_insert_le 0
    (insert n (P.image (fun p => (C p).lo) ∪ P.image (fun p => (C p).hi)))
  have hn := Finset.card_insert_le n
    (P.image (fun p => (C p).lo) ∪ P.image (fun p => (C p).hi))
  have hu := Finset.card_union_le
    (P.image fun p => (C p).lo) (P.image fun p => (C p).hi)
  have hlo := Finset.card_image_le (s := P) (f := fun p => (C p).lo)
  have hhi := Finset.card_image_le (s := P) (f := fun p => (C p).hi)
  unfold boundaries
  omega

theorem partition_card {n : ℕ} (P : Finset A) (C : A → Cut n) :
    (Cells.partition (boundaries P C) n).card ≤ 2 * P.card + 1 := by
  have h := Cells.card_le (B := boundaries P C) (n := n) (by simp [boundaries])
  have := boundaries_card P C
  omega

theorem cut_constant {n : ℕ} {P : Finset A} {C : A → Cut n}
    {I : ℕ × ℕ} (hI : I ∈ Cells.partition (boundaries P C) n)
    {p : A} (hp : p ∈ P) {i j : ℕ}
    (hi : Cells.Contains I i) (hj : Cells.Contains I j) :
    ((C p).Contains i ↔ (C p).Contains j) ∧
      ((C p).bit i ↔ (C p).bit j) := by
  have hlo := Cells.same_side hI hi hj
    (k := (C p).lo) (by
      simp only [boundaries, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))
  have hhi := Cells.same_side hI hi hj
    (k := (C p).hi) (by
      simp only [boundaries, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inr ⟨p, hp, rfl⟩)))
  constructor
  · simp only [Cut.Contains]
    omega
  · cases h : (C p).ancestor <;> simp [Cut.bit, h] <;> omega

theorem signature_constant {n : ℕ} {P : Finset A} {C : A → Cut n}
    {I : ℕ × ℕ} (hI : I ∈ Cells.partition (boundaries P C) n)
    {i j : ℕ} (hi : Cells.Contains I i) (hj : Cells.Contains I j) :
    signature P C i = signature P C j := by
  ext p
  simp only [signature, Finset.mem_filter]
  exact and_congr_right fun hp => (cut_constant hI hp hi hj).2

/-- Every atom is wholly inside an actual fringe interval, or wholly outside
all fringe intervals. -/
theorem partition_classify {n : ℕ} {P : Finset A} {C : A → Cut n}
    {I : ℕ × ℕ} (hI : I ∈ Cells.partition (boundaries P C) n) :
    (∃ p ∈ P, ∀ i, Cells.Contains I i → (C p).Contains i) ∨
      (∀ p ∈ P, ∀ i, Cells.Contains I i → ¬ (C p).Contains i) := by
  by_cases hf : ∃ p ∈ P, (C p).Contains I.1
  · obtain ⟨p, hp, hf⟩ := hf
    exact Or.inl ⟨p, hp, fun i hi =>
      (cut_constant hI hp ⟨le_rfl, (Cells.bounds hI).1⟩ hi).1.mp hf⟩
  · right
    intro p hp i hi h
    exact hf ⟨p, hp, (cut_constant hI hp ⟨le_rfl, (Cells.bounds hI).1⟩ hi).1.mpr h⟩

theorem core_signatures_distinct {n : ℕ} {P : Finset A} {C : A → Cut n}
    {I J : ℕ × ℕ}
    (hI : I ∈ Cells.partition (boundaries P C) n)
    (hJ : J ∈ Cells.partition (boundaries P C) n)
    (hIc : ∀ p ∈ P, ¬ (C p).Contains I.1)
    (hJc : ∀ p ∈ P, ¬ (C p).Contains J.1)
    (he : signature P C I.1 = signature P C J.1) : I = J := by
  have hbits (p : A) (hp : p ∈ P) : (C p).bit I.1 ↔ (C p).bit J.1 := by
    have hh := Finset.ext_iff.mp he p
    simpa [signature, hp] using hh
  apply Cells.eq_of_sides (by simp [boundaries]) hI hJ
    ⟨le_rfl, (Cells.bounds hI).1⟩ ⟨le_rfl, (Cells.bounds hJ).1⟩
  intro k hk
  simp only [boundaries, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hk
  rcases hk with rfl | rfl | ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · omega
  · have h1 := (Cells.bounds hI).1.trans_le (Cells.bounds hI).2.1
    have h2 := (Cells.bounds hJ).1.trans_le (Cells.bounds hJ).2.1
    omega
  · exact ((C p).outside_bit_sides (hIc p hp) (hJc p hp) (hbits p hp)).1
  · exact ((C p).outside_bit_sides (hIc p hp) (hJc p hp) (hbits p hp)).2

end

end StreamingReachability.Early
