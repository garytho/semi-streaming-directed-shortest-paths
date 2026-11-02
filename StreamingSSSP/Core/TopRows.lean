module

public import StreamingSSSP.Graph.StoredEdges

@[expose] public section

namespace StreamingSSSP.Core

namespace TopRows

def Unique (n : ℕ) (row : Finset ℕ) : Prop :=
  ∀ a ∈ row, ∀ b ∈ row, a % n = b % n → a = b

def Covered (n τ : ℕ) (row : Finset ℕ) (k : ℕ) : Prop :=
  (∃ q ∈ row, q % n = k % n ∧ q ≤ k) ∨
    τ ≤ (row.filter (· ≤ k)).card

def replace (n k : ℕ) (row : Finset ℕ) : Finset ℕ :=
  insert k (row.filter fun q => q % n ≠ k % n)

def maximum (row : Finset ℕ) : ℕ :=
  (row.sort (· ≤ ·)).foldr Nat.max 0

@[simp] theorem maximum_eq_sup (row : Finset ℕ) : maximum row = row.sup id := by
  have h (xs : List ℕ) : xs.foldr Nat.max 0 = xs.toFinset.sup id := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
        simp only [List.foldr_cons, List.toFinset_cons, Finset.sup_insert, id_eq, ih]
  simpa only [Finset.sort_toFinset, maximum] using h (row.sort (· ≤ ·))

def eraseKey (row : Finset ℕ) (k : ℕ) : Finset ℕ := row.filter (· ≠ k)

@[simp] theorem eraseKey_eq (row : Finset ℕ) (k : ℕ) :
    eraseKey row k = row.erase k := by
  ext q
  simp [eraseKey, and_comm]

def cap (τ : ℕ) (row : Finset ℕ) : Finset ℕ :=
  if row.card ≤ τ then row else eraseKey row (maximum row)

def hasBetter (n k : ℕ) (row : Finset ℕ) : Prop :=
  0 < (row.filter fun q => q % n = k % n ∧ q ≤ k).card
  deriving Decidable

@[simp] theorem hasBetter_iff (n k : ℕ) (row : Finset ℕ) :
    hasBetter n k row ↔ ∃ q ∈ row, q % n = k % n ∧ q ≤ k := by
  unfold hasBetter
  rw [Finset.card_pos]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hqr, hqres, hqle⟩ := Finset.mem_filter.mp hq
    exact ⟨q, hqr, hqres, hqle⟩
  · rintro ⟨q, hq, hr, hle⟩
    exact ⟨q, Finset.mem_filter.mpr ⟨hq, hr, hle⟩⟩

def offer (n τ k : ℕ) (row : Finset ℕ) : Finset ℕ :=
  if hasBetter n k row then row
  else cap τ (replace n k row)

structure Valid (n τ : ℕ) (seen row : Finset ℕ) : Prop where
  retained : row ⊆ seen
  bounded : row.card ≤ τ
  unique : Unique n row
  covers : ∀ k ∈ seen, Covered n τ row k

theorem sup_mem {row : Finset ℕ} (h : row.Nonempty) : row.sup id ∈ row := by
  obtain ⟨q, hq, he⟩ := Finset.exists_mem_eq_sup row h id
  simpa only [he, id_eq] using hq

theorem cap_subset (τ : ℕ) (row : Finset ℕ) : cap τ row ⊆ row := by
  unfold cap
  split_ifs
  · exact Finset.Subset.refl _
  · exact Finset.filter_subset _ _

theorem cap_card (τ : ℕ) (row : Finset ℕ) (h : row.card ≤ τ + 1) :
    (cap τ row).card ≤ τ := by
  unfold cap
  rw [maximum_eq_sup, eraseKey_eq]
  split_ifs with hc
  · exact hc
  · have hm := sup_mem (Finset.card_pos.mp (by omega : 0 < row.card))
    rw [Finset.card_erase_of_mem hm]
    omega

theorem cap_card_eq (τ : ℕ) (row : Finset ℕ) (h : row.card = τ + 1) :
    (cap τ row).card = τ := by
  have hm := sup_mem (Finset.card_pos.mp (by omega : 0 < row.card))
  simp [cap, h, Finset.card_erase_of_mem hm]

theorem cap_covered (n τ : ℕ) (row : Finset ℕ) (k : ℕ)
    (hsize : row.card ≤ τ + 1) (h : Covered n τ row k) :
    Covered n τ (cap τ row) k := by
  by_cases hc : row.card ≤ τ
  · simpa [cap, hc] using h
  have hcard : row.card = τ + 1 := by omega
  have hcap : (cap τ row).card = τ := cap_card_eq τ row hcard
  have hall (hk : row.sup id ≤ k) :
      (cap τ row).filter (· ≤ k) = cap τ row := by
    apply Finset.filter_true_of_mem
    intro q hq
    exact (Finset.le_sup (cap_subset τ row hq)).trans hk
  rcases h with ⟨q, hq, hres, hqk⟩ | hlow
  · by_cases hqm : q = row.sup id
    · right
      rw [hall (hqm ▸ hqk), hcap]
    · left
      exact ⟨q, by simp [cap, hc, hq, hqm], hres, hqk⟩
  · right
    by_cases hm : row.sup id ≤ k
    · rw [hall hm, hcap]
    · have hfilter :
          (cap τ row).filter (· ≤ k) = row.filter (· ≤ k) := by
        ext q
        simp only [cap, maximum_eq_sup, eraseKey_eq, hc, ↓reduceIte,
          Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hq⟩, hqk⟩
          exact ⟨hq, hqk⟩
        · rintro ⟨hq, hqk⟩
          exact ⟨⟨fun he => hm (he ▸ hqk), hq⟩, hqk⟩
      simpa only [hfilter] using hlow

theorem replace_unique (n k : ℕ) (row : Finset ℕ) (h : Unique n row) :
    Unique n (replace n k row) := by
  intro a ha b hb hab
  simp only [replace, Finset.mem_insert, Finset.mem_filter] at ha hb
  rcases ha with rfl | ⟨ha, hak⟩
  · rcases hb with rfl | ⟨_, hbk⟩
    · rfl
    · exact False.elim (hbk hab.symm)
  · rcases hb with rfl | ⟨hb, _⟩
    · exact False.elim (hak hab)
    · exact h a ha b hb hab

theorem replace_card (n k : ℕ) (row : Finset ℕ) :
    (replace n k row).card ≤ row.card + 1 := by
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_filter_le _ _) 1)

theorem offer_card (n τ k : ℕ) (row : Finset ℕ) (h : row.card ≤ τ) :
    (offer n τ k row).card ≤ τ := by
  unfold offer
  split_ifs
  · exact h
  · exact cap_card τ _ ((replace_card n k row).trans (Nat.add_le_add_right h 1))

def transitionCells (n τ k : ℕ) (row : Finset ℕ) : ℕ :=
  row.card + (row.filter fun q => q % n ≠ k % n).card +
    (replace n k row).card + (offer n τ k row).card

theorem transitionCells_le (n τ k : ℕ) (row : Finset ℕ) (h : row.card ≤ τ) :
    transitionCells n τ k row ≤ 4 * τ + 1 := by
  have hf := Finset.card_filter_le row (fun q => q % n ≠ k % n)
  have hr := replace_card n k row
  have ho := offer_card n τ k row h
  unfold transitionCells
  omega

theorem replace_covered (n τ k : ℕ) (row : Finset ℕ)
    (hu : Unique n row)
    (hnew : ¬ ∃ q ∈ row, q % n = k % n ∧ q ≤ k)
    {j : ℕ} (hj : Covered n τ row j) :
    Covered n τ (replace n k row) j := by
  have hlt : ∀ q ∈ row, q % n = k % n → k < q := by
    intro q hq hr
    exact lt_of_not_ge (fun h => hnew ⟨q, hq, hr, h⟩)
  let f : ℕ → ℕ := fun q => if q % n = k % n then k else q
  have hfres (q : ℕ) : f q % n = q % n := by
    dsimp [f]
    split_ifs with h
    · exact h.symm
    · rfl
  have hfle (q : ℕ) (hq : q ∈ row) : f q ≤ q := by
    dsimp [f]
    split_ifs with h
    · exact (hlt q hq h).le
    · exact le_rfl
  have hfmem (q : ℕ) (hq : q ∈ row) : f q ∈ replace n k row := by
    dsimp [f]
    split_ifs with h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hq, h⟩)
  rcases hj with ⟨q, hq, hres, hqj⟩ | hlow
  · exact Or.inl ⟨f q, hfmem q hq, (hfres q).trans hres, (hfle q hq).trans hqj⟩
  · right
    apply hlow.trans
    apply Finset.card_le_card_of_injOn f
    · intro q hq
      obtain ⟨hqr, hqj⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hfmem q hqr, (hfle q hqr).trans hqj⟩
    · intro a ha b hb he
      apply hu a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      rw [← hfres a, ← hfres b, he]

theorem valid_empty (n τ : ℕ) : Valid n τ ∅ ∅ := by
  constructor <;> simp [Unique]

theorem valid_offer (n τ k : ℕ) (seen row : Finset ℕ)
    (h : Valid n τ seen row) :
    Valid n τ (insert k seen) (offer n τ k row) := by
  by_cases hn : ∃ q ∈ row, q % n = k % n ∧ q ≤ k
  · simp only [offer, hasBetter_iff, hn, ↓reduceIte]
    refine ⟨h.retained.trans (Finset.subset_insert _ _), h.bounded, h.unique, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hn
    · exact h.covers j hj
  · simp only [offer, hasBetter_iff, hn, ↓reduceIte]
    have hs : (replace n k row).card ≤ τ + 1 :=
      (replace_card n k row).trans (Nat.add_le_add_right h.bounded 1)
    refine ⟨?_, cap_card τ _ hs, ?_, ?_⟩
    · intro q hq
      have hqr := cap_subset τ (replace n k row) hq
      rcases Finset.mem_insert.mp hqr with rfl | hqr
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (h.retained (Finset.mem_filter.mp hqr).1)
    · intro a ha b hb hr
      exact replace_unique n k row h.unique a (cap_subset τ _ ha)
        b (cap_subset τ _ hb) hr
    · intro j hj
      apply cap_covered n τ _ j hs
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact Or.inl ⟨j, Finset.mem_insert_self _ _, rfl, le_rfl⟩
      · exact replace_covered n τ k row h.unique hn (h.covers j hj)

def build (n τ : ℕ) (keys : List ℕ) : Finset ℕ :=
  keys.foldl (fun row k => offer n τ k row) ∅

theorem fold_valid (n τ : ℕ) (keys : List ℕ) (seen row : Finset ℕ)
    (h : Valid n τ seen row) :
    Valid n τ (seen ∪ keys.toFinset)
      (keys.foldl (fun row k => offer n τ k row) row) := by
  induction keys generalizing seen row with
  | nil => simpa using h
  | cons k ks ih =>
      have hh := ih (insert k seen) (offer n τ k row) (valid_offer n τ k seen row h)
      simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert,
        List.foldl_cons] using hh

theorem build_valid (n τ : ℕ) (keys : List ℕ) :
    Valid n τ keys.toFinset (build n τ keys) := by
  simpa only [Finset.empty_union, build] using fold_valid n τ keys ∅ ∅ (valid_empty n τ)

theorem missing_witness (n τ : ℕ) (seen row : Finset ℕ)
    (h : Valid n τ seen row) {k : ℕ} (hk : k ∈ seen)
    (hm : ¬ ∃ q ∈ row, q % n = k % n ∧ q ≤ k) :
    ∃ Z : Finset ℕ, Z ⊆ row ∧ Z.card = τ ∧ ∀ q ∈ Z, q ≤ k := by
  have hlow : τ ≤ (row.filter (· ≤ k)).card := (h.covers k hk).resolve_left hm
  refine ⟨row.filter (· ≤ k), Finset.filter_subset _ _, ?_, ?_⟩
  · exact le_antisymm ((Finset.card_filter_le _ _).trans h.bounded) hlow
  · intro q hq
    exact (Finset.mem_filter.mp hq).2

theorem retained_minimum (n τ : ℕ) (seen row : Finset ℕ)
    (h : Valid n τ seen row) {q k : ℕ} (hq : q ∈ row) (hk : k ∈ seen)
    (hr : q % n = k % n) : q ≤ k := by
  rcases h.covers k hk with ⟨p, hp, hpk, hle⟩ | hlow
  · have he := h.unique q hq p hp (hr.trans hpk.symm)
    exact he ▸ hle
  · have he : row.filter (· ≤ k) = row :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (h.bounded.trans hlow)
    have hqf : q ∈ row.filter (· ≤ k) := by rwa [he]
    exact (Finset.mem_filter.mp hqf).2

end TopRows

end StreamingSSSP.Core
