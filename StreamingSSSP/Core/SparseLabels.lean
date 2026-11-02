module

public import StreamingSSSP.Core.Rounding

@[expose] public section

namespace StreamingSSSP.Core.SparseLabels

variable {V : Type*} [DecidableEq V]

abbrev Labels (V : Type*) := List (V × Distance)

def get (records : Labels V) (v : V) : Distance :=
  records.foldr (fun p d => if p.1 = v then min p.2 d else d) ⊤

def support (records : Labels V) : Finset V := (records.map Prod.fst).toFinset

@[simp] theorem get_nil (v : V) : get [] v = ⊤ := rfl

@[simp] theorem get_cons (p : V × Distance) (records : Labels V) (v : V) :
    get (p :: records) v = if p.1 = v then min p.2 (get records v) else get records v := rfl

theorem get_le_record (records : Labels V) {v : V} {d : Distance} (h : (v, d) ∈ records) :
    get records v ≤ d := by
  induction records with
  | nil => simp at h
  | cons p records ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp only [get_cons, ↓reduceIte]
        exact min_le_left _ _
      · rw [get_cons]
        split_ifs
        · exact (min_le_right _ _).trans (ih h)
        · exact ih h

theorem le_get (records : Labels V) (v : V) (d : Distance) :
    d ≤ get records v ↔ ∀ p ∈ records, p.1 = v → d ≤ p.2 := by
  induction records with
  | nil => simp
  | cons p records ih =>
      by_cases hp : p.1 = v <;> simp [get_cons, hp, ih]

theorem get_eq_top_of_not_mem (records : Labels V) {v : V} (hv : v ∉ support records) :
    get records v = ⊤ := by
  apply top_le_iff.mp
  apply (le_get records v ⊤).mpr
  intro p hp he
  exact False.elim (hv (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, he⟩)))

def upsert (v : V) (d : Distance) : Labels V → Labels V
  | [] => [(v, d)]
  | p :: records =>
      if p.1 = v then (v, min d p.2) :: records else p :: upsert v d records

theorem get_insert (v : V) (d : Distance) (records : Labels V) (u : V) :
    get (upsert v d records) u =
      if u = v then min d (get records u) else get records u := by
  induction records with
  | nil =>
      by_cases huv : u = v
      · subst u; simp [upsert, get]
      · simp [upsert, get, huv, Ne.symm huv]
  | cons p records ih =>
      by_cases hp : p.1 = v
      · by_cases huv : u = v
        · subst u; simp [upsert, hp, get_cons, min_assoc]
        · simp [upsert, hp, get_cons, huv, Ne.symm huv]
      · by_cases huv : u = v
        · subst u; simpa [upsert, hp, get_cons] using ih
        · simp [upsert, hp, get_cons, huv, ih]

theorem support_insert (v : V) (d : Distance) (records : Labels V) :
    support (upsert v d records) = insert v (support records) := by
  induction records with
  | nil => simp [upsert, support]
  | cons p records ih =>
      by_cases hp : p.1 = v
      · simp [upsert, support, hp]
      · simp only [upsert, hp, ↓reduceIte, support, List.map_cons, List.toFinset_cons]
        simpa only [support, Finset.insert_comm] using
          congrArg (fun s : Finset V => insert p.1 s) ih

theorem length_insert (v : V) (d : Distance) (records : Labels V) :
    (upsert v d records).length ≤ records.length + 1 := by
  induction records with
  | nil => simp [upsert]
  | cons p records ih =>
      by_cases hp : p.1 = v
      · simp [upsert, hp]
      · simpa only [upsert, hp, ↓reduceIte, List.length_cons] using Nat.add_le_add_right ih 1

theorem nodup_insert (v : V) (d : Distance) (records : Labels V)
    (h : (records.map Prod.fst).Nodup) :
    ((upsert v d records).map Prod.fst).Nodup := by
  induction records with
  | nil => simp [upsert]
  | cons p records ih =>
      obtain ⟨hp, ht⟩ := List.nodup_cons.mp h
      by_cases he : p.1 = v
      · simpa only [upsert, he, ↓reduceIte, List.map_cons, he] using h
      · simp only [upsert, he, ↓reduceIte, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih ht⟩
        intro hm
        have hs : p.1 ∈ support (upsert v d records) := List.mem_toFinset.mpr hm
        rw [support_insert] at hs
        rcases Finset.mem_insert.mp hs with hs | hs
        · exact he hs
        · exact hp (List.mem_toFinset.mp hs)

theorem length_eq_card (records : Labels V) (h : (records.map Prod.fst).Nodup) :
    records.length = (support records).card := by
  simpa only [support, List.length_map] using (List.toFinset_card_of_nodup h).symm

def vector {n : ℕ} (records : Labels (Fin n)) : StoredEdges.DistanceArray n :=
  Vector.ofFn (get records)

@[simp] theorem vector_get {n : ℕ} (records : Labels (Fin n)) (v : Fin n) :
    (vector records).get v = get records v := by simp [vector]

end StreamingSSSP.Core.SparseLabels
