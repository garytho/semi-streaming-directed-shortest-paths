module

public import StreamingReachability.Core.SparseLabels

@[expose] public section

namespace StreamingReachability.Core.RecordMap

variable {K S T : Type*} [DecidableEq K]

abbrev Map (K S : Type*) := List (K × S)

def get (zero : S) : Map K S → K → S
  | [], _ => zero
  | p :: ps, k => if p.1 = k then p.2 else get zero ps k

def keys (xs : Map K S) : Finset K := (xs.map Prod.fst).toFinset

def Unique (xs : Map K S) : Prop := (xs.map Prod.fst).Nodup

def set (k : K) (s : S) : Map K S → Map K S
  | [] => [(k, s)]
  | p :: ps => if p.1 = k then (k, s) :: ps else p :: set k s ps

def modify (zero : S) (k : K) (f : S → S) (xs : Map K S) : Map K S :=
  set k (f (get zero xs k)) xs

@[simp] theorem get_nil (zero : S) (k : K) : get zero [] k = zero := rfl

@[simp] theorem get_cons (zero : S) (p : K × S) (ps : Map K S) (k : K) :
    get zero (p :: ps) k = if p.1 = k then p.2 else get zero ps k := rfl

theorem get_set (zero : S) (xs : Map K S) (k q : K) (s : S) :
    get zero (set k s xs) q = if q = k then s else get zero xs q := by
  induction xs with
  | nil =>
      by_cases h : q = k
      · subst q; simp [set, get]
      · simp [set, get, h, Ne.symm h]
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · by_cases hq : q = k
        · subst q; simp [set, hp, get]
        · have hpq : p.1 ≠ q := fun h => hq (h.symm.trans hp)
          simp [set, hp, get, hq, hpq, Ne.symm hq]
      · by_cases hq : q = k
        · subst q; simpa [set, hp, get] using ih
        · simp [set, hp, get, hq, ih]

theorem get_map (zs : S) (zt : T) (xs : Map K S) (f : K → S → T)
    (hz : ∀ k, f k zs = zt) (k : K) :
    get zt (xs.map fun p => (p.1, f p.1 p.2)) k = f k (get zs xs k) := by
  induction xs with
  | nil => exact (hz k).symm
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · simp [get, hp]
      · simp [get, hp, ih]

theorem get_of_not_mem (zero : S) (xs : Map K S) {k : K} (hk : k ∉ keys xs) :
    get zero xs k = zero := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
      have hp : p.1 ≠ k := by
        intro he
        exact hk (by simp [keys, he])
      have ht : k ∉ keys ps := fun h => hk (by simpa [keys] using Or.inr h)
      simp [get, hp, ih ht]

theorem get_mem (zero : S) (xs : Map K S) (hu : Unique xs) {k : K} {s : S}
    (hs : (k, s) ∈ xs) : get zero xs k = s := by
  induction xs with
  | nil => simp at hs
  | cons p ps ih =>
      obtain ⟨hp, ht⟩ := List.nodup_cons.mp hu
      rcases List.mem_cons.mp hs with he | hs
      · subst p; simp [get]
      · have hk : p.1 ≠ k := by
          intro he
          exact hp (he ▸ List.mem_map.mpr ⟨(k, s), hs, rfl⟩)
        simp only [get, hk, ↓reduceIte]
        exact ih ht hs

theorem exists_get_mem (zero : S) (xs : Map K S) {k : K} (hk : k ∈ keys xs) :
    (k, get zero xs k) ∈ xs := by
  induction xs with
  | nil => simp [keys] at hk
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · have he : p = (k, p.2) := Prod.ext hp rfl
        simp [get, hp, ← he]
      · have ht : k ∈ keys ps := by simpa [keys, hp, Ne.symm hp] using hk
        simp only [get, hp, ↓reduceIte]
        exact List.mem_cons_of_mem _ (ih ht)

theorem keys_set (xs : Map K S) (k : K) (s : S) :
    keys (set k s xs) = insert k (keys xs) := by
  induction xs with
  | nil => simp [set, keys]
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · simp [set, hp, keys]
      · simp only [set, hp, ↓reduceIte, keys, List.map_cons, List.toFinset_cons]
        simpa only [keys, Finset.insert_comm] using congrArg (fun t : Finset K => insert p.1 t) ih

theorem unique_set (xs : Map K S) (hu : Unique xs) (k : K) (s : S) :
    Unique (set k s xs) := by
  induction xs with
  | nil => simp [Unique, set]
  | cons p ps ih =>
      obtain ⟨hp, ht⟩ := List.nodup_cons.mp hu
      by_cases he : p.1 = k
      · simpa only [Unique, set, he, ↓reduceIte, List.map_cons, he] using hu
      · simp only [Unique, set, he, ↓reduceIte, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih ht⟩
        intro h
        have hm : p.1 ∈ keys (set k s ps) := List.mem_toFinset.mpr h
        rw [keys_set] at hm
        rcases Finset.mem_insert.mp hm with hm | hm
        · exact he hm
        · exact hp (List.mem_toFinset.mp hm)

theorem unique_map (xs : Map K S) (hu : Unique xs) (f : K → S → T) :
    Unique (xs.map fun p => (p.1, f p.1 p.2)) := by
  simpa only [Unique, List.map_map, Function.comp_def] using hu

theorem length_set (xs : Map K S) (k : K) (s : S) :
    (set k s xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [set]
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · simp [set, hp]
      · simpa only [set, hp, ↓reduceIte, List.length_cons] using Nat.add_le_add_right ih 1

def foldModify (zero : S) (f : K → S → S) (guard : K → Bool)
    (publicKeys : List K) (xs : Map K S) : Map K S :=
  publicKeys.foldl (fun ys k => if guard k then modify zero k (f k) ys else ys) xs

theorem get_foldModify (zero : S) (f : K → S → S) (guard : K → Bool)
    (publicKeys : List K) (hu : publicKeys.Nodup) (xs : Map K S) (q : K) :
    get zero (foldModify zero f guard publicKeys xs) q =
      if q ∈ publicKeys ∧ guard q = true then f q (get zero xs q) else get zero xs q := by
  induction publicKeys generalizing xs with
  | nil => simp [foldModify]
  | cons k ks ih =>
      obtain ⟨hk, ht⟩ := List.nodup_cons.mp hu
      unfold foldModify
      rw [List.foldl_cons]
      change get zero (foldModify zero f guard ks
        (if guard k then modify zero k (f k) xs else xs)) q = _
      rw [ih ht]
      by_cases hq : q = k
      · subst q
        cases hg : guard k <;> simp [hg, hk, modify, get_set]
      · cases hg : guard k <;>
          simp [hg, hq, Ne.symm hq, modify, get_set]

theorem unique_foldModify (zero : S) (f : K → S → S) (guard : K → Bool)
    (publicKeys : List K) (xs : Map K S) (hu : Unique xs) :
    Unique (foldModify zero f guard publicKeys xs) := by
  induction publicKeys generalizing xs with
  | nil => exact hu
  | cons k ks ih =>
      unfold foldModify
      rw [List.foldl_cons]
      apply ih
      cases hg : guard k
      · exact hu
      · exact unique_set xs hu k _

end StreamingReachability.Core.RecordMap
