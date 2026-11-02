module

public import StreamingSSSP.Core.RecordMap

@[expose] public section

namespace StreamingSSSP.Core.SparseLabels

variable {V : Type*} [DecidableEq V]

theorem get_append (xs ys : Labels V) (v : V) :
    get (xs ++ ys) v = min (get xs v) (get ys v) := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
      by_cases hp : p.1 = v <;> simp [get_cons, hp, ih, min_assoc]

theorem support_append (xs ys : Labels V) :
    support (xs ++ ys) = support xs ∪ support ys := by
  simp [support]

def ofSet [LinearOrder V] (K : Finset V) (d : V → Distance) : Labels V :=
  (K.sort (· ≤ ·)).map fun v => (v, d v)

theorem support_ofSet [LinearOrder V] (K : Finset V) (d : V → Distance) :
    support (ofSet K d) = K := by
  simp [support, ofSet, List.map_map, Function.comp_def]

theorem get_ofSet [LinearOrder V] (K : Finset V) (d : V → Distance) (v : V) :
    get (ofSet K d) v = if v ∈ K then d v else ⊤ := by
  by_cases hv : v ∈ K
  · rw [ite_eq_left hv]
    apply le_antisymm
    · apply get_le_record
      exact List.mem_map.mpr ⟨v, (Finset.mem_sort _).mpr hv, rfl⟩
    · apply (le_get _ _ _).mpr
      intro p hp he
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hp
      have hu : u = v := he
      subst u
      exact le_rfl
  · rw [ite_eq_right hv]
    apply get_eq_top_of_not_mem
    simpa only [support_ofSet] using hv

theorem nodup_ofSet [LinearOrder V] (K : Finset V) (d : V → Distance) :
    ((ofSet K d).map Prod.fst).Nodup := by
  simpa [ofSet, List.map_map, Function.comp_def] using
    K.sort_nodup (· ≤ ·)

theorem nodup_append (xs ys : Labels V) (hx : (xs.map Prod.fst).Nodup)
    (hy : (ys.map Prod.fst).Nodup) (hd : Disjoint (support xs) (support ys)) :
    ((xs ++ ys).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨hx, hy, ?_⟩
  intro a ha b hb he
  subst b
  exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hb)

def addNew [LinearOrder V] (xs : Labels V) (U : Finset V) (r : Distance) : Labels V :=
  xs ++ ofSet (U \ support xs) (fun _ => r)

theorem support_addNew [LinearOrder V] (xs : Labels V) (U : Finset V) (r : Distance) :
    support (addNew xs U r) = support xs ∪ U := by
  rw [addNew, support_append, support_ofSet]
  ext v
  simp

theorem get_addNew [LinearOrder V] (xs : Labels V) (U : Finset V) (r : Distance) (v : V) :
    get (addNew xs U r) v =
      if v ∈ support xs then get xs v else if v ∈ U then r else ⊤ := by
  rw [addNew, get_append, get_ofSet]
  by_cases hx : v ∈ support xs
  · simp [hx]
  · have he := get_eq_top_of_not_mem xs hx
    simp [hx, he]

theorem nodup_addNew [LinearOrder V] (xs : Labels V) (U : Finset V) (r : Distance)
    (hx : (xs.map Prod.fst).Nodup) : ((addNew xs U r).map Prod.fst).Nodup :=
  nodup_append xs _ hx (nodup_ofSet _ _) (by
    rw [support_ofSet]
    exact Finset.disjoint_left.mpr (fun _ hv hs => (Finset.mem_sdiff.mp hs).2 hv))

end StreamingSSSP.Core.SparseLabels
