module

public import StreamingReachability.Hopset.TrialFacts
public import StreamingReachability.Hopset.HistoryTransitions

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

variable {n ns : ℕ}

def selectedVertices (targets : List (Target n ns)) (i : Fin ns) : List (Fin n) :=
  targets.filterMap fun target =>
    if target.kind = .pivot ∧ target.setId = i then some target.vertex else none

theorem selectedVertices_append (left right : List (Target n ns)) (i : Fin ns) :
    selectedVertices (left ++ right) i =
      selectedVertices left i ++ selectedVertices right i := List.filterMap_append

theorem selectedVertices_map (vertices : List (Fin n)) (j i : Fin ns) (kind : TargetKind) :
    selectedVertices (vertices.map fun v => ⟨j, v, kind⟩) i =
      if kind = .pivot ∧ j = i then vertices else [] := by
  by_cases h : kind = .pivot ∧ j = i <;>
    induction vertices with
    | nil => simp [selectedVertices]
    | cons v vertices ih => simp [selectedVertices, h, ih]

theorem selectedVertices_flatMap {A : Type*} (L : List A) (f : A → List (Target n ns))
    (i : Fin ns) :
    selectedVertices (L.flatMap f) i = L.flatMap (fun a => selectedVertices (f a) i) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.flatMap_cons, selectedVertices_append, ih]

theorem flatMap_one_index {A : Type*} (L : List (Fin ns)) (hL : L.Nodup)
    (f : Fin ns → List A) (i : Fin ns) :
    L.flatMap (fun j => if j = i then f j else []) = if i ∈ L then f i else [] := by
  induction L with
  | nil => simp
  | cons j L ih =>
      obtain ⟨hj, hTail⟩ := List.nodup_cons.mp hL
      by_cases he : j = i
      · subst j
        simp only [List.flatMap_cons, ↓reduceIte, ih hTail, hj, List.mem_cons,
          true_or, List.append_nil]
      · simp only [List.flatMap_cons, he, ↓reduceIte, List.nil_append, ih hTail,
          List.mem_cons, Ne.symm he, false_or]

theorem members_filter (S : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    members (S.filter p) = (members S).filter fun v => decide (p v) := by
  unfold members
  rw [List.filter_filter]
  apply List.filter_congr
  intro v hv
  by_cases hS : v ∈ S <;> by_cases hp : p v <;> simp [hS, hp]

theorem members_bool_filter (S : Finset (Fin n)) (p : Fin n → Bool) :
    members (S.filter fun v => p v = true) = (members S).filter p := by
  rw [members_filter]
  congr 1

theorem pivotMembers_eq (cfg : Config) (r : ℕ) (rank : Vector ℕ n) (S : Finset (Fin n))
    (hr : r < cfg.earlyLevel) :
    (members S).filter (fun v => pivotWanted cfg r (rank.get v)) =
      members (CopyHistory.pivots S r (fun v => rank.get v)) := by
  rw [CopyHistory.pivots, members_filter]
  apply List.filter_congr
  intro v hv
  by_cases he : rank.get v = r <;> simp [pivotWanted, he, hr]

theorem earlyTargets_selected (cfg : Config) (r : ℕ) (rank : Vector ℕ n)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (hr : r < cfg.earlyLevel) :
    selectedVertices (earlyTargets cfg r rank sets) i =
      members (CopyHistory.pivots (sets.get i) r (fun v => rank.get v)) := by
  rw [earlyTargets, selectedVertices_flatMap]
  have he (j : Fin ns) :
      selectedVertices
          ((((members (sets.get j)).filter fun v => advanceWanted cfg r (rank.get v)).map
            fun v => ⟨j, v, .advanceStar⟩) ++
          (((members (sets.get j)).filter fun v => pivotWanted cfg r (rank.get v)).map
            fun v => ⟨j, v, .pivot⟩)) i =
        if j = i then (members (sets.get j)).filter (fun v => pivotWanted cfg r (rank.get v)) else [] := by
    rw [selectedVertices_append, selectedVertices_map, selectedVertices_map]
    simp
  simp_rw [he]
  rw [flatMap_one_index _ (List.nodup_finRange ns)]
  simp only [List.mem_finRange, ↓reduceIte]
  exact pivotMembers_eq cfg r rank (sets.get i) hr

def pivotTargets (P : Fin ns → Finset (Fin n)) : List (Target n ns) :=
  (List.finRange ns).flatMap fun j => (members (P j)).map fun v => ⟨j, v, .pivot⟩

theorem selectedVertices_pivot_targets (P : Fin ns → Finset (Fin n)) (i : Fin ns) :
    selectedVertices (pivotTargets P) i = members (P i) := by
  unfold pivotTargets
  rw [selectedVertices_flatMap]
  simp only [selectedVertices_map, true_and]
  rw [flatMap_one_index _ (List.nodup_finRange ns)]
  simp

theorem pivotTargets_valid (sets : Vector (Finset (Fin n)) ns) (P : Fin ns → Finset (Fin n))
    (hP : ∀ i, P i ⊆ sets.get i) :
    ∀ target ∈ pivotTargets P, ValidTarget sets target := by
  intro target ht
  obtain ⟨i, _, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  exact hP i ((mem_members (P i) v).mp hv)

theorem filterMap_get_unique {A B : Type*} (f : A → Option B) (L : List A) :
    (L.filterMap f).Nodup → ∀ (i j : Fin L.length) (b : B),
      f (L.get i) = some b → f (L.get j) = some b → i = j := by
  induction L with
  | nil => intro h i; exact Fin.elim0 i
  | cons a L ih =>
      intro h
      have htail : (L.filterMap f).Nodup := by
        cases he : f a with
        | none => simpa [he] using h
        | some b =>
            have hc : (b :: L.filterMap f).Nodup := by simpa [he] using h
            exact (List.nodup_cons.mp hc).2
      have hsep (b : B) (ha : f a = some b) (j : Fin L.length)
          (hj : f (L.get j) = some b) : False := by
        have hc : (b :: L.filterMap f).Nodup := by simpa [ha] using h
        exact (List.nodup_cons.mp hc).1
          (List.mem_filterMap.mpr ⟨L.get j, List.get_mem L j, hj⟩)
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro b hi hj
          rfl
        · intro b hi hj
          exact False.elim (hsep b (by simpa using hi) j (by simpa using hj))
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro b hi hj
          exact False.elim (hsep b (by simpa using hj) i (by simpa using hi))
        · intro b hi hj
          exact congrArg Fin.succ (ih htail i j b (by simpa using hi) (by simpa using hj))

theorem selected_index_exists (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (v : Fin n) (hv : v ∈ P) :
    ∃ j : Fin targets.length, (targets.get j).kind = .pivot ∧
      (targets.get j).setId = i ∧ (targets.get j).vertex = v := by
  have hm : v ∈ selectedVertices targets i := by rw [hselected]; exact (mem_members P v).mpr hv
  obtain ⟨target, ht, he⟩ := List.mem_filterMap.mp hm
  by_cases hk : target.kind = .pivot ∧ target.setId = i
  · have hv' : target.vertex = v := by simpa [hk] using he
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp ht
    exact ⟨j, hj ▸ hk.1, hj ▸ hk.2, hj ▸ hv'⟩
  · simp [hk] at he

theorem selected_vertex_mem (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (j : Fin targets.length) (hk : (targets.get j).kind = .pivot)
    (hi : (targets.get j).setId = i) : (targets.get j).vertex ∈ P := by
  apply (mem_members P _).mp
  rw [← hselected]
  exact List.mem_filterMap.mpr ⟨targets.get j, List.get_mem targets j,
    by simp only [hk, hi, and_self, ↓reduceIte]⟩

noncomputable def pivotIndex (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (v : {v : Fin n // v ∈ P}) : Fin targets.length :=
  Classical.choose (selected_index_exists targets i P hselected v.val v.property)

theorem pivotIndex_spec (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (v : {v : Fin n // v ∈ P}) :
    (targets.get (pivotIndex targets i P hselected v)).kind = .pivot ∧
      (targets.get (pivotIndex targets i P hselected v)).setId = i ∧
      (targets.get (pivotIndex targets i P hselected v)).vertex = v.val :=
  Classical.choose_spec (selected_index_exists targets i P hselected v.val v.property)

theorem pivotIndex_injective (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P) :
    Function.Injective (pivotIndex targets i P hselected) := by
  intro u v he
  apply Subtype.ext
  calc
    u.val = (targets.get (pivotIndex targets i P hselected u)).vertex :=
      (pivotIndex_spec targets i P hselected u).2.2.symm
    _ = (targets.get (pivotIndex targets i P hselected v)).vertex := by rw [he]
    _ = v.val := (pivotIndex_spec targets i P hselected v).2.2

theorem pivotIndex_active (targets : List (Target n ns)) (i : Fin ns)
    (P : Finset (Fin n)) (hselected : selectedVertices targets i = members P)
    (j : Fin targets.length) (hk : (targets.get j).kind = .pivot)
    (hi : (targets.get j).setId = i) :
    pivotIndex targets i P hselected
      ⟨(targets.get j).vertex, selected_vertex_mem targets i P hselected j hk hi⟩ = j := by
  have hd : (selectedVertices targets i).Nodup := by rw [hselected]; exact members_nodup P
  have hs := pivotIndex_spec targets i P hselected
    ⟨(targets.get j).vertex, selected_vertex_mem targets i P hselected j hk hi⟩
  apply filterMap_get_unique _ targets hd _ j (targets.get j).vertex
  · simp only [hs.1, hs.2.1, hs.2.2, and_self, ↓reduceIte]
  · simp only [hk, hi, and_self, ↓reduceIte]

end StreamingReachability.Hopset
