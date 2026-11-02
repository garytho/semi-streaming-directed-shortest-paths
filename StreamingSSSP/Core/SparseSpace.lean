module

public import StreamingSSSP.Core.SparseRefinement

@[expose] public section

namespace StreamingSSSP.Core.SparseDriver

open StoredEdges

variable {n b : ℕ}

def Active (cache : RecordMap.Map (Fin b) (Global.BlockState n)) : Prop :=
  ∀ pair ∈ cache, 0 < pair.2.known.length

structure Shape (s : State n b) : Prop where
  unique : RecordMap.Unique s.cache
  active : Active s.cache
  labels_unique : (s.labels.map Prod.fst).Nodup
  labels_nonempty : 0 < s.labels.length
  settled_stored : s.settled ⊆ SparseLabels.support s.labels

theorem all_set {K S : Type*} [DecidableEq K] (P : K × S → Prop)
    (xs : RecordMap.Map K S) (hx : ∀ p ∈ xs, P p) (k : K) (s : S) (hs : P (k, s)) :
    ∀ p ∈ RecordMap.set k s xs, P p := by
  induction xs with
  | nil => simpa [RecordMap.set] using hs
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · simp only [RecordMap.set, hp, ↓reduceIte]
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hs
        · exact hx q (by simp [hq])
      · simp only [RecordMap.set, hp, ↓reduceIte]
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hx q (by simp)
        · exact ih (fun z hz => hx z (by simp [hz])) q hq

theorem search_known_monotone (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n))
    (r : ℕ) (i : Fin b) (old : Global.BlockState n) :
    old.known.length ≤ (searchBlock hn p stored input r i old).state.known.length := by
  unfold searchBlock
  split_ifs
  · simp only [List.length_append]
    exact Nat.le_add_right _ _
  · exact le_rfl

theorem external_active (A r : ℕ) (B U : Finset (Fin n)) (old : Global.BlockState n)
    (hu : 0 < (U ∩ B).card) : 0 < (Global.externalBlock A r B U old).known.length := by
  by_cases ho : old.known = []
  · simpa [Global.externalBlock, ho, SparseLabels.support, SparseLabels.ofSet] using hu
  · have hpos : 0 < old.known.length := by cases hk : old.known <;> simp_all
    have hle : old.known.length ≤ (Global.externalBlock A r B U old).known.length := by
      simp only [Global.externalBlock, List.length_append]
      exact Nat.le_add_right _ _
    exact hpos.trans_le hle

theorem commitCache_active (p : Parameters n b) (r : ℕ) (U : Finset (Fin n))
    (cache : RecordMap.Map (Fin b) (Global.BlockState n)) (ha : Active cache) :
    Active (commitCache p r U cache) := by
  have h (indices : List (Fin b)) (xs : RecordMap.Map (Fin b) (Global.BlockState n)) (hx : Active xs) :
      Active (RecordMap.foldModify Global.emptyBlock
        (fun i => Global.externalBlock p.scale r (p.blockAt i) U)
        (fun i => decide (0 < (U ∩ p.blockAt i).card)) indices xs) := by
    induction indices generalizing xs with
    | nil => exact hx
    | cons i is ih =>
        unfold RecordMap.foldModify
        rw [List.foldl_cons]
        apply ih
        split_ifs with hg
        · exact all_set (fun pair : Fin b × Global.BlockState n => 0 < pair.2.known.length) xs hx i _
            (external_active _ _ _ _ _ (of_decide_eq_true hg))
        · exact hx
  exact h _ cache ha

theorem round_shape (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (old : State n b) (h : Shape old) : Shape (round hn p stored input r old) := by
  refine ⟨round_unique hn p stored input r old h.unique, ?_, ?_, ?_, ?_⟩
  · apply commitCache_active
    intro pair hp
    obtain ⟨result, hr, rfl⟩ := List.mem_map.mp hp
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hr
    exact (h.active original ho).trans_le (search_known_monotone hn p stored input r _ _)
  · exact SparseLabels.nodup_addNew old.labels _ _ h.labels_unique
  · change 0 < (old.labels ++ _).length
    rw [List.length_append]
    have hn := h.labels_nonempty
    omega
  · change old.settled ∪ _ ⊆ SparseLabels.support (SparseLabels.addNew old.labels _ _)
    rw [SparseLabels.support_addNew]
    exact Finset.union_subset_union h.settled_stored (Finset.Subset.refl _)

theorem execute_shape (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ) :
    Shape (execute hn p stored input r) := by
  induction r with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [execute, initial, RecordMap.Unique, Active]
  | succ r ih => exact round_shape hn p stored input r _ ih

def membershipRecords (s : State n b) : ℕ :=
  (s.cache.map fun pair => pair.2.known.length).sum

def distanceRecords (s : State n b) : ℕ := s.labels.length + membershipRecords s

def stateCells (s : State n b) : ℕ :=
  6 + 4 * s.labels.length + 2 * s.settled.card + 8 * s.cache.length + 4 * membershipRecords s

theorem active_count_le (cache : RecordMap.Map (Fin b) (Global.BlockState n)) (ha : Active cache) :
    cache.length ≤ (cache.map fun pair => pair.2.known.length).sum := by
  induction cache with
  | nil => simp
  | cons pair ps ih =>
      have hh := ha pair (by simp)
      have ht := ih (fun p hp => ha p (by simp [hp]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

theorem stateCells_bound (s : State n b) (h : Shape s) :
    stateCells s ≤ 12 * distanceRecords s := by
  have hc := active_count_le s.cache h.active
  have hs : s.settled.card ≤ s.labels.length := by
    have he := SparseLabels.length_eq_card s.labels h.labels_unique
    exact (Finset.card_le_card h.settled_stored).trans_eq he.symm
  have hn := h.labels_nonempty
  unfold stateCells distanceRecords membershipRecords at *
  omega

theorem execute_space (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ) :
    stateCells (execute hn p stored input r) ≤
      12 * distanceRecords (execute hn p stored input r) :=
  stateCells_bound _ (execute_shape hn p stored input r)

end StreamingSSSP.Core.SparseDriver
