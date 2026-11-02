module

public import StreamingSSSP.Hopset.Protocol

@[expose] public section

namespace StreamingSSSP.Hopset

variable {n : ℕ}

def groupKeys (S : Finset (Fin n)) (keep : Fin n → Bool) (key : Fin n → List ℕ) :
    List (List ℕ) :=
  (((members S).filter keep).map key).dedup

def grouped (S : Finset (Fin n)) (keep : Fin n → Bool) (key : Fin n → List ℕ) :
    List (Finset (Fin n)) :=
  (groupKeys S keep key).map fun label => S.filter fun v => keep v = true ∧ key v = label

theorem groupKeys_nodup (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) : (groupKeys S keep key).Nodup :=
  List.nodup_dedup _

theorem groupKeys_mem (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) (label : List ℕ) :
    label ∈ groupKeys S keep key ↔ ∃ v ∈ S, keep v = true ∧ key v = label := by
  simp only [groupKeys, List.mem_dedup, List.mem_map, List.mem_filter, mem_members]
  constructor
  · rintro ⟨v, ⟨hv, hk⟩, he⟩
    exact ⟨v, hv, hk, he⟩
  · rintro ⟨v, hv, hk, he⟩
    exact ⟨v, ⟨hv, hk⟩, he⟩

theorem grouped_subset (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) :
    ∀ T ∈ grouped S keep key, T ⊆ S := by
  intro T hT
  obtain ⟨label, _, rfl⟩ := List.mem_map.mp hT
  exact Finset.filter_subset _ _

theorem grouped_nonempty (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) :
    ∀ T ∈ grouped S keep key, T.Nonempty := by
  intro T hT
  obtain ⟨label, hl, rfl⟩ := List.mem_map.mp hT
  obtain ⟨v, hv, hk, he⟩ := (groupKeys_mem S keep key label).mp hl
  exact ⟨v, Finset.mem_filter.mpr ⟨hv, hk, he⟩⟩

theorem grouped_covers (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) {v : Fin n} (hv : v ∈ S) (hk : keep v = true) :
    ∃ T ∈ grouped S keep key, v ∈ T := by
  let T := S.filter fun w => keep w = true ∧ key w = key v
  have hl : key v ∈ groupKeys S keep key :=
    (groupKeys_mem S keep key _).mpr ⟨v, hv, hk, rfl⟩
  exact ⟨T, List.mem_map.mpr ⟨key v, hl, rfl⟩,
    Finset.mem_filter.mpr ⟨hv, hk, rfl⟩⟩

theorem grouped_card_sum (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) :
    ((grouped S keep key).map Finset.card).sum ≤ S.card := by
  classical
  let K := groupKeys S keep key
  let count := fun label => (S.filter fun v => keep v = true ∧ key v = label).card
  have he : ((grouped S keep key).map Finset.card).sum =
      ∑ label ∈ K.toFinset, count label := by
    simp only [grouped, List.map_map]
    exact (List.sum_toFinset _ (groupKeys_nodup S keep key)).symm
  rw [he]
  simp only [count, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _v ∈ S, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro v hv
      by_cases hk : keep v = true
      · have hkey : key v ∈ K := (groupKeys_mem S keep key _).mpr ⟨v, hv, hk, rfl⟩
        simp [hk, hkey]
      · simp [hk]
    _ = S.card := by simp

theorem grouped_sum_at (S : Finset (Fin n)) (keep : Fin n → Bool)
    (key : Fin n → List ℕ) (v : Fin n) :
    ((grouped S keep key).map fun T => if v ∈ T then (1 : ℝ) else 0).sum ≤ 1 := by
  classical
  let count := fun label => if v ∈ S.filter (fun w => keep w = true ∧ key w = label)
    then (1 : ℝ) else 0
  have he : ((grouped S keep key).map fun T => if v ∈ T then (1 : ℝ) else 0).sum =
    ∑ label ∈ (groupKeys S keep key).toFinset, count label := by
    simp only [grouped, List.map_map]
    exact (List.sum_toFinset count (groupKeys_nodup S keep key)).symm
  rw [he]
  by_cases hv : v ∈ S
  · by_cases hk : keep v = true
    · simp only [count, Finset.mem_filter, hv, hk, true_and]
      rw [Finset.sum_ite_eq]
      split_ifs <;> norm_num
    · simp only [count, Finset.mem_filter, hv, hk, true_and, false_and,
        ↓reduceIte, Finset.sum_const_zero]
      norm_num
  · simp only [count, Finset.mem_filter, hv, false_and, ↓reduceIte, Finset.sum_const_zero]
    norm_num

structure Pivot (n ns : ℕ) where
  setId : Fin ns
  vertex : Fin n
  eta : ℕ
  shift : ℕ
  forward : ℕ
  backward : ℕ

def outFlag (cfg : Config) (r : ℕ) {ns : ℕ} (p : Pivot n ns)
    (reply : Core.BatchAPI.SparseReply n) (v : Fin n) : Bool :=
  withinFraction (lookup reply p.forward v)
    ((p.eta * cfg.shifts + p.shift) * cfg.initialNumerator)
    (cfg.shifts * cfg.denominatorAt r)

def inFlag (cfg : Config) (r : ℕ) {ns : ℕ} (p : Pivot n ns)
    (reply : Core.BatchAPI.SparseReply n) (v : Fin n) : Bool :=
  withinFraction (lookup reply p.backward v)
    ((p.eta * cfg.shifts + p.shift) * cfg.initialNumerator)
    (cfg.shifts * cfg.denominatorAt r)

def labels (cfg : Config) (r : ℕ) {ns : ℕ} (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns) (v : Fin n) : List ℕ :=
  pivots.flatMap fun p =>
    if p.setId = i then
      (if inFlag cfg r p reply v then [2 * p.vertex.val] else []) ++
        if outFlag cfg r p reply v then [2 * p.vertex.val + 1] else []
    else []

def removed (cfg : Config) (r : ℕ) {ns : ℕ} (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns) (v : Fin n) : Bool :=
  pivots.any fun p =>
    decide (p.setId = i) && inFlag cfg r p reply v && outFlag cfg r p reply v

def earlyCore (cfg : Config) (r : ℕ) {ns : ℕ} (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    List (Finset (Fin n)) :=
  (List.finRange ns).flatMap fun i =>
    grouped (sets.get i) (fun v => !removed cfg r pivots reply i v)
      (labels cfg r pivots reply i)

def earlyFringes (cfg : Config) (r : ℕ) {ns : ℕ}
    (sets : Vector (Finset (Fin n)) ns) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) : List (Finset (Fin n)) :=
  pivots.map fun p =>
    fringe cfg r p.eta p.shift (sets.get p.setId) reply p.forward p.backward

def lateBlocks (cfg : Config) (r : ℕ) {ns : ℕ}
    (sets : Vector (Finset (Fin n)) ns) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) : List (Finset (Fin n)) :=
  pivots.map fun p =>
    bothBall cfg r (p.eta + 1) p.shift (sets.get p.setId) reply p.forward p.backward

def lateCore (cfg : Config) (r : ℕ) {ns : ℕ} (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    List (Finset (Fin n)) :=
  (List.finRange ns).map fun i =>
    (sets.get i).filter fun v => labels cfg r pivots reply i v = []

end StreamingSSSP.Hopset
