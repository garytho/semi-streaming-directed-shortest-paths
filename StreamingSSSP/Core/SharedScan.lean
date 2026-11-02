module

public import StreamingSSSP.Core.Descriptors
public import StreamingSSSP.Core.Packing

@[expose] public section

namespace StreamingSSSP.Core.Shared

open StoredEdges

variable {n nb ns nq : ℕ}

theorem fold_update (c : Catalog n nb ns nq) (input : List (Edge n)) (ws : List (Work n nb nq)) :
    input.foldl (update c) ws = ws.map fun w =>
      { w with
        rows := ViewedSkeleton.scanRows (view c w.job.searchId) (block c w.job.searchId w.job.blockId)
          (SparseLabels.support w.job.sources) w.job.threshold input w.rows } := by
  induction input generalizing ws with
  | nil => simp [ViewedSkeleton.scanRows]
  | cons e es ih =>
      rw [List.foldl_cons, ih]
      simp only [update, List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro w _
      simp only [updateWork, ViewedSkeleton.scanRows]
      congr 2
      apply List.map_congr_left
      intro row _
      exact update_row_eq c w.job e row

theorem scanPack_state (c : Catalog n nb ns nq) (jobs : List (Job n nb nq))
    (stored input : List (Edge n)) :
    (scanPack c jobs stored input).state = jobs.map fun job =>
      Work.mk job (ViewedSkeleton.rows (view c job.searchId) (block c job.searchId job.blockId)
        (SparseLabels.support job.sources) job.threshold stored input) := by
  rw [scanPack, Streaming.readPass_state, ← List.foldl_append, fold_update]
  simp only [List.map_map, Function.comp_def, start]
  apply List.map_congr_left
  intro job _
  congr 1
  exact ViewedSkeleton.scanRows_append _ _ _ _ _ _ _

theorem storedEdges_eq (hn : 0 < n) (c : Catalog n nb ns nq) (jobs : List (Job n nb nq))
    (stored input : List (Edge n)) {w : Work n nb nq}
    (hw : w ∈ (scanPack c jobs stored input).state) :
    storedEdges hn w = ViewedSkeleton.build hn (view c w.job.searchId)
      (block c w.job.searchId w.job.blockId) (SparseLabels.support w.job.sources)
      w.job.threshold stored input := by
  rw [scanPack_state] at hw
  obtain ⟨job, _, rfl⟩ := List.mem_map.mp hw
  rfl

def Valid (c : Catalog n nb ns nq) (job : Job n nb nq) : Prop :=
  0 < (block c job.searchId job.blockId).card ∧ 0 < job.threshold

def Invariant (c : Catalog n nb ns nq) (limit : ℕ) (ws : List (Work n nb nq)) : Prop :=
  (∀ w ∈ ws, Valid c w.job ∧ Skeleton.StateBound
    (block c w.job.searchId w.job.blockId).card w.job.threshold w.rows) ∧
    (ws.map fun w => capacity c w.job).sum ≤ limit

theorem cells_bound (c : Catalog n nb ns nq) (limit : ℕ) (ws : List (Work n nb nq))
    (hi : Invariant c limit ws) : cells ws ≤ 14 * limit := by
  have hpoint (w : Work n nb nq) (hv : Valid c w.job)
      (hb : Skeleton.StateBound (block c w.job.searchId w.job.blockId).card w.job.threshold w.rows) :
      8 + Skeleton.stateCells w.rows ≤ 14 * capacity c w.job := by
    have h := Skeleton.stateCells_le _ _ _ hb
    have hbc : (block c w.job.searchId w.job.blockId).card ≤ capacity c w.job :=
      Nat.le_mul_of_pos_right _ hv.2
    have hc : 0 < capacity c w.job := Nat.mul_pos hv.1 hv.2
    unfold capacity at *
    omega
  have hsum (xs : List (Work n nb nq))
      (hx : ∀ w ∈ xs, Valid c w.job ∧ Skeleton.StateBound
        (block c w.job.searchId w.job.blockId).card w.job.threshold w.rows) :
      cells xs ≤ 14 * (xs.map fun w => capacity c w.job).sum := by
    induction xs with
    | nil => simp [cells]
    | cons w xs ih =>
        have hh := hpoint w (hx w (by simp)).1 (hx w (by simp)).2
        have ht := ih (fun q hq => hx q (by simp [hq]))
        simp only [cells, List.map_cons, List.sum_cons] at *
        omega
  exact (hsum ws hi.1).trans (Nat.mul_le_mul_left 14 hi.2)

theorem update_invariant (c : Catalog n nb ns nq) (limit : ℕ)
    (ws : List (Work n nb nq)) (raw : Edge n) (hi : Invariant c limit ws) :
    Invariant c limit (update c ws raw) := by
  constructor
  · intro w hw
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hv, hb⟩ := hi.1 old ho
    exact ⟨hv, ViewedSkeleton.update_bound _ _ _
      (block c old.job.searchId old.job.blockId).card old.job.threshold raw old.rows hb⟩
  · simpa only [update, List.map_map, Function.comp_def, updateWork] using hi.2

theorem fold_invariant (c : Catalog n nb ns nq) (limit : ℕ)
    (input : List (Edge n)) (ws : List (Work n nb nq)) (hi : Invariant c limit ws) :
    Invariant c limit (input.foldl (update c) ws) := by
  induction input generalizing ws with
  | nil => exact hi
  | cons e es ih => exact ih _ (update_invariant c limit ws e hi)

theorem scanPack_memory (c : Catalog n nb ns nq) (jobs : List (Job n nb nq))
    (stored input : List (Edge n)) (limit : ℕ)
    (hj : ∀ job ∈ jobs, Valid c job) (hc : Packing.load (capacity c) jobs ≤ limit) :
    (scanPack c jobs stored input).peakCells ≤ 14 * limit := by
  have hi : Invariant c limit (jobs.map (start c)) := by
    constructor
    · intro w hw
      obtain ⟨job, hmem, rfl⟩ := List.mem_map.mp hw
      refine ⟨hj job hmem, ?_⟩
      constructor
      · simp [start]
      · intro row hr
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
        exact Nat.zero_le _
    · simpa only [List.map_map, Function.comp_def, start, Packing.load] using hc
  exact (Streaming.readPass_bound _ _ input _ (Invariant c limit) (14 * limit)
    (fold_invariant c limit stored _ hi)
    (fun ws e h => update_invariant c limit ws e h)
    (fun ws h => cells_bound c limit ws h)).2

theorem scanPack_reads (c : Catalog n nb ns nq) (jobs : List (Job n nb nq))
    (stored input : List (Edge n)) :
    (scanPack c jobs stored input).reads = input.length :=
  Streaming.readPass_reads _ _ _ _

end StreamingSSSP.Core.Shared
