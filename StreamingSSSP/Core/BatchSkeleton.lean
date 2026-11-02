module

public import StreamingSSSP.Core.SkeletonMemory
public import StreamingSSSP.Core.Packing
public import StreamingSSSP.Core.Doubling

@[expose] public section

namespace StreamingSSSP.Core.BatchSkeleton

open StoredEdges

variable {n : ℕ}

structure Request (n : ℕ) where
  block : Finset (Fin n)
  known : Finset (Fin n)
  threshold : ℕ

def capacity (job : Request n) : ℕ := job.block.card * job.threshold

def Valid (job : Request n) : Prop := 0 < job.block.card ∧ 0 < job.threshold

structure Work (n : ℕ) where
  request : Request n
  rows : List (Skeleton.Row n)

def initialWork (job : Request n) : Work n :=
  ⟨job, (job.block.sort (· ≤ ·)).map fun a => ⟨a, ∅⟩⟩

def updateWork (e : Edge n) (w : Work n) : Work n :=
  { w with
    rows := w.rows.map (Skeleton.updateRow w.request.block w.request.known w.request.threshold e) }

def update (works : List (Work n)) (e : Edge n) : List (Work n) :=
  works.map (updateWork e)

def cells (works : List (Work n)) : ℕ :=
  (works.map fun w => 2 + Skeleton.stateCells w.rows).sum

def Invariant (limit : ℕ) (works : List (Work n)) : Prop :=
  (∀ w ∈ works, Valid w.request ∧
    Skeleton.StateBound w.request.block.card w.request.threshold w.rows) ∧
    (works.map fun w => capacity w.request).sum ≤ limit

theorem work_cells (w : Work n) (hv : Valid w.request)
    (hb : Skeleton.StateBound w.request.block.card w.request.threshold w.rows) :
    2 + Skeleton.stateCells w.rows ≤ 8 * capacity w.request := by
  have hr := Skeleton.stateCells_le _ _ _ hb
  have hbc : w.request.block.card ≤ capacity w.request := by
    exact Nat.le_mul_of_pos_right _ hv.2
  have hc : 0 < capacity w.request := Nat.mul_pos hv.1 hv.2
  unfold capacity at *
  omega

theorem cells_bound (limit : ℕ) (works : List (Work n)) (hi : Invariant limit works) :
    cells works ≤ 8 * limit := by
  have h (ws : List (Work n))
      (hw : ∀ w ∈ ws, Valid w.request ∧
        Skeleton.StateBound w.request.block.card w.request.threshold w.rows) :
      cells ws ≤ 8 * (ws.map fun w => capacity w.request).sum := by
    induction ws with
    | nil => simp [cells]
    | cons w ws ih =>
        have hcell := work_cells w (hw w (by simp)).1 (hw w (by simp)).2
        have ht := ih (fun q hq => hw q (by simp [hq]))
        simp only [cells, List.map_cons, List.sum_cons] at *
        omega
  exact (h works hi.1).trans (Nat.mul_le_mul_left 8 hi.2)

theorem update_invariant (limit : ℕ) (works : List (Work n)) (e : Edge n)
    (hi : Invariant limit works) : Invariant limit (update works e) := by
  constructor
  · intro w hw
    obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hv, hb⟩ := hi.1 old ho
    exact ⟨hv, Skeleton.update_stateBound old.request.block old.request.known _ _ e _ hb⟩
  · simpa only [update, List.map_map, Function.comp_def, updateWork] using hi.2

def scanPack (jobs : List (Request n)) (input : List (Edge n)) :
    Streaming.Metered (List (Work n)) :=
  Streaming.readPass update cells input (jobs.map initialWork)

theorem scanPack_memory (jobs : List (Request n)) (input : List (Edge n)) (limit : ℕ)
    (hj : ∀ j ∈ jobs, Valid j) (hcap : Packing.load capacity jobs ≤ limit) :
    (scanPack jobs input).peakCells ≤ 8 * limit := by
  have hi : Invariant limit (jobs.map initialWork) := by
    constructor
    · intro w hw
      obtain ⟨j, hmem, rfl⟩ := List.mem_map.mp hw
      refine ⟨hj j hmem, ?_⟩
      constructor
      · simp [initialWork]
      · intro row hr
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
        exact Nat.zero_le _
    · simpa only [List.map_map, initialWork, Function.comp_def, Packing.load] using hcap
  exact (Streaming.readPass_bound update cells input _ (Invariant limit) (8 * limit) hi
    (fun ws e h => update_invariant limit ws e h)
    (fun ws h => cells_bound limit ws h)).2

theorem scanPack_reads (jobs : List (Request n)) (input : List (Edge n)) :
    (scanPack jobs input).reads = input.length :=
  Streaming.readPass_reads _ _ _ _

theorem fold_update (input : List (Edge n)) (works : List (Work n)) :
    input.foldl update works = works.map fun w =>
      { w with
        rows := Skeleton.scanRows w.request.block w.request.known w.request.threshold input w.rows } := by
  induction input generalizing works with
  | nil => simp [Skeleton.scanRows]
  | cons e es ih =>
      simp only [List.foldl_cons, ih, update, List.map_map, Function.comp_def,
        updateWork, Skeleton.scanRows]

theorem scanPack_state (jobs : List (Request n)) (input : List (Edge n)) :
    (scanPack jobs input).state = jobs.map fun j =>
      Work.mk j (Skeleton.rows j.block j.known j.threshold input) := by
  rw [scanPack, Streaming.readPass_state, fold_update]
  simp only [List.map_map, Function.comp_def, initialWork, Skeleton.rows]

def storedEdges (hn : 0 < n) (w : Work n) : List (Edge n) :=
  w.rows.flatMap (Skeleton.rowEdges hn)

theorem storedEdges_correct (hn : 0 < n) (jobs : List (Request n))
    (input : List (Edge n)) {w : Work n} (hw : w ∈ (scanPack jobs input).state) :
    storedEdges hn w = Skeleton.build hn w.request.block w.request.known
      w.request.threshold input := by
  rw [scanPack_state] at hw
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw
  rfl

theorem packed_scan_bound (jobs : List (Request n)) :
    n * (Packing.pack n capacity jobs).length ≤ n + 2 * Packing.load capacity jobs :=
  Packing.pack_scan_bound _ _ _

theorem packed_memory (jobs : List (Request n)) (input : List (Edge n))
    (hj : ∀ j ∈ jobs, Valid j) (hc : ∀ j ∈ jobs, capacity j ≤ n)
    {pack : List (Request n)} (hp : pack ∈ Packing.pack n capacity jobs) :
    (scanPack pack input).peakCells ≤ 8 * n := by
  apply scanPack_memory pack input n
  · intro j hmem
    apply hj j
    have hf : j ∈ (Packing.pack n capacity jobs).flatten :=
      List.mem_flatten.mpr ⟨pack, hp, hmem⟩
    rw [Packing.pack_flatten] at hf
    exact List.mem_reverse.mp hf
  · exact Packing.pack_bounded n capacity jobs hc pack hp

end StreamingSSSP.Core.BatchSkeleton
