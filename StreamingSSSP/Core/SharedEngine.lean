module

public import StreamingSSSP.Core.SharedScan
public import StreamingSSSP.Core.Packing
public import StreamingSSSP.Core.RecordMap

@[expose] public section

namespace StreamingSSSP.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

inductive Task (n nb nq : ℕ) where
  | active (job : Job n nb nq)
  | finished (out : BlockSearch.Outcome n)

def addSpent (job : Job n nb nq) (out : BlockSearch.Outcome n) : BlockSearch.Outcome n :=
  { out with scans := job.spentScans + out.scans
             reservations := job.spentReservations + out.reservations }

def evaluate (c : Catalog n nb ns nq) (r : ℕ) (job : Job n nb nq)
    (f : DistanceArray n) : Task n nb nq :=
  let B := block c job.searchId job.blockId
  let K := SparseLabels.support job.sources
  if (found B K f.get (c.scale * r)).card < job.threshold
  then .finished (addSpent job (BlockSearch.finish B K (c.scale * r) job.threshold f))
  else .active (double c job)

def completeWork (hn : 0 < n) (c : Catalog n nb ns nq) (r : ℕ)
    (slot : Fin N × Job n nb nq) (w : Work n nb nq) : Fin N × Task n nb nq :=
  (slot.1, evaluate c r slot.2 (StoredSearch.run (storedEdges hn w) (SparseLabels.vector slot.2.sources)))

def active (tasks : Vector (Task n nb nq) N) : List (Fin N × Job n nb nq) :=
  (List.finRange N).filterMap fun i =>
    match tasks.get i with
    | .active job => some (i, job)
    | .finished _ => none

def executePack (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n)) (r : ℕ)
    (slots : List (Fin N × Job n nb nq)) : RecordMap.Map (Fin N) (Task n nb nq) :=
  slots.zipWith (completeWork hn c r)
    (scanPack c (slots.map Prod.snd) stored input).state

noncomputable def localStep (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (task : Task n nb nq) : Task n nb nq :=
  match task with
  | .finished out => .finished out
  | .active job =>
      evaluate c r job (ViewedSkeleton.labels hn (view c job.searchId)
        (block c job.searchId job.blockId) (SparseLabels.support job.sources)
        job.threshold (SparseLabels.vector job.sources) stored input)

noncomputable def slotStep (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (slot : Fin N × Job n nb nq) :
    Fin N × Task n nb nq :=
  (slot.1, localStep hn c stored input r (.active slot.2))

theorem executePack_eq (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (slots : List (Fin N × Job n nb nq)) :
    executePack hn c stored input r slots = slots.map (slotStep hn c stored input r) := by
  unfold executePack
  rw [scanPack_state]
  simp only [List.map_map, Function.comp_def]
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, ih]
      rfl

structure Phase (n nb nq N : ℕ) where
  updates : RecordMap.Map (Fin N) (Task n nb nq)
  scans : ℕ
  reads : ℕ
  peakRows : ℕ

def executePackResult (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ)
    (slots : List (Fin N × Job n nb nq)) : Phase n nb nq N :=
  let scanned := scanPack c (slots.map Prod.snd) stored input
  { updates := slots.zipWith (completeWork hn c r) scanned.state
    scans := 1
    reads := scanned.reads
    peakRows := scanned.peakCells }

def executePacks (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) :
    List (List (Fin N × Job n nb nq)) → Phase n nb nq N
  | [] => ⟨[], 0, 0, 0⟩
  | slots :: rest =>
      let first := executePackResult hn c stored input r slots
      let tail := executePacks hn c stored input r rest
      ⟨first.updates ++ tail.updates, tail.scans + 1,
        first.reads + tail.reads, max first.peakRows tail.peakRows⟩

def phase (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (tasks : Vector (Task n nb nq) N) : Phase n nb nq N :=
  executePacks hn c stored input r (Packing.pack n (fun slot => capacity c slot.2) (active tasks))

def nextTasks (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (tasks : Vector (Task n nb nq) N) :
    Vector (Task n nb nq) N :=
  let replies := phase hn c stored input r tasks
  Vector.ofFn fun i => RecordMap.get (tasks.get i) replies.updates i

theorem executePacks_eq (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (packs : List (List (Fin N × Job n nb nq))) :
    (executePacks hn c stored input r packs).updates =
      packs.flatten.map (slotStep hn c stored input r) := by
  induction packs with
  | nil => rfl
  | cons pack rest ih =>
      change executePack hn c stored input r pack ++
        (executePacks hn c stored input r rest).updates = _
      rw [executePack_eq, ih, List.flatten_cons, List.map_append]

theorem phase_eq (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (tasks : Vector (Task n nb nq) N) :
    (phase hn c stored input r tasks).updates =
      (active tasks).reverse.map (slotStep hn c stored input r) := by
  rw [phase, executePacks_eq, Packing.pack_flatten]

theorem active_mem (tasks : Vector (Task n nb nq) N) (i : Fin N) (job : Job n nb nq) :
    (i, job) ∈ active tasks ↔ tasks.get i = .active job := by
  unfold active
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, _, hk⟩
    cases ht : tasks.get k with
    | finished out => simp only [ht] at hk; cases hk
    | active q =>
        have he : (k, q) = (i, job) := by simpa only [ht, Option.some.injEq] using hk
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        exact ht
  · intro ht
    exact ⟨i, List.mem_finRange i, by simp only [ht]⟩

theorem active_unique (tasks : Vector (Task n nb nq) N) :
    RecordMap.Unique (active tasks) := by
  have h (indices : List (Fin N)) :
      ((indices.filterMap fun i =>
        match tasks.get i with
        | .active job => some (i, job)
        | .finished _ => none).map Prod.fst) =
      indices.filter (fun i => match tasks.get i with | .active _ => true | .finished _ => false) := by
    induction indices with
    | nil => rfl
    | cons i is ih =>
        cases ht : tasks.get i <;> simp only [List.filterMap_cons, ht, List.map_cons,
          List.filter_cons, Bool.false_eq_true, ↓reduceIte, ih]
  unfold RecordMap.Unique active
  rw [h]
  exact (List.nodup_finRange N).filter _

theorem nextTasks_get (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (tasks : Vector (Task n nb nq) N) (i : Fin N) :
    (nextTasks hn c stored input r tasks).get i = localStep hn c stored input r (tasks.get i) := by
  rw [nextTasks, Vector.get_ofFn, phase_eq]
  have hu : RecordMap.Unique ((active tasks).reverse.map (slotStep hn c stored input r)) := by
    simpa [RecordMap.Unique, List.map_map, Function.comp_def, slotStep, List.map_reverse] using
      active_unique tasks
  cases ht : tasks.get i with
  | active job =>
      have hm : (i, localStep hn c stored input r (.active job)) ∈
          (active tasks).reverse.map (slotStep hn c stored input r) :=
        List.mem_map.mpr ⟨(i, job), List.mem_reverse.mpr ((active_mem tasks i job).mpr ht), rfl⟩
      rw [RecordMap.get_mem _ _ hu hm]
  | finished out =>
      rw [RecordMap.get_of_not_mem]
      · rfl
      · intro hm
        simp only [RecordMap.keys, List.map_map, Function.comp_def, slotStep, List.mem_toFinset] at hm
        obtain ⟨slot, hs, he⟩ := List.mem_map.mp hm
        obtain ⟨k, job⟩ := slot
        have hi : k = i := he
        subst k
        have hbad := (active_mem tasks i job).mp (List.mem_reverse.mp hs)
        rw [ht] at hbad
        cases hbad

end StreamingSSSP.Core.Shared.Engine
