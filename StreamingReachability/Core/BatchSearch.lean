module

public import StreamingReachability.Core.BatchSkeleton
public import StreamingReachability.Core.SparseLabels

@[expose] public section

namespace StreamingReachability.Core.BatchSearch

open StoredEdges

variable {n : ℕ}

structure Query (n : ℕ) where
  id : ℕ
  request : BatchSkeleton.Request n
  sources : SparseLabels.Labels (Fin n)
  radiusNumerator : ℕ

def capacity (q : Query n) : ℕ := BatchSkeleton.capacity q.request

inductive Stage (n : ℕ) where
  | returned (outcome : BlockSearch.Outcome n)
  | retry

def evaluate (q : Query n) (f : DistanceArray n) : Stage n :=
  if (found q.request.block q.request.known f.get q.radiusNumerator).card < q.request.threshold
  then .returned (BlockSearch.finish q.request.block q.request.known
    q.radiusNumerator q.request.threshold f)
  else .retry

def completeWork (hn : 0 < n) (q : Query n) (w : BatchSkeleton.Work n) : Query n × Stage n :=
  (q, evaluate q (StoredSearch.run (BatchSkeleton.storedEdges hn w)
    (SparseLabels.vector q.sources)))

def executePack (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n)) :
    List (Query n × Stage n) :=
  jobs.zipWith (completeWork hn)
    (BatchSkeleton.scanPack (jobs.map Query.request) input).state

def semanticStage (hn : 0 < n) (input : List (Edge n)) (q : Query n) : Query n × Stage n :=
  (q, evaluate q (BlockSearch.labels hn q.request.block q.request.known
    q.request.threshold (SparseLabels.vector q.sources) input))

@[simp] theorem semanticStage_fst (hn : 0 < n) (input : List (Edge n)) (q : Query n) :
    (semanticStage hn input q).1 = q := rfl

theorem executePack_correct (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n)) :
    executePack hn input jobs = jobs.map (semanticStage hn input) := by
  unfold executePack
  rw [BatchSkeleton.scanPack_state]
  simp only [List.map_map, Function.comp_def]
  induction jobs with
  | nil => rfl
  | cons q qs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, ih]
      rfl

structure Phase (n : ℕ) where
  stages : List (Query n × Stage n)
  scans : ℕ
  reads : ℕ
  peakRows : ℕ

def executePacks (hn : 0 < n) (input : List (Edge n)) : List (List (Query n)) → Phase n
  | [] => ⟨[], 0, 0, 0⟩
  | jobs :: rest =>
      let scanned := BatchSkeleton.scanPack (jobs.map Query.request) input
      let results := jobs.zipWith (completeWork hn) scanned.state
      let tail := executePacks hn input rest
      ⟨results ++ tail.stages, tail.scans + 1,
        scanned.reads + tail.reads, max scanned.peakCells tail.peakRows⟩

theorem executePacks_correct (hn : 0 < n) (input : List (Edge n))
    (packs : List (List (Query n))) :
    (executePacks hn input packs).stages = packs.flatten.map (semanticStage hn input) := by
  induction packs with
  | nil => rfl
  | cons jobs rest ih =>
      change executePack hn input jobs ++ (executePacks hn input rest).stages = _
      rw [executePack_correct, ih, List.flatten_cons, List.map_append]

theorem executePacks_scans (hn : 0 < n) (input : List (Edge n))
    (packs : List (List (Query n))) :
    (executePacks hn input packs).scans = packs.length := by
  induction packs with
  | nil => rfl
  | cons jobs rest ih => simpa only [executePacks, List.length_cons] using congrArg (· + 1) ih

theorem executePacks_reads (hn : 0 < n) (input : List (Edge n))
    (packs : List (List (Query n))) :
    (executePacks hn input packs).reads = input.length * packs.length := by
  induction packs with
  | nil => simp [executePacks]
  | cons jobs rest ih =>
      simp only [executePacks, BatchSkeleton.scanPack_reads, ih, List.length_cons,
        Nat.mul_add, Nat.mul_one]
      omega

theorem executePacks_memory (hn : 0 < n) (input : List (Edge n))
    (packs : List (List (Query n)))
    (hv : ∀ pack ∈ packs, ∀ q ∈ pack, BatchSkeleton.Valid q.request)
    (hc : ∀ pack ∈ packs, Packing.load capacity pack ≤ n) :
    (executePacks hn input packs).peakRows ≤ 8 * n := by
  induction packs with
  | nil => exact Nat.zero_le _
  | cons jobs rest ih =>
      apply max_le
      · apply BatchSkeleton.scanPack_memory _ input n
        · intro j hj
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hj
          exact hv jobs (by simp) q hq
        · unfold Packing.load
          rw [List.map_map]
          exact hc jobs (by simp)
      · exact ih (fun p hp => hv p (by simp [hp])) (fun p hp => hc p (by simp [hp]))

def runPhase (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n)) : Phase n :=
  executePacks hn input (Packing.pack n capacity jobs)

theorem runPhase_correct (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n)) :
    (runPhase hn input jobs).stages = jobs.reverse.map (semanticStage hn input) := by
  rw [runPhase, executePacks_correct, Packing.pack_flatten]

theorem runPhase_scan_bound (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n)) :
    n * (runPhase hn input jobs).scans ≤ n + 2 * Packing.load capacity jobs := by
  rw [runPhase, executePacks_scans]
  exact Packing.pack_scan_bound _ _ _

theorem runPhase_memory (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n))
    (hv : ∀ q ∈ jobs, BatchSkeleton.Valid q.request)
    (hc : ∀ q ∈ jobs, capacity q ≤ n) :
    (runPhase hn input jobs).peakRows ≤ 8 * n := by
  apply executePacks_memory hn input _
  · intro pack hp q hq
    have hm : q ∈ (Packing.pack n capacity jobs).flatten := List.mem_flatten.mpr ⟨pack, hp, hq⟩
    rw [Packing.pack_flatten] at hm
    exact hv q (List.mem_reverse.mp hm)
  · exact Packing.pack_bounded n capacity jobs hc

theorem completeWork_memory (hn : 0 < n) (input : List (Edge n))
    (jobs : List (BatchSkeleton.Request n)) {w : BatchSkeleton.Work n}
    (hw : w ∈ (BatchSkeleton.scanPack jobs input).state)
    (initial : DistanceArray n) (round scanned : ℕ) :
    workspaceCells (BatchSkeleton.storedEdges hn w)
      (runRounds (BatchSkeleton.storedEdges hn w) round initial)
      (relaxEdges ((BatchSkeleton.storedEdges hn w).take scanned)
        (runRounds (BatchSkeleton.storedEdges hn w) round initial)
        (runRounds (BatchSkeleton.storedEdges hn w) round initial)) ≤
      3 * BatchSkeleton.capacity w.request + 2 * n := by
  rw [workspaceCells_eq, BatchSkeleton.storedEdges_correct hn jobs input hw]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 3 (Skeleton.length_le hn _ _ _ input)) _

end StreamingReachability.Core.BatchSearch
