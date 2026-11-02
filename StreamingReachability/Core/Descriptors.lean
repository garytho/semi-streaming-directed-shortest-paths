module

public import StreamingReachability.Core.ViewedSkeleton
public import StreamingReachability.Core.GlobalMain

@[expose] public section

namespace StreamingReachability.Core.Shared

open StoredEdges

structure Search (n ns : ℕ) where
  setId : Fin ns
  source : Fin n
  backward : Bool
  radius : ℕ

structure Catalog (n nb ns nq : ℕ) where
  scale : ℕ
  blocks : Vector (Finset (Fin n)) nb
  sets : Vector (Finset (Fin n)) ns
  searches : Vector (Search n ns) nq

variable {n nb ns nq : ℕ}

def vertices (c : Catalog n nb ns nq) (j : Fin nq) : Finset (Fin n) :=
  c.sets.get (c.searches.get j).setId

def block (c : Catalog n nb ns nq) (j : Fin nq) (i : Fin nb) : Finset (Fin n) :=
  c.blocks.get i ∩ vertices c j

def view (c : Catalog n nb ns nq) (j : Fin nq) (raw : Edge n) : Option (Edge n) :=
  if raw.source ∈ vertices c j ∧ raw.target ∈ vertices c j
  then some (OrdinaryScan.orient (c.searches.get j).backward raw) else none

theorem view_properties (c : Catalog n nb ns nq) (j : Fin nq) (raw e : Edge n)
    (he : view c j raw = some e) :
    e.source ∈ vertices c j ∧ e.target ∈ vertices c j ∧ e.weight = raw.weight := by
  unfold view at he
  split_ifs at he with h
  have heq := Option.some.inj he
  subst e
  cases hb : (c.searches.get j).backward <;>
    simp [OrdinaryScan.orient, hb, h.1, h.2]

theorem viewed_positive (c : Catalog n nb ns nq) (j : Fin nq)
    (input : List (Edge n)) (hp : ∀ e ∈ input, 0 < e.weight) :
    ∀ e ∈ input.filterMap (view c j), 0 < e.weight := by
  intro e he
  obtain ⟨raw, hr, hview⟩ := List.mem_filterMap.mp he
  rw [(view_properties c j raw e hview).2.2]
  exact hp raw hr

noncomputable def referenceProblem (c : Catalog n nb ns nq) (j : Fin nq) : Global.Problem n nb :=
  ⟨c.scale, (c.searches.get j).source, Vector.ofFn (block c j)⟩

structure Job (n nb nq : ℕ) where
  searchId : Fin nq
  blockId : Fin nb
  sources : SparseLabels.Labels (Fin n)
  threshold : ℕ
  spentScans : ℕ
  spentReservations : ℕ
  deriving DecidableEq

def capacity (c : Catalog n nb ns nq) (job : Job n nb nq) : ℕ :=
  (block c job.searchId job.blockId).card * job.threshold

def double (c : Catalog n nb ns nq) (job : Job n nb nq) : Job n nb nq :=
  { job with
    threshold := 2 * job.threshold
    spentScans := job.spentScans + 1
    spentReservations := job.spentReservations + capacity c job }

structure Work (n nb nq : ℕ) where
  job : Job n nb nq
  rows : List (Skeleton.Row n)

def start (c : Catalog n nb ns nq) (job : Job n nb nq) : Work n nb nq :=
  ⟨job, ((block c job.searchId job.blockId).sort (· ≤ ·)).map fun a => ⟨a, ∅⟩⟩

def updateWork (c : Catalog n nb ns nq) (raw : Edge n) (w : Work n nb nq) : Work n nb nq :=
  { w with
    rows := w.rows.map (ViewedSkeleton.update (view c w.job.searchId) (c.blocks.get w.job.blockId)
      (SparseLabels.support w.job.sources) w.job.threshold raw) }

theorem update_row_eq (c : Catalog n nb ns nq) (job : Job n nb nq) (raw : Edge n)
    (row : Skeleton.Row n) :
    ViewedSkeleton.update (view c job.searchId) (c.blocks.get job.blockId)
        (SparseLabels.support job.sources) job.threshold raw row =
      ViewedSkeleton.update (view c job.searchId) (block c job.searchId job.blockId)
        (SparseLabels.support job.sources) job.threshold raw row := by
  cases hv : view c job.searchId raw with
  | none => simp [ViewedSkeleton.update, hv]
  | some e =>
      have he := (view_properties c job.searchId raw e hv).2.1
      have hel : Skeleton.eligible (c.blocks.get job.blockId)
          (SparseLabels.support job.sources) row.source e ↔
          Skeleton.eligible (block c job.searchId job.blockId)
            (SparseLabels.support job.sources) row.source e := by
        simp only [Skeleton.eligible, block, Finset.mem_inter, he, and_true]
      simp only [ViewedSkeleton.update, hv, Skeleton.updateRow, hel]

def update (c : Catalog n nb ns nq) (ws : List (Work n nb nq)) (raw : Edge n) :
    List (Work n nb nq) := ws.map (updateWork c raw)

def cells (ws : List (Work n nb nq)) : ℕ :=
  (ws.map fun w => 8 + Skeleton.stateCells w.rows).sum

def scanPack (c : Catalog n nb ns nq) (jobs : List (Job n nb nq))
    (stored input : List (Edge n)) : Streaming.Metered (List (Work n nb nq)) :=
  Streaming.readPass (update c) cells input
    (stored.foldl (update c) (jobs.map (start c)))

def storedEdges (hn : 0 < n) (w : Work n nb nq) : List (Edge n) :=
  w.rows.flatMap (Skeleton.rowEdges hn)

theorem block_card_le (c : Catalog n nb ns nq) (j : Fin nq) (i : Fin nb) :
    (block c j i).card ≤ (c.blocks.get i).card :=
  Finset.card_le_card Finset.inter_subset_left

end StreamingReachability.Core.Shared
