module

public import StreamingSSSP.Core.Descriptors

@[expose] public section

namespace StreamingSSSP.Core.SparseDriver

open StoredEdges

variable {n b : ℕ}

structure Parameters (n b : ℕ) where
  scale : ℕ
  source : Fin n
  blockAt : Fin b → Finset (Fin n)
  edgeView : Edge n → Option (Edge n)

def ofCatalog {ns nq : ℕ} (c : Shared.Catalog n b ns nq) (j : Fin nq) : Parameters n b :=
  ⟨c.scale, (c.searches.get j).source, Shared.block c j, Shared.view c j⟩

noncomputable def reference (p : Parameters n b) : Global.Problem n b :=
  ⟨p.scale, p.source, Vector.ofFn p.blockAt⟩

structure State (n b : ℕ) where
  labels : SparseLabels.Labels (Fin n)
  settled : Finset (Fin n)
  cache : RecordMap.Map (Fin b) (Global.BlockState n)

def initial (p : Parameters n b) : State n b := ⟨[(p.source, 0)], ∅, []⟩

noncomputable def observe (s : State n b) : Global.State n b :=
  ⟨s.labels, s.settled, Vector.ofFn (RecordMap.get Global.emptyBlock s.cache)⟩

def emptyResult : Global.BlockResult n := ⟨Global.emptyBlock, ∅, 0, 0⟩

def searchBlock (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (i : Fin b) (old : Global.BlockState n) : Global.BlockResult n :=
  if old.next = (r : Distance) then
    let out := (ViewedSkeleton.search hn p.edgeView (p.blockAt i) (SparseLabels.support old.known)
      (p.scale * r) (SparseLabels.vector old.known) stored input).getD Global.emptyOutcome
    ⟨⟨old.known ++ out.records, roundDistance p.scale out.nextNumerator,
        ScheduleCharge.searched old.charge out.vertices.card, old.reservations + out.reservations⟩,
      out.vertices, out.scans, out.reservations⟩
  else ⟨old, ∅, 0, 0⟩

theorem searchBlock_eq (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (i : Fin b) (old : Global.BlockState n) :
    searchBlock hn p stored input r i old =
      Global.searchBlock hn p.scale (p.blockAt i) ((stored ++ input).filterMap p.edgeView) r old := by
  unfold searchBlock Global.searchBlock
  split_ifs
  · rw [ViewedSkeleton.search_eq]
  · rfl

theorem searchBlock_empty (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n))
    (r : ℕ) (i : Fin b) :
    searchBlock hn p stored input r i Global.emptyBlock = emptyResult := by
  simp [searchBlock, Global.emptyBlock, emptyResult]

def edgeStep (p : Parameters n b) (r : ℕ) (s : State n b) (C : Finset (Fin n))
    (raw : Edge n) : Finset (Fin n) :=
  match p.edgeView raw with
  | none => C
  | some e => Global.edgeStep p.scale r s.labels s.settled C e

theorem fold_edgeStep (p : Parameters n b) (r : ℕ) (s : State n b)
    (input : List (Edge n)) (C : Finset (Fin n)) :
    input.foldl (edgeStep p r s) C =
      (input.filterMap p.edgeView).foldl (Global.edgeStep p.scale r s.labels s.settled) C := by
  induction input generalizing C with
  | nil => rfl
  | cons raw es ih =>
      cases he : p.edgeView raw with
      | none => simpa only [List.foldl_cons, List.filterMap_cons, he, edgeStep] using ih C
      | some e =>
          simpa only [List.foldl_cons, List.filterMap_cons, he, edgeStep] using
            (ih (Global.edgeStep p.scale r s.labels s.settled C e))

def resultUnion : RecordMap.Map (Fin b) (Global.BlockResult n) → Finset (Fin n)
  | [] => ∅
  | p :: ps => p.2.vertices ∪ resultUnion ps

theorem resultUnion_mem (xs : RecordMap.Map (Fin b) (Global.BlockResult n)) (v : Fin n) :
    v ∈ resultUnion xs ↔ ∃ p ∈ xs, v ∈ p.2.vertices := by
  induction xs with
  | nil => simp [resultUnion]
  | cons p ps ih => simp [resultUnion, ih]

theorem resultUnion_eq (xs : RecordMap.Map (Fin b) (Global.BlockResult n))
    (hu : RecordMap.Unique xs) :
    resultUnion xs = Finset.univ.biUnion (fun i => (RecordMap.get emptyResult xs i).vertices) := by
  ext v
  rw [resultUnion_mem, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨i, result⟩, hp, hv⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rwa [RecordMap.get_mem emptyResult xs hu hp]
  · rintro ⟨i, _, hv⟩
    have hi : i ∈ RecordMap.keys xs := by
      by_contra h
      rw [RecordMap.get_of_not_mem emptyResult xs h] at hv
      simp [emptyResult] at hv
    exact ⟨_, RecordMap.exists_get_mem emptyResult xs hi, hv⟩

def results (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (s : State n b) : RecordMap.Map (Fin b) (Global.BlockResult n) :=
  s.cache.map fun pair => (pair.1, searchBlock hn p stored input r pair.1 pair.2)

def fresh (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ) (s : State n b)
    (found : Finset (Fin n)) : Finset (Fin n) :=
  ((if r = 0 then {p.source} else ∅) ∪
    input.foldl (edgeStep p r s) (stored.foldl (edgeStep p r s) ∅) ∪ found) \ s.settled

def commitCache (p : Parameters n b) (r : ℕ) (U : Finset (Fin n))
    (cache : RecordMap.Map (Fin b) (Global.BlockState n)) :
    RecordMap.Map (Fin b) (Global.BlockState n) :=
  RecordMap.foldModify Global.emptyBlock (fun i => Global.externalBlock p.scale r (p.blockAt i) U)
    (fun i => decide (0 < (U ∩ p.blockAt i).card)) (List.finRange b) cache

theorem external_noop (A r : ℕ) (B U : Finset (Fin n)) (old : Global.BlockState n)
    (h : (U ∩ B).card = 0) : Global.externalBlock A r B U old = old := by
  have he : U ∩ B = ∅ := Finset.card_eq_zero.mp h
  simp [Global.externalBlock, he, SparseLabels.ofSet]

theorem get_commitCache (p : Parameters n b) (r : ℕ) (U : Finset (Fin n))
    (cache : RecordMap.Map (Fin b) (Global.BlockState n)) (i : Fin b) :
    RecordMap.get Global.emptyBlock (commitCache p r U cache) i =
      Global.externalBlock p.scale r (p.blockAt i) U (RecordMap.get Global.emptyBlock cache i) := by
  rw [commitCache, RecordMap.get_foldModify _ _ _ _ (List.nodup_finRange b)]
  simp only [List.mem_finRange, true_and, decide_eq_true_eq]
  split_ifs with h
  · rfl
  · exact (external_noop _ _ _ _ _ (by omega)).symm

def round (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (old : State n b) : State n b :=
  let found := results hn p stored input r old
  let U := fresh p stored input r old (resultUnion found)
  { labels := SparseLabels.addNew old.labels U (r : Distance)
    settled := old.settled ∪ U
    cache := commitCache p r U (found.map fun pair => (pair.1, pair.2.state)) }

theorem round_unique (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (old : State n b) (hu : RecordMap.Unique old.cache) :
    RecordMap.Unique (round hn p stored input r old).cache := by
  apply RecordMap.unique_foldModify
  exact RecordMap.unique_map _
    (RecordMap.unique_map old.cache hu (fun i bs => searchBlock hn p stored input r i bs))
    (fun _ result => result.state)

def execute (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) : ℕ → State n b
  | 0 => initial p
  | r + 1 => round hn p stored input r (execute hn p stored input r)

theorem execute_unique (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ) :
    RecordMap.Unique (execute hn p stored input r).cache := by
  induction r with
  | zero => simp [execute, initial, RecordMap.Unique]
  | succ r ih => exact round_unique hn p stored input r _ ih

end StreamingSSSP.Core.SparseDriver
