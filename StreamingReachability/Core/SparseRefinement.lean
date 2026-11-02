module

public import StreamingReachability.Core.SparseDriver

@[expose] public section

namespace StreamingReachability.Core.SparseDriver

open StoredEdges

variable {n b : ℕ}

theorem results_get (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (old : State n b) (i : Fin b) :
    RecordMap.get emptyResult (results hn p stored input r old) i =
      Global.searchOne hn (reference p) ((stored ++ input).filterMap p.edgeView) r i
        ((observe old).blocks.get i) := by
  rw [results, RecordMap.get_map Global.emptyBlock emptyResult old.cache
    (fun i bs => searchBlock hn p stored input r i bs)
    (fun i => searchBlock_empty hn p stored input r i)]
  simp only [Global.searchOne, reference, observe, Vector.get_ofFn]
  exact searchBlock_eq hn p stored input r i _

theorem fresh_eq (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (old : State n b) (hu : RecordMap.Unique old.cache) :
    fresh p stored input r old (resultUnion (results hn p stored input r old)) =
      Global.newVertices (reference p) ((stored ++ input).filterMap p.edgeView) r (observe old)
        (Vector.ofFn fun i =>
          Global.searchOne hn (reference p) ((stored ++ input).filterMap p.edgeView) r i
            ((observe old).blocks.get i)) := by
  have hr := resultUnion_eq (results hn p stored input r old)
    (RecordMap.unique_map old.cache hu (fun i bs => searchBlock hn p stored input r i bs))
  unfold fresh Global.newVertices Global.ordinary
  rw [← List.foldl_append, fold_edgeStep, hr]
  congr 2
  apply Finset.biUnion_congr rfl
  intro i _
  rw [results_get, Vector.get_ofFn]

theorem observe_round (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ)
    (old : State n b) (hu : RecordMap.Unique old.cache) :
    observe (round hn p stored input r old) =
      Global.round hn (reference p) ((stored ++ input).filterMap p.edgeView) r (observe old) := by
  let found := results hn p stored input r old
  let U := fresh p stored input r old (resultUnion found)
  let rs : Vector (Global.BlockResult n) b := Vector.ofFn fun i =>
    Global.searchOne hn (reference p) ((stored ++ input).filterMap p.edgeView) r i
      ((observe old).blocks.get i)
  let Uref := Global.newVertices (reference p) ((stored ++ input).filterMap p.edgeView) r (observe old) rs
  have hU : U = Uref := fresh_eq hn p stored input r old hu
  have hcache (i : Fin b) :
      RecordMap.get Global.emptyBlock
        (commitCache p r U (found.map fun pair => (pair.1, pair.2.state))) i =
      Global.insertExternal (reference p) r Uref i (rs.get i).state := by
    rw [get_commitCache, RecordMap.get_map emptyResult Global.emptyBlock found
      (fun _ result => result.state) (fun _ => rfl)]
    rw [show RecordMap.get emptyResult found i = rs.get i from by
      simpa only [rs, Vector.get_ofFn] using results_get hn p stored input r old i]
    rw [hU]
    simp only [Global.insertExternal, reference, Vector.get_ofFn]
  change (Global.State.mk (SparseLabels.addNew old.labels U (r : Distance))
      (old.settled ∪ U)
      (Vector.ofFn (RecordMap.get Global.emptyBlock
        (commitCache p r U (found.map fun pair => (pair.1, pair.2.state)))))) =
    Global.State.mk (SparseLabels.addNew old.labels Uref (r : Distance))
      (old.settled ∪ Uref)
      (Vector.ofFn fun i => Global.insertExternal (reference p) r Uref i (rs.get i).state)
  rw [hU]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  simpa only [Vector.get_ofFn, ← hU] using hcache ⟨i, hi⟩

theorem observe_initial (p : Parameters n b) :
    observe (initial p) = Global.initial (reference p) := by
  change Global.State.mk [(p.source, 0)] ∅
      (Vector.ofFn (RecordMap.get Global.emptyBlock [])) =
    Global.State.mk [(p.source, 0)] ∅ (Vector.replicate b Global.emptyBlock)
  congr 1
  apply Vector.ext
  intro i hi
  simp [RecordMap.get]

theorem execute_observe (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (r : ℕ) :
    observe (execute hn p stored input r) =
      Global.execute hn (reference p) ((stored ++ input).filterMap p.edgeView) r := by
  induction r with
  | zero => exact observe_initial p
  | succ r ih =>
      rw [execute, observe_round hn p stored input r _ (execute_unique hn p stored input r), ih]
      rfl

def output (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (R : ℕ)
    (v : Fin n) : Distance :=
  let s := execute hn p stored input (R + 1)
  if v ∈ s.settled then SparseLabels.get s.labels v else ⊤

theorem output_eq (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n)) (R : ℕ)
    (v : Fin n) :
    output hn p stored input R v =
      Global.output hn (reference p) ((stored ++ input).filterMap p.edgeView) R v := by
  have he := execute_observe hn p stored input (R + 1)
  have hS := congrArg Global.State.settled he
  have hL := congrArg Global.State.labels he
  unfold output Global.output
  dsimp only
  rw [← hS, ← hL]
  rfl

theorem core_distance_correct (hn : 0 < n) (p : Parameters n b) (stored input : List (Edge n))
    (hp : ∀ e ∈ (stored ++ input).filterMap p.edgeView, 0 < e.weight)
    (hA : 0 < p.scale) (R : ℕ) (v : Fin n) :
    output hn p stored input R v =
      if (fullQueryGraph ((stored ++ input).filterMap p.edgeView)
          (reference p).blocks.toList p.scale).dist p.source v ≤ (R : Distance)
      then (fullQueryGraph ((stored ++ input).filterMap p.edgeView)
          (reference p).blocks.toList p.scale).dist p.source v else ⊤ := by
  rw [output_eq]
  exact Global.core_distance_correct hn (reference p) _ hp hA R v

theorem catalog_core_distance_correct {ns nq : ℕ} (hn : 0 < n)
    (c : Shared.Catalog n b ns nq) (j : Fin nq) (stored input : List (Edge n))
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (v : Fin n) :
    output hn (ofCatalog c j) stored input (c.searches.get j).radius v =
      if (fullQueryGraph ((stored ++ input).filterMap (Shared.view c j))
          (Shared.referenceProblem c j).blocks.toList c.scale).dist (c.searches.get j).source v ≤
            ((c.searches.get j).radius : Distance)
      then (fullQueryGraph ((stored ++ input).filterMap (Shared.view c j))
          (Shared.referenceProblem c j).blocks.toList c.scale).dist (c.searches.get j).source v else ⊤ := by
  apply core_distance_correct hn (ofCatalog c j) stored input
  · apply Shared.viewed_positive
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact hs e he
    · exact hp e he
  · exact hA

end StreamingReachability.Core.SparseDriver
