module

public import StreamingReachability.Core.GuardedWorkspace
public import StreamingReachability.Core.GuardedProposals

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

structure PrefixFacts (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (registry : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq) : Prop where
  valid : RecordGuard.Valid c budget registry
  cover : Cover registry state.states
  shape : ∀ j, SparseDriver.Shape (state.states.get j)
  known : ∀ j i,
    ((RecordMap.get Global.emptyBlock (state.states.get j).cache i).known.map Prod.fst).Nodup ∧
    SparseLabels.support (RecordMap.get Global.emptyBlock (state.states.get j).cache i).known ⊆
      SparseLabels.support (state.states.get j).labels ∩ c.blocks.get i
  source : ∀ j, (c.searches.get j).source ∈ SparseLabels.support (state.states.get j).labels
  queries : nq ≤ budget
  slots : (BatchDriver.jobs c r state.states).length ≤ budget

theorem prefix_facts (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x rounds : ℕ) (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (first old : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq)
    (hi : initSources c budget = .ok first)
    (hd : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (old, state)) : PrefixFacts c budget rounds old state := by
  have hv := prefix_registry_valid hn c stored input budget x rounds first old state hi hd
  have hc := prefix_cover hn c stored input budget x rounds first old state hi hd
  have he := prefix_state_eq hn c stored input budget x rounds first old state hd
  have hshape : ∀ j, SparseDriver.Shape (state.states.get j) := by
    rw [he]
    exact BatchDriver.execute_shape hn c stored input x rounds hx
  have hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (state.states.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (state.states.get j).cache i).known ⊆
        SparseLabels.support (state.states.get j).labels ∩ c.blocks.get i := by
    rw [he]
    exact raw_known_shapes hn c stored input x rounds hs hp hA hx
  refine ⟨hv, hc, hshape, hknown, ?_, initSources_queries_le c budget first hi, ?_⟩
  · intro j
    rw [he]
    have hg := (BatchDriver.execute_global_invariant hn c stored input x rounds hs hp hA hx j).1
    rw [show SparseLabels.support ((BatchDriver.execute hn c stored input x rounds).states.get j).labels =
      ((BatchDriver.execute hn c stored input x rounds).states.get j).settled ∪ {(c.searches.get j).source} from
      hg.label_support]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · exact (BatchDriver.jobs_count c rounds state.states hshape).trans
      ((registered_records c old state.states hshape hc hknown).trans (hv.1 ▸ hv.2))

theorem ordinary_registry_valid (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (before after : RecordGuard.Registry n nq) (C : Vector (Finset (Fin n)) nq)
    (hv : RecordGuard.Valid c budget before)
    (he : ordinary c budget r old stored input before = .ok (after, C)) : RecordGuard.Valid c budget after :=
  ordinary_post c budget r (RecordGuard.Valid c budget)
    (fun key old next hv he => RecordGuard.reserve_valid c budget key old next hv he)
    old stored input before after C hv he

theorem ordinary_registry_mono (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (before after : RecordGuard.Registry n nq) (C : Vector (Finset (Fin n)) nq)
    (he : ordinary c budget r old stored input before = .ok (after, C)) : before.seen ⊆ after.seen :=
  ordinary_post c budget r (fun reg => before.seen ⊆ reg.seen)
    (fun key old next hp he => hp.trans (reserve_mono c budget key old next he))
    old stored input before after C (Finset.Subset.refl _) he

def newStates (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : BatchDriver.States n nb nq)
    (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) : BatchDriver.States n nb nq :=
  Vector.ofFn fun j => BatchDriver.finishQuery c r j (old.get j) (C.get j) replies

theorem newStates_cover (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : BatchDriver.States n nb nq)
    (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (registry : RecordGuard.Registry n nq) (hc : Cover registry old)
    (hp : ∀ j, ∀ v ∈ proposed c r j (old.get j) (C.get j) replies, (j, v) ∈ registry.seen) :
    Cover registry (newStates c r old C replies) := by
  intro j v hv
  rw [newStates, Vector.get_ofFn, finishQuery_support] at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact hc j v hv
  · exact hp j v hv

theorem after_edges_space (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x rounds : ℕ) (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (first old afterBlocks afterEdges : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq)
    (blocks : Shared.Engine.Run n nb nq (BatchDriver.jobs c rounds state.states).length)
    (C : Vector (Finset (Fin n)) nq)
    (hi : initSources c budget = .ok first)
    (hd : drive hn c stored input budget x rounds 0 first ⟨BatchDriver.initial c, 0, 0, 0, 0⟩ =
      .ok (old, state))
    (hb : GuardedEngine.run hn c stored input budget rounds (Nat.log 2 x + 2)
      (BatchDriver.tasks (BatchDriver.jobs c rounds state.states)) old = .ok (afterBlocks, blocks))
    (he : ordinary c budget rounds state.states stored input afterBlocks = .ok (afterEdges, C)) :
    RecordGuard.Valid c budget afterEdges ∧
      Cover afterEdges (newStates c rounds state.states C
        (BatchDriver.answers (BatchDriver.jobs c rounds state.states) blocks.tasks)) ∧
      BatchDriver.stateCells (newStates c rounds state.states C
        (BatchDriver.answers (BatchDriver.jobs c rounds state.states) blocks.tasks)) ≤ 2 + 13 * budget ∧
      BatchDriver.ordinaryCells C ≤ 4 * budget ∧ GuardedEngine.tasksCells blocks.tasks ≤ 14 * budget := by
  have hf := prefix_facts hn c stored input budget x rounds hs hp hA hx first old state hi hd
  have hvb : RecordGuard.Valid c budget afterBlocks :=
    GuardedEngine.runAux_post hn c stored input budget rounds (Nat.log 2 x + 2) (RecordGuard.Valid c budget)
      (fun job f old next task hv he => GuardedEngine.evaluate_valid c budget rounds job f old next task hv he)
      _ old afterBlocks 0 0 0 blocks hf.valid hb
  have hve := ordinary_registry_valid c budget rounds state.states stored input afterBlocks afterEdges C hvb he
  have hmb := GuardedEngine.run_mono hn c stored input budget rounds _ _ old afterBlocks blocks hb
  have hme := ordinary_registry_mono c budget rounds state.states stored input afterBlocks afterEdges C he
  have hr := GuardedEngine.runAux_registered hn c stored input budget rounds (Nat.log 2 x + 2)
    (fun i => BatchDriver.key ((BatchDriver.jobs c rounds state.states).get i))
    _ old afterBlocks 0 0 0 blocks
    (BatchDriver.jobs_registered c rounds state.states old hf.shape hf.cover hf.known) hb
  have hr' := fun i => GuardedEngine.registered_mono c hme _ _ (hr i)
  have hR := answers_cover c afterEdges (BatchDriver.jobs c rounds state.states) blocks.tasks hr'
  have hC := ordinary_cover c budget rounds state.states stored input afterBlocks afterEdges C he
  have hP := proposed_cover c rounds state.states C _ afterEdges
    (fun j => (hmb.trans hme) (hf.cover j _ (hf.source j))) hC hR
  have hcover := newStates_cover c rounds state.states C _ afterEdges
    (cover_mono old afterEdges state.states hf.cover (hmb.trans hme)) hP
  have hblock := GuardedEngine.run_erases hn c stored input budget rounds _ _ old afterBlocks blocks hb
  have hedge := ordinary_erases c budget rounds state.states stored input afterBlocks afterEdges C he
  have hstate := prefix_state_eq hn c stored input budget x rounds first old state hd
  have hnext : newStates c rounds state.states C
      (BatchDriver.answers (BatchDriver.jobs c rounds state.states) blocks.tasks) =
      (BatchDriver.execute hn c stored input x (rounds + 1)).states := by
    calc
      _ = (BatchDriver.round hn c stored input x rounds state.states).states := by
        simp only [BatchDriver.round]
        rw [← hblock, ← hedge]
        rfl
      _ = _ := by rw [hstate]; rfl
  have hshape : ∀ j, SparseDriver.Shape
      ((newStates c rounds state.states C (BatchDriver.answers (BatchDriver.jobs c rounds state.states)
        blocks.tasks)).get j) := by
    rw [hnext]
    exact BatchDriver.execute_shape hn c stored input x (rounds + 1) hx
  have hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock
        ((newStates c rounds state.states C
          (BatchDriver.answers (BatchDriver.jobs c rounds state.states) blocks.tasks)).get j).cache i).known.map
        Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock
        ((newStates c rounds state.states C
          (BatchDriver.answers (BatchDriver.jobs c rounds state.states) blocks.tasks)).get j).cache i).known ⊆
        SparseLabels.support ((newStates c rounds state.states C
          (BatchDriver.answers (BatchDriver.jobs c rounds state.states) blocks.tasks)).get j).labels ∩ c.blocks.get i := by
    rw [hnext]
    exact raw_known_shapes hn c stored input x (rounds + 1) hs hp hA hx
  exact ⟨hve, hcover, registered_state_space c budget afterEdges _ hve hshape hcover hknown,
    candidate_cells c budget afterEdges C hve hC hf.queries,
    GuardedEngine.tasksCells_bound c budget afterEdges hve _
      (BatchDriver.job_origin_injective c rounds state.states (fun j => (hf.shape j).unique))
      blocks.tasks hf.slots hr'⟩

end StreamingReachability.Core.GuardedDriver
