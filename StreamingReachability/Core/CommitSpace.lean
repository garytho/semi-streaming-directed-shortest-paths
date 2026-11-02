module

public import StreamingReachability.Core.OrdinarySpace

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.Live

open StoredEdges

variable {n nb ns nq : ℕ} {hn : 0 < n} {c : Shared.Catalog n nb ns nq}
  {stored input : List (Edge n)} {budget x : ℕ}

structure Commit (p : Boundary hn c stored input budget x) where
  blocks : Blocks p
  complete : blocks.phases = Nat.log 2 x + 2
  afterEdges : RecordGuard.Registry n nq
  candidates : Vector (Finset (Fin n)) nq
  scanned : GuardedDriver.ordinary c budget p.rounds p.state.states stored input blocks.registry =
    .ok (afterEdges, candidates)
  count : ℕ
  registry : RecordGuard.Registry n nq
  result : BatchDriver.States n nb nq
  executed : GuardedDriver.finishQueries c budget p.rounds p.state.states candidates
    (BatchDriver.answers p.jobs blocks.result.tasks) ((List.finRange nq).take count)
    afterEdges p.state.states = .ok (registry, result)

def Commit.replies {p : Boundary hn c stored input budget x} (f : Commit p) :=
  BatchDriver.answers p.jobs f.blocks.result.tasks

def Commit.newState {p : Boundary hn c stored input budget x} (f : Commit p) : BatchDriver.States n nb nq :=
  GuardedDriver.newStates c p.rounds p.state.states f.candidates f.replies

theorem Commit.after_space {p : Boundary hn c stored input budget x} (f : Commit p)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    RecordGuard.Valid c budget f.afterEdges ∧ GuardedDriver.Cover f.afterEdges f.newState ∧
      BatchDriver.stateCells f.newState ≤ 2 + 13 * budget ∧
      BatchDriver.ordinaryCells f.candidates ≤ 4 * budget ∧
      GuardedEngine.tasksCells f.blocks.result.tasks ≤ 14 * budget := by
  have hb := f.blocks.executed
  rw [f.complete] at hb
  exact GuardedDriver.after_edges_space hn c stored input budget x p.rounds hs hp hA hx
    p.first p.registry f.blocks.registry f.afterEdges p.state f.blocks.result f.candidates
    p.initialized p.executed hb f.scanned

theorem Commit.new_eq {p : Boundary hn c stored input budget x} (f : Commit p) :
    f.newState = (BatchDriver.execute hn c stored input x (p.rounds + 1)).states := by
  have hb := GuardedEngine.run_erases hn c stored input budget p.rounds f.blocks.phases _
    p.registry f.blocks.registry f.blocks.result f.blocks.executed
  rw [f.complete] at hb
  dsimp only [Boundary.jobs] at hb
  have he := GuardedDriver.ordinary_erases c budget p.rounds p.state.states stored input
    f.blocks.registry f.afterEdges f.candidates f.scanned
  calc
    _ = (BatchDriver.round hn c stored input x p.rounds p.state.states).states := by
      simp only [BatchDriver.round]
      rw [← hb, ← he]
      rfl
    _ = _ := by
      rw [GuardedDriver.prefix_state_eq hn c stored input budget x p.rounds
        p.first p.registry p.state p.executed]
      rfl

theorem Commit.valid {p : Boundary hn c stored input budget x} (f : Commit p)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    RecordGuard.Valid c budget f.registry :=
  GuardedDriver.finishQueries_post c budget p.rounds (RecordGuard.Valid c budget)
    (fun key old next hv he => RecordGuard.reserve_valid c budget key old next hv he)
    p.state.states f.candidates f.replies _ f.afterEdges f.registry p.state.states f.result
    (f.after_space hs hp hA hx).1 f.executed

theorem Commit.mono {p : Boundary hn c stored input budget x} (f : Commit p) :
    f.afterEdges.seen ⊆ f.registry.seen :=
  GuardedDriver.finishQueries_post c budget p.rounds (fun reg => f.afterEdges.seen ⊆ reg.seen)
    (fun key old next hp he => hp.trans (GuardedDriver.reserve_mono c budget key old next he))
    p.state.states f.candidates f.replies _ f.afterEdges f.registry p.state.states f.result
    (Finset.Subset.refl _) f.executed

theorem Commit.mixed {p : Boundary hn c stored input budget x} (f : Commit p) :
    ∀ j, f.result.get j = p.state.states.get j ∨ f.result.get j = f.newState.get j := by
  intro j
  rw [GuardedDriver.finishQueries_erases c budget p.rounds p.state.states f.candidates f.replies _
    f.afterEdges f.registry p.state.states f.result f.executed,
    VectorStore.get_applyEach _ _ (List.nodup_finRange nq).take]
  split_ifs
  · right
    rw [Commit.newState, GuardedDriver.newStates, Vector.get_ofFn]
  · exact Or.inl rfl

theorem Commit.result_space {p : Boundary hn c stored input budget x} (f : Commit p)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    BatchDriver.stateCells f.result ≤ 2 + 13 * budget := by
  have hf := p.facts hs hp hA hx
  have ha := f.after_space hs hp hA hx
  have hshape : ∀ j, SparseDriver.Shape (f.newState.get j) := by
    rw [f.new_eq]
    exact BatchDriver.execute_shape hn c stored input x (p.rounds + 1) hx
  have hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (f.newState.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (f.newState.get j).cache i).known ⊆
        SparseLabels.support (f.newState.get j).labels ∩ c.blocks.get i := by
    rw [f.new_eq]
    exact GuardedDriver.raw_known_shapes hn c stored input x (p.rounds + 1) hs hp hA hx
  have hOldNew : p.registry.seen ⊆ f.registry.seen :=
    f.blocks.mono.trans
      ((GuardedDriver.ordinary_registry_mono c budget p.rounds p.state.states stored input
        f.blocks.registry f.afterEdges f.candidates f.scanned).trans f.mono)
  exact GuardedDriver.mixed_state_space c budget f.registry (f.valid hs hp hA hx)
    p.state.states f.newState f.result hf.shape hshape
    (GuardedDriver.cover_mono p.registry f.registry p.state.states hf.cover hOldNew)
    (GuardedDriver.cover_mono f.afterEdges f.registry f.newState ha.2.1 f.mono)
    hf.known hknown f.mixed

def Commit.cells {p : Boundary hn c stored input budget x} (f : Commit p) : ℕ :=
  f.blocks.cells + registryCells f.afterEdges + BatchDriver.ordinaryCells f.candidates +
    registryCells f.registry + BatchDriver.stateCells f.result + 6 * nq + 12

theorem Commit.cells_le {p : Boundary hn c stored input budget x} (f : Commit p)
    (hs : ∀ a ∈ stored, 0 < a.weight) (hp : ∀ a ∈ input, 0 < a.weight)
    (hA : 0 < c.scale) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    f.cells ≤ 28 + 93 * budget := by
  have hb := f.blocks.cells_le hs hp hA hx
  have ha := f.after_space hs hp hA hx
  have hr := RecordGuard.registry_cells c budget f.afterEdges ha.1
  have hr' := RecordGuard.registry_cells c budget f.registry (f.valid hs hp hA hx)
  have hc := f.result_space hs hp hA hx
  have hq := (p.facts hs hp hA hx).queries
  unfold Commit.cells registryCells
  omega

end StreamingReachability.Core.Live
