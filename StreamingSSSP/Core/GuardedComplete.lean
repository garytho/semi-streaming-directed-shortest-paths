module

public import StreamingSSSP.Core.GuardedDriverBounded
public import StreamingSSSP.Core.GuardedAllowed
public import StreamingSSSP.Core.InterfaceCosts

@[expose] public section

namespace StreamingSSSP.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem round_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hb : BatchDriver.Nrec c stored input ≤ budget)
    (registry : RecordGuard.Registry n nq) (hseen : registry.seen ⊆ RecordGuard.allowed c stored input)
    (hv : RecordGuard.Valid c budget registry) :
    ∃ next result,
      round hn c stored input budget x r (BatchDriver.execute hn c stored input x r).states registry =
        .ok (next, result) ∧ next.seen ⊆ RecordGuard.allowed c stored input ∧ RecordGuard.Valid c budget next := by
  let old := (BatchDriver.execute hn c stored input x r).states
  let P := RecordGuard.Context c r old
  let pending := BatchDriver.jobs c r old
  have hweight : RecordGuard.weight c (RecordGuard.allowed c stored input) ≤ budget := by
    rwa [RecordGuard.allowed_weight]
  have hu : ∀ j, RecordMap.Unique (old.get j).cache :=
    fun j => (BatchDriver.execute_shape hn c stored input x r hx j).unique
  have htasks : ∀ i, GuardedEngine.TaskProperty P ((BatchDriver.tasks pending).get i) := by
    intro i
    simp only [BatchDriver.tasks, Vector.get_ofFn, GuardedEngine.TaskProperty]
    exact RecordGuard.jobs_context c r old hu (List.get_mem pending i)
  have hfound : GuardedEngine.FoundRule hn c stored input r P (RecordGuard.allowed c stored input) :=
    fun job hctx => RecordGuard.found_allowed hn c stored input x r hs hp hA hx job hctx
  obtain ⟨afterBlocks, blocks, hblocks, hseenB, hvalidB⟩ :=
    GuardedEngine.run_bounded hn c stored input budget r (Nat.log 2 x + 2) P
      (fun job hctx => RecordGuard.context_double c r old job hctx)
      (RecordGuard.allowed c stored input) hweight hfound (BatchDriver.tasks pending) htasks registry hseen hv
  have heBlocks := GuardedEngine.run_erases hn c stored input budget r (Nat.log 2 x + 2)
    _ registry afterBlocks blocks hblocks
  obtain ⟨afterEdges, candidates, hedges, hseenE, hvalidE⟩ :=
    ordinary_bounded c budget r old stored input (RecordGuard.allowed c stored input) hweight
      (fun raw hm j v he => ordinaryTarget_allowed hn c stored input x r hs hp hA hx raw hm j v he)
      afterBlocks hseenB hvalidB
  have heCandidates := ordinary_erases c budget r old stored input afterBlocks afterEdges candidates hedges
  have hproposed : ∀ j v, v ∈ proposed c r j (old.get j) (candidates.get j)
      (BatchDriver.answers pending blocks.tasks) → (j, v) ∈ RecordGuard.allowed c stored input := by
    intro j v hm
    rw [heBlocks, heCandidates, Shared.Engine.runTail_eq] at hm
    exact proposed_allowed hn c stored input x r hs hp hA hx j v hm
  obtain ⟨last, states, hfinish, hseenF, hvalidF⟩ :=
    finishQueries_bounded c budget r old candidates (BatchDriver.answers pending blocks.tasks) (List.finRange nq)
      (RecordGuard.allowed c stored input) hweight hproposed afterEdges hseenE hvalidE old
  refine ⟨last, ⟨states, blocks.scans + 1, blocks.reservations, blocks.peakRows,
    BatchDriver.ordinaryCells candidates⟩, ?_, hseenF, hvalidF⟩
  dsimp only [pending, old] at hblocks hedges hfinish
  simp only [round, hblocks, hedges, hfinish]

theorem drive_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hb : BatchDriver.Nrec c stored input ≤ budget)
    (registry : RecordGuard.Registry n nq) (hseen : registry.seen ⊆ RecordGuard.allowed c stored input)
    (hv : RecordGuard.Valid c budget registry) :
    ∃ next result, drive hn c stored input budget x fuel r registry
        (BatchDriver.execute hn c stored input x r) = .ok (next, result) ∧
      next.seen ⊆ RecordGuard.allowed c stored input ∧ RecordGuard.Valid c budget next := by
  induction fuel generalizing r registry with
  | zero => exact ⟨registry, _, rfl, hseen, hv⟩
  | succ fuel ih =>
      obtain ⟨middle, step, hstep, hseen', hv'⟩ :=
        round_bounded hn c stored input budget x r hs hp hA hx hb registry hseen hv
      have he := round_erases hn c stored input budget x r _ registry middle step hstep
      obtain ⟨last, result, htail, hseen'', hv''⟩ := ih (r + 1) middle hseen' hv'
      refine ⟨last, result, ?_, hseen'', hv''⟩
      rw [drive, hstep]
      simp only [he]
      exact htail

theorem initSources_bounded (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget : ℕ) (hb : BatchDriver.Nrec c stored input ≤ budget) :
    ∃ next, initSources c budget = .ok next ∧
      next.seen ⊆ RecordGuard.allowed c stored input ∧ RecordGuard.Valid c budget next := by
  apply RecordGuard.reserveMany_bounded c budget (RecordGuard.allowed c stored input)
    (by rwa [RecordGuard.allowed_weight])
  · intro key hk
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk
    simp [RecordGuard.allowed, BatchDriver.reached, Global.target, Shared.referenceProblem]
  · exact Finset.empty_subset _
  · exact RecordGuard.empty_valid c budget

theorem run_complete {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ) (input : List (Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (hb : BatchAPI.replyCharge request (BatchAPI.run request input).records ≤ budget) :
    run request budget input = .ok (BatchAPI.run request input) := by
  have hbudget : BatchDriver.Nrec request.catalog request.explicit input ≤ budget := by
    rwa [BatchAPI.raw_reply_charge request input hn hs hp hA hx] at hb
  obtain ⟨registry, hinit, hseen, hvalid⟩ := initSources_bounded request.catalog request.explicit input budget hbudget
  obtain ⟨last, finished, hdrive, _, _⟩ := drive_bounded hn request.catalog request.explicit input budget request.workspace
    (request.radius + 1) 0 hs hp hA hx hbudget registry hseen hvalid
  simp only [BatchDriver.execute] at hdrive
  have hex : ∃ result, run request budget input = .ok result := by
    refine ⟨⟨BatchAPI.serialize request.catalog finished.states, finished.passes,
      finished.reservations, finished.peakRows, finished.ordinaryPeak⟩, ?_⟩
    simp only [run, dite_eq_left hn, hinit, hdrive]
  obtain ⟨result, hr⟩ := hex
  rw [hr, run_erases request budget input result hr]

end StreamingSSSP.Core.GuardedDriver
