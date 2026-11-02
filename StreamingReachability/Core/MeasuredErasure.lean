module

public import StreamingReachability.Core.MeasuredDriver

@[expose] public section

namespace StreamingReachability.Core.PassMeter

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem packs_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (packages : List (List (Fin N × Shared.Job n nb nq))) (registry : RecordGuard.Registry n nq) :
    (packs hn c stored input budget r packages registry).result =
      GuardedEngine.packs hn c stored input budget r packages registry := by
  induction packages generalizing registry with
  | nil => rfl
  | cons slots rest ih =>
      rw [packs, GuardedEngine.packs]
      cases he : GuardedEngine.pack hn c stored input budget r slots registry with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, first⟩ := pair
          simp only
          rw [ih]
          cases GuardedEngine.packs hn c stored input budget r rest next <;> rfl

theorem phase_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    (phase hn c stored input budget r tasks registry).result =
      GuardedEngine.phase hn c stored input budget r tasks registry :=
  packs_erases _ _ _ _ _ _ _ _

theorem runAux_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (registry : RecordGuard.Registry n nq) (scans reservations peak : ℕ) :
    (runAux hn c stored input budget r fuel tasks registry scans reservations peak).result =
      GuardedEngine.runAux hn c stored input budget r fuel tasks registry scans reservations peak := by
  induction fuel generalizing tasks registry scans reservations peak with
  | zero => rfl
  | succ fuel ih =>
      rw [runAux, GuardedEngine.runAux, ← phase_erases]
      cases he : (phase hn c stored input budget r tasks registry).result with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, out⟩ := pair
          exact ih _ next _ _ _

theorem run_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq) :
    (run hn c stored input budget r fuel tasks registry).result =
      GuardedEngine.run hn c stored input budget r fuel tasks registry :=
  runAux_erases _ _ _ _ _ _ _ _ _ _ _ _

theorem round_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ) (old : BatchDriver.States n nb nq) (registry : RecordGuard.Registry n nq) :
    (round hn c stored input budget x r old registry).result =
      GuardedDriver.round hn c stored input budget x r old registry := by
  unfold round GuardedDriver.round
  dsimp only
  rw [← run_erases]
  cases he : (run hn c stored input budget r (Nat.log 2 x + 2)
      (BatchDriver.tasks (BatchDriver.jobs c r old)) registry).result with
  | error reason => rfl
  | ok pair =>
      obtain ⟨afterBlocks, blocks⟩ := pair
      simp only
      cases ho : GuardedDriver.ordinary c budget r old stored input afterBlocks with
      | error reason => rfl
      | ok pair =>
          obtain ⟨afterEdges, candidates⟩ := pair
          simp only
          cases GuardedDriver.finishQueries c budget r old candidates
            (BatchDriver.answers (BatchDriver.jobs c r old) blocks.tasks) (List.finRange nq) afterEdges old <;> rfl

theorem drive_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (registry : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq) :
    (drive hn c stored input budget x fuel r registry state).result =
      GuardedDriver.drive hn c stored input budget x fuel r registry state := by
  induction fuel generalizing r registry state with
  | zero => rfl
  | succ fuel ih =>
      rw [drive, GuardedDriver.drive, ← round_erases]
      cases he : (round hn c stored input budget x r state.states registry).result with
      | error reason => rfl
      | ok pair =>
          obtain ⟨next, out⟩ := pair
          exact ih _ next _

theorem solve_erases {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ) (input : List (Edge n)) :
    (solve request budget input).result = GuardedDriver.run request budget input := by
  unfold solve GuardedDriver.run
  split_ifs with hn
  · cases hi : GuardedDriver.initSources request.catalog budget with
    | error reason => rfl
    | ok registry =>
        simp only
        rw [drive_erases]
        cases GuardedDriver.drive hn request.catalog request.explicit input budget request.workspace
          (request.radius + 1) 0 registry ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩ <;> rfl
  · rfl

theorem runAux_success_passes (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (registry last : RecordGuard.Registry n nq) (scans reservations peak : ℕ)
    (result : Shared.Engine.Run n nb nq N)
    (h : (runAux hn c stored input budget r fuel tasks registry scans reservations peak).result = .ok (last, result)) :
    (runAux hn c stored input budget r fuel tasks registry scans reservations peak).passes = result.scans := by
  induction fuel generalizing tasks registry scans reservations peak with
  | zero => cases h; rfl
  | succ fuel ih =>
      rw [runAux] at h ⊢
      cases he : (phase hn c stored input budget r tasks registry).result with
      | error reason => simp [he] at h
      | ok pair =>
          obtain ⟨next, out⟩ := pair
          simp only [he] at h ⊢
          exact ih _ next _ _ _ h

theorem packs_abort_prefix (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (packages : List (List (Fin N × Shared.Job n nb nq))) (registry : RecordGuard.Registry n nq)
    (reason : RecordGuard.Abort) (h : (packs hn c stored input budget r packages registry).result = .error reason) :
    ∃ k < packages.length, ∃ next out,
      GuardedEngine.packs hn c stored input budget r (packages.take k) registry = .ok (next, out) ∧
      (packs hn c stored input budget r packages registry).passes = out.scans + 1 := by
  induction packages generalizing registry reason with
  | nil => cases h
  | cons slots rest ih =>
      rw [packs] at h ⊢
      cases he : GuardedEngine.pack hn c stored input budget r slots registry with
      | error error =>
          refine ⟨0, by simp, registry, ⟨[], 0, 0, 0⟩, rfl, ?_⟩
          simp only [he]
      | ok pair =>
          obtain ⟨middle, first⟩ := pair
          simp only [he] at h ⊢
          cases ht : (packs hn c stored input budget r rest middle).result with
          | ok pair =>
              simp only [ht, Except.map] at h
              cases h
          | error error =>
              obtain ⟨k, hk, next, out, hp, hc⟩ := ih middle error ht
              refine ⟨k + 1, by simpa using Nat.add_lt_add_right hk 1, next,
                ⟨first.updates ++ out.updates, out.scans + 1, first.reads + out.reads,
                  max first.peakRows out.peakRows⟩, ?_, ?_⟩
              · simp only [List.take_succ_cons, GuardedEngine.packs, he, hp]
              · rw [hc]

end StreamingReachability.Core.PassMeter

namespace StreamingReachability.Core.BatchAPI

theorem runGuardedMeasured_erases {n : ℕ} (request : Request n) (budget : ℕ)
    (input : List (StoredEdges.Edge n)) :
    (runGuardedMeasured request budget input).result = runGuarded request budget input :=
  PassMeter.solve_erases request budget input

end StreamingReachability.Core.BatchAPI
