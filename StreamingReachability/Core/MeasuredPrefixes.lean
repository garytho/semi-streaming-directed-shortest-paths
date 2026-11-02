module

public import StreamingReachability.Core.GuardedSegments

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Core.PassMeter

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem run_abort_prefix (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N) (registry : RecordGuard.Registry n nq)
    (reason : RecordGuard.Abort) (h : (run hn c stored input budget r fuel tasks registry).result = .error reason) :
    ∃ k < fuel, ∃ before out,
      GuardedEngine.run hn c stored input budget r k tasks registry = .ok (before, out) ∧
      ∃ count next replies,
        GuardedEngine.packs hn c stored input budget r
          ((Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active out.tasks)).take count)
          before = .ok (next, replies) ∧
        (run hn c stored input budget r fuel tasks registry).passes = out.scans + replies.scans + 1 := by
  induction fuel generalizing tasks registry reason with
  | zero => cases h
  | succ fuel ih =>
      have hraw : GuardedEngine.run hn c stored input budget r (fuel + 1) tasks registry = .error reason := by
        rw [← run_erases]
        exact h
      rw [GuardedEngine.run_succ] at hraw
      cases he : GuardedEngine.phase hn c stored input budget r tasks registry with
      | error error =>
          have hphase : (phase hn c stored input budget r tasks registry).result = .error error :=
            (phase_erases _ _ _ _ _ _ _ _).trans he
          obtain ⟨count, _, next, replies, hp, hc⟩ := packs_abort_prefix hn c stored input budget r _
            registry error hphase
          refine ⟨0, by omega, registry, ⟨tasks, 0, 0, 0⟩, rfl, count, next, replies, hp, ?_⟩
          change (runAux hn c stored input budget r (fuel + 1) tasks registry 0 0 0).passes = _
          rw [runAux, hphase]
          simpa only [Nat.zero_add, phase] using hc
      | ok pair =>
          obtain ⟨next, first⟩ := pair
          simp only [he] at hraw
          cases ht : GuardedEngine.run hn c stored input budget r fuel
              (Shared.Engine.commitTasks tasks first.updates) next with
          | ok pair =>
              simp only [ht, Except.map] at hraw
              cases hraw
          | error error =>
              have hchild : (run hn c stored input budget r fuel
                  (Shared.Engine.commitTasks tasks first.updates) next).result = .error error :=
                (run_erases _ _ _ _ _ _ _ _ _).trans ht
              obtain ⟨k, hk, before, out, hb, count, last, replies, hp, hc⟩ :=
                ih _ next error hchild
              let combined : Shared.Engine.Run n nb nq N :=
                ⟨out.tasks, first.scans + out.scans,
                  Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks) + out.reservations,
                  max first.peakRows out.peakRows⟩
              have hcombined : GuardedEngine.run hn c stored input budget r (k + 1) tasks registry =
                  .ok (before, combined) := by
                rw [GuardedEngine.run_succ, he]
                simp only
                rw [hb]
                rfl
              refine ⟨k + 1, by omega, before, combined, hcombined, count, last, replies, hp, ?_⟩
              have hphase : (phase hn c stored input budget r tasks registry).result = .ok (next, first) :=
                (phase_erases _ _ _ _ _ _ _ _).trans he
              change (runAux hn c stored input budget r (fuel + 1) tasks registry 0 0 0).passes = _
              rw [runAux, hphase]
              simp only [Nat.zero_add, Nat.zero_max]
              rw [runAux_pass_offset, hc]
              simp only [combined]
              omega

theorem drive_abort_prefix (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (registry : RecordGuard.Registry n nq) (state : BatchDriver.Run n nb nq)
    (reason : RecordGuard.Abort) (h : (drive hn c stored input budget x fuel r registry state).result = .error reason) :
    ∃ k < fuel, ∃ before out,
      GuardedDriver.drive hn c stored input budget x k r registry state = .ok (before, out) ∧
      ∃ error, (round hn c stored input budget x (r + k) out.states before).result = .error error ∧
        (drive hn c stored input budget x fuel r registry state).passes =
          out.passes + (round hn c stored input budget x (r + k) out.states before).passes := by
  induction fuel generalizing r registry state reason with
  | zero => cases h
  | succ fuel ih =>
      rw [drive] at h ⊢
      cases he : (round hn c stored input budget x r state.states registry).result with
      | error error =>
          refine ⟨0, by omega, registry, state, rfl, error, ?_, ?_⟩ <;> simpa only [Nat.add_zero, he]
      | ok pair =>
          obtain ⟨next, first⟩ := pair
          simp only [he] at h ⊢
          obtain ⟨k, hk, before, out, hp, error, hr, hc⟩ := ih (r + 1) next _ reason h
          refine ⟨k + 1, by omega, before, out, ?_, error, ?_, ?_⟩
          · rw [GuardedDriver.drive]
            have he' : GuardedDriver.round hn c stored input budget x r state.states registry =
                .ok (next, first) := (round_erases _ _ _ _ _ _ _ _ _).symm.trans he
            rw [he']
            exact hp
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr
          · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc

theorem drive_success_passes (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (registry last : RecordGuard.Registry n nq)
    (state result : BatchDriver.Run n nb nq)
    (h : (drive hn c stored input budget x fuel r registry state).result = .ok (last, result)) :
    (drive hn c stored input budget x fuel r registry state).passes = result.passes := by
  induction fuel generalizing r registry state with
  | zero => cases h; rfl
  | succ fuel ih =>
      rw [drive] at h ⊢
      cases he : (round hn c stored input budget x r state.states registry).result with
      | error reason => simp [he] at h
      | ok pair =>
          obtain ⟨next, out⟩ := pair
          simp only [he] at h ⊢
          exact ih _ next _ h

variable {hn : 0 < n} {c : Shared.Catalog n nb ns nq} {stored input : List (Edge n)} {budget x : ℕ}

theorem round_successful_blocks {R : ℕ} (p : Live.Boundary hn c stored input budget x)
    (clock : p.rounds ≤ R) (reason : RecordGuard.Abort)
    (h : (round hn c stored input budget x p.rounds p.state.states p.registry).result = .error reason) :
    ∃ point : Live.PassPrefix hn c stored input budget x R,
      p.state.passes + (round hn c stored input budget x p.rounds p.state.states p.registry).passes =
        point.passes := by
  let pending := p.jobs
  cases he : (run hn c stored input budget p.rounds (Nat.log 2 x + 2)
      (BatchDriver.tasks pending) p.registry).result with
  | error error =>
      obtain ⟨k, hk, before, out, hb, count, next, replies, hp, hc⟩ :=
        run_abort_prefix hn c stored input budget p.rounds _ (BatchDriver.tasks pending) p.registry error he
      let b : Live.Blocks p := ⟨k, before, out, hb⟩
      let s : Live.Packs b := ⟨count, next, replies, hp⟩
      refine ⟨.skeleton p b s clock hk, ?_⟩
      unfold round
      dsimp only
      have he' : (run hn c stored input budget p.rounds (Nat.log 2 x + 2)
          (BatchDriver.tasks (BatchDriver.jobs c p.rounds p.state.states)) p.registry).result = .error error := he
      rw [he']
      change p.state.passes + (run hn c stored input budget p.rounds (Nat.log 2 x + 2)
        (BatchDriver.tasks pending) p.registry).passes = _
      rw [hc]
      change p.state.passes + (out.scans + replies.scans + 1) =
        p.state.passes + out.scans + replies.scans + 1
      omega
  | ok pair =>
      obtain ⟨next, blocks⟩ := pair
      have hb : GuardedEngine.run hn c stored input budget p.rounds (Nat.log 2 x + 2)
          (BatchDriver.tasks pending) p.registry = .ok (next, blocks) :=
        (run_erases _ _ _ _ _ _ _ _ _).symm.trans he
      let b : Live.Blocks p := ⟨Nat.log 2 x + 2, next, blocks, hb⟩
      have hc : (run hn c stored input budget p.rounds (Nat.log 2 x + 2)
          (BatchDriver.tasks pending) p.registry).passes = blocks.scans :=
        runAux_success_passes hn c stored input budget p.rounds _ _ p.registry next 0 0 0 blocks he
      refine ⟨.ordinary p b clock rfl, ?_⟩
      unfold round
      dsimp only
      have he' : (run hn c stored input budget p.rounds (Nat.log 2 x + 2)
          (BatchDriver.tasks (BatchDriver.jobs c p.rounds p.state.states)) p.registry).result = .ok (next, blocks) := he
      rw [he']
      cases ho : GuardedDriver.ordinary c budget p.rounds p.state.states stored input next with
      | error error =>
          simp only [ho]
          change p.state.passes + ((run hn c stored input budget p.rounds (Nat.log 2 x + 2)
            (BatchDriver.tasks pending) p.registry).passes + 1) = p.state.passes + blocks.scans + 1
          rw [hc]
          omega
      | ok pair =>
          obtain ⟨afterEdges, candidates⟩ := pair
          simp only [ho]
          change p.state.passes + ((run hn c stored input budget p.rounds (Nat.log 2 x + 2)
            (BatchDriver.tasks pending) p.registry).passes + 1) = p.state.passes + blocks.scans + 1
          rw [hc]
          omega

end StreamingReachability.Core.PassMeter
