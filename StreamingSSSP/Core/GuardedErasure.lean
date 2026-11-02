module

public import StreamingSSSP.Core.GuardedEngineProofs
public import StreamingSSSP.Core.GuardedOrdinaryProofs

@[expose] public section

namespace StreamingSSSP.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem finishQueries_erases (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (indices : List (Fin nq)) (registry last : RecordGuard.Registry n nq)
    (acc result : BatchDriver.States n nb nq)
    (h : finishQueries c budget r old C replies indices registry acc = .ok (last, result)) :
    result = VectorStore.applyEach (fun j _ => BatchDriver.finishQuery c r j (old.get j) (C.get j) replies)
      indices acc := by
  induction indices generalizing registry acc with
  | nil => cases h; rfl
  | cons j js ih =>
      rw [finishQueries] at h
      cases hg : GuardedEngine.reserveFound c budget j (proposed c r j (old.get j) (C.get j) replies) registry with
      | error reason => simp [hg] at h
      | ok next =>
          simp only [hg] at h
          rw [ih next _ h]
          rfl

theorem round_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ) (old : BatchDriver.States n nb nq)
    (registry last : RecordGuard.Registry n nq) (result : BatchDriver.Round n nb nq)
    (h : round hn c stored input budget x r old registry = .ok (last, result)) :
    result = BatchDriver.round hn c stored input x r old := by
  unfold round at h
  cases hb : GuardedEngine.run hn c stored input budget r (Nat.log 2 x + 2)
      (BatchDriver.tasks (BatchDriver.jobs c r old)) registry with
  | error reason => simp [hb] at h
  | ok pair =>
      obtain ⟨afterBlocks, blocks⟩ := pair
      simp only [hb] at h
      have heBlocks := GuardedEngine.run_erases hn c stored input budget r (Nat.log 2 x + 2)
        _ registry afterBlocks blocks hb
      cases ho : ordinary c budget r old stored input afterBlocks with
      | error reason => simp [ho] at h
      | ok pair =>
          obtain ⟨afterEdges, candidates⟩ := pair
          simp only [ho] at h
          have heCandidates := ordinary_erases c budget r old stored input afterBlocks afterEdges candidates ho
          cases hf : finishQueries c budget r old candidates
              (BatchDriver.answers (BatchDriver.jobs c r old) blocks.tasks)
              (List.finRange nq) afterEdges old with
          | error reason => simp [hf] at h
          | ok pair =>
              obtain ⟨endRegistry, states⟩ := pair
              simp only [hf] at h
              have heStates := finishQueries_erases c budget r old candidates _ _ afterEdges endRegistry old states hf
              rw [VectorStore.applyEach_all] at heStates
              have heResult := (congrArg Prod.snd (Except.ok.inj h)).symm
              dsimp only at heResult
              rw [heResult, heStates, heCandidates, heBlocks]
              unfold BatchDriver.round
              dsimp only
              rw [BatchDriver.ordinary_peak_eq]

theorem drive_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (registry last : RecordGuard.Registry n nq)
    (state result : BatchDriver.Run n nb nq)
    (h : drive hn c stored input budget x fuel r registry state = .ok (last, result)) :
    result = BatchDriver.driveAux hn c stored input x fuel r state := by
  induction fuel generalizing r registry state with
  | zero => cases h; rfl
  | succ fuel ih =>
      rw [drive] at h
      cases hr : round hn c stored input budget x r state.states registry with
      | error reason => simp [hr] at h
      | ok pair =>
          obtain ⟨nextRegistry, step⟩ := pair
          simp only [hr] at h
          have he := round_erases hn c stored input budget x r state.states registry nextRegistry step hr
          subst step
          exact ih (r + 1) nextRegistry _ h

theorem run_erases {n : ℕ} (request : BatchAPI.Request n) (budget : ℕ) (input : List (Edge n))
    (result : BatchAPI.Result n) (h : run request budget input = .ok result) :
    result = BatchAPI.run request input := by
  unfold run at h
  by_cases hn : 0 < n
  · rw [dite_eq_left hn] at h
    cases hi : initSources request.catalog budget with
    | error reason => simp [hi] at h
    | ok registry =>
        simp only [hi] at h
        cases hd : drive hn request.catalog request.explicit input budget request.workspace
            (request.radius + 1) 0 registry ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩ with
        | error reason => simp [hd] at h
        | ok pair =>
            obtain ⟨lastRegistry, finished⟩ := pair
            simp only [hd] at h
            have he := drive_erases hn request.catalog request.explicit input budget request.workspace
              (request.radius + 1) 0 registry lastRegistry _ finished hd
            change finished = BatchDriver.executeTail hn request.catalog request.explicit input
              request.workspace (request.radius + 1) at he
            have hr := Except.ok.inj h
            rw [← hr, he, BatchAPI.run, dite_eq_left hn]
  · rw [dite_eq_right hn] at h
    cases h
    rw [BatchAPI.run, dite_eq_right hn]

end StreamingSSSP.Core.GuardedDriver
