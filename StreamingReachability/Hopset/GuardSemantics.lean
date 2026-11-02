module

public import StreamingReachability.Hopset.BatchModel
public import StreamingReachability.Core.GuardedCharge

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

namespace Backend

theorem guardedHandler_threshold (request : Core.BatchAPI.Request n) (budget : ℕ)
    (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    guardedHandler input request budget =
      Law.pure (if Core.BatchAPI.replyCharge request (Core.BatchAPI.run request input).records ≤ budget
        then some (Core.BatchAPI.run request input).records else none) := by
  unfold guardedHandler
  by_cases hb : Core.BatchAPI.replyCharge request (Core.BatchAPI.run request input).records ≤ budget
  · rw [(Core.BatchAPI.runGuarded_coupled request budget input hn hs hp hA hx).mpr hb]
    simp only [hb, ↓reduceIte]
  · simp only [hb, ↓reduceIte]
    cases hr : Core.BatchAPI.runGuarded request budget input with
    | error reason => rfl
    | ok result =>
        have he := Core.GuardedDriver.run_erases request budget input result hr
        have hf := (Core.BatchAPI.runGuarded_coupled request budget input hn hs hp hA hx).mp
          (by simpa only [he] using hr)
        exact False.elim (hb hf)

theorem guarded_query (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) (allowance : ℕ) :
    let request := Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize
    guardedHandler input request allowance =
      Law.pure (if recordCharge stored.blocks (Core.BatchAPI.run request input).records ≤ allowance
        then some (Core.BatchAPI.run request input).records else none) := by
  have hx (i : Fin stored.blocks.length) :
      ((catalog cfg r stored.blocks sets targets).blocks.get i).card ≤ cfg.blockSize :=
    hsize _ (catalog_block_mem cfg r stored.blocks sets targets i)
  have h := guardedHandler_threshold
    (Core.BatchAPI.Request.ofCatalog stored.explicit (catalog cfg r stored.blocks sets targets) cfg.blockSize)
    allowance input hn hs hp cfg.inputScale_pos hx
  rw [replyCharge cfg r stored sets targets cfg.blockSize] at h
  exact h

end Backend

theorem expect_guarded_batch (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (state : State n) (hstate : state.records ≤ cfg.recordCap)
    (f : Option (Core.BatchAPI.SparseReply n × State n) → ℝ) :
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    (Code.evaluate (Backend.guardedHandler input) (batch cfg r stored sets targets state)).expect f =
      if state.records + recordCharge stored.blocks reply ≤ cfg.recordCap then
        f (some (reply, { state with
          records := state.records + recordCharge stored.blocks reply
          output := { state.output with explicit := state.output.explicit ++ emittedStars cfg targets reply } }))
      else f none := by
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  dsimp only
  simp only [batch, Code.evaluate]
  rw [Backend.guarded_query cfg r stored input hn hs hp hsize sets targets (cfg.recordCap - state.records),
    Law.expect_bind, Law.expect_pure]
  by_cases hb : state.records + recordCharge stored.blocks reply ≤ cfg.recordCap
  · have ha : recordCharge stored.blocks reply ≤ cfg.recordCap - state.records := by omega
    dsimp only [reply] at hb ha
    simp only [hb, ha, ↓reduceIte, Code.evaluate, Law.expect_pure]
  · have ha : ¬ recordCharge stored.blocks reply ≤ cfg.recordCap - state.records := by omega
    dsimp only [reply] at hb ha
    simp only [hb, ha, ↓reduceIte, Law.expect_pure]

end

end StreamingReachability.Hopset
