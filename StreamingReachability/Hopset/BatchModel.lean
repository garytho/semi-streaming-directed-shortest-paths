module

public import StreamingReachability.Hopset.LateLevelLaw
public import StreamingReachability.Hopset.RecordLaws

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical BigOperators

variable {n ns : ℕ}

structure Step (n : ℕ) where
  output : Output n
  children : List (Finset (Fin n))
  records : ℕ

def assemble (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (reply : Core.BatchAPI.SparseReply n) (pivots : List (Pivot n ns)) : Step n where
  output := {
    explicit := emittedStars cfg targets reply
    blocks := if r < cfg.earlyLevel then [] else lateBlocks cfg r sets pivots reply }
  children := if r < cfg.earlyLevel then
    earlyFringes cfg r sets pivots reply ++ earlyCore cfg r sets pivots reply
    else if r < cfg.maximumLevel then lateCore cfg r sets pivots reply else []
  records := recordCharge stored.blocks reply

/-- The one-level code before the controller's outer copy/block guards. -/
def queryCode (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) (allowance : ℕ) :
    Code n (Step n) :=
  .batch (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) allowance fun reply =>
      (pivotLoop cfg r sets reply targets 0).map (assemble cfg r stored sets targets reply)

def levelCode (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (rank : Vector ℕ n) (r : ℕ) (sets : Vector (Finset (Fin n)) ns) (allowance : ℕ) :
    Code n (Step n) :=
  if r < cfg.earlyLevel then
    queryCode cfg r stored sets (earlyTargets cfg r rank sets) allowance
  else (lateTargetLoop cfg hn r sets (List.finRange ns)).bind fun targets =>
    queryCode cfg r stored sets targets allowance

noncomputable section

def queryLaw (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) : Law (Step n) :=
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  (Law.family targets.length (fun _ =>
    Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).map fun xs =>
      assemble cfg r stored sets targets reply (pivotsFromOwners cfg r sets reply targets 0 xs)

def levelLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) : Law (Step n) :=
  if r < cfg.earlyLevel then queryLaw cfg r stored input sets (earlyTargets cfg r rank sets)
  else (Law.family ns (lateDraw cfg hn r sets)).bind fun P =>
    queryLaw cfg r stored input sets (pivotTargets P)

theorem queryCode_law (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (allowance : ℕ) (f : Option (Step n) → ℝ) :
    (Code.evaluate (Backend.rawHandler input) (queryCode cfg r stored sets targets allowance)).expect f =
      (queryLaw cfg r stored input sets targets).expect (fun step => f (some step)) := by
  simp only [queryCode, Code.evaluate, Backend.rawHandler, Law.expect_bind, Law.expect_pure]
  rw [Code.expect_map, expect_pivotLoop]
  simp only [queryLaw, Law.expect_map, Option.map_some]

theorem levelCode_law (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (allowance : ℕ) (f : Option (Step n) → ℝ) :
    (Code.evaluate (Backend.rawHandler input) (levelCode cfg hn stored rank r sets allowance)).expect f =
      (levelLaw cfg hn stored input rank r sets).expect (fun step => f (some step)) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [levelCode, levelLaw, he, ↓reduceIte]
    exact queryCode_law cfg r stored input sets _ allowance f
  · simp only [levelCode, levelLaw, he, ↓reduceIte]
    rw [Code.expect_bind, expect_lateTargetLoop, Law.expect_bind]
    simp only
    simp_rw [queryCode_law]

theorem query_records (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) :
    (queryLaw cfg r stored input sets targets).expect (fun step => (step.records : ℝ)) =
      (recordCharge stored.blocks
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records : ℝ) := by
  simp only [queryLaw, Law.expect_map, assemble, Law.expect_const]

theorem level_records (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    (levelLaw cfg hn stored input rank r sets).expect (fun step => (step.records : ℝ)) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input (fun v => rank.get v) r (sets.get i)).expect
        (fun step => (Reference.nodeRecords cfg stored input (fun v => rank.get v) r (sets.get i) step.value : ℝ)) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [levelLaw, he, ↓reduceIte, query_records]
    exact expected_early_records cfg r stored input hn hs hp hsize sets rank he
  · simp only [levelLaw, he, ↓reduceIte, Law.expect_bind]
    simp_rw [query_records]
    have h := expected_late_records (Backend.rawHandler input) cfg r stored input hn hs hp hsize
      sets (fun v => rank.get v) he
    rw [expect_lateTargetLoop] at h
    exact h

theorem level_children (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (f : Finset (Fin n) → ℝ) :
    (levelLaw cfg hn stored input rank r sets).expect (fun step => (step.children.map f).sum) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input (fun v => rank.get v) r (sets.get i)).expect
        (fun step => (step.children.map f).sum) := by
  by_cases he : r < cfg.earlyLevel
  · have h := expected_early_children (Backend.rawHandler input) cfg r stored input hn hs hp hsize hnum
      sets rank he f
    dsimp only at h
    rw [expect_pivotLoop] at h
    simpa only [levelLaw, he, ↓reduceIte, queryLaw, Law.expect_map, assemble] using h
  · have h := expected_late_children (Backend.rawHandler input) cfg r stored input hn hs hp hsize hnum
      sets (fun v => rank.get v) he f
    rw [expect_lateTargetLoop] at h
    simp_rw [expect_pivotLoop] at h
    simpa only [levelLaw, he, ↓reduceIte, Law.expect_bind, queryLaw, Law.expect_map, assemble] using h

theorem level_blocks (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (f : Finset (Fin n) → ℝ) :
    (levelLaw cfg hn stored input rank r sets).expect (fun step => (step.output.blocks.map f).sum) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input (fun v => rank.get v) r (sets.get i)).expect
        (fun step => ((Reference.blocks cfg stored input r (sets.get i) step.value).map f).sum) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [levelLaw, he, ↓reduceIte, queryLaw, Law.expect_map, assemble, Reference.blocks,
      List.map_nil, List.sum_nil, Law.expect_const, Finset.sum_const_zero]
  · have h := expected_late_blocks (Backend.rawHandler input) cfg r stored input hn hs hp hsize hnum
      sets (fun v => rank.get v) he f
    rw [expect_lateTargetLoop] at h
    simp_rw [expect_pivotLoop] at h
    simpa only [levelLaw, he, ↓reduceIte, Law.expect_bind, queryLaw, Law.expect_map, assemble] using h

end

end StreamingReachability.Hopset.Batched
