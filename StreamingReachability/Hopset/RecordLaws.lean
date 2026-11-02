module

public import StreamingReachability.Hopset.RecordTotals

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ}

theorem raw_global_records (cfg : Config)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (rank : Vector ℕ n) :
    recordCharge stored.blocks
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg 0 stored.blocks (Vector.replicate 1 Finset.univ) (globalTargets cfg rank))
          cfg.blockSize) input).records =
      Reference.globalRecords cfg stored input (fun v => rank.get v) := by
  have hvalid : ∀ target ∈ globalTargets cfg rank,
      ValidTarget (Vector.replicate 1 Finset.univ) target := by
    intro target ht
    simp [ValidTarget, Vector.get_eq_getElem]
  exact (raw_target_records cfg 0 stored input hn hs hp hsize _ _ hvalid).trans
    (global_targets_records cfg stored input rank)

theorem expected_early_records (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (rank : Vector ℕ n) (hr : r < cfg.earlyLevel) :
    (recordCharge stored.blocks
        (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
          (catalog cfg r stored.blocks sets (earlyTargets cfg r rank sets)) cfg.blockSize) input).records : ℝ) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input (fun v => rank.get v) r (sets.get i)).expect
        (fun step => (Reference.nodeRecords cfg stored input (fun v => rank.get v) r (sets.get i) step.value : ℝ)) := by
  let owners : Fin ns → Reference.Owners n cfg :=
    fun _ _ => (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  rw [raw_target_records cfg r stored input hn hs hp hsize sets (earlyTargets cfg r rank sets)
    (earlyTargets_inside cfg r rank sets), early_targets_records cfg r stored input sets rank hr owners,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Reference.kernel, Reference.choices, Reference.pivotLaw, hr, ↓reduceIte,
    Law.expect_map, Law.expect_bind, Law.expect_pure, Reference.nodeRecords, Law.expect_const]

theorem expected_late_records (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (ranks : Fin n → ℕ) (hr : ¬ r < cfg.earlyLevel) :
    (Code.evaluate handler (lateTargetLoop cfg hn r sets (List.finRange ns))).expect
        (fun result => match result with
          | none => 0
          | some targets =>
            (recordCharge stored.blocks
              (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
                (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records : ℝ)) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input ranks r (sets.get i)).expect
        (fun step => (Reference.nodeRecords cfg stored input ranks r (sets.get i) step.value : ℝ)) := by
  let owners : Reference.Owners n cfg :=
    fun _ => (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)
  calc
    _ = ∑ i : Fin ns, (Reference.pivotLaw cfg hn r (sets.get i) ranks).expect
        (fun P => (Reference.nodeRecords cfg stored input ranks r (sets.get i) ⟨P, owners⟩ : ℝ)) := by
      apply expected_late_targets_observable handler cfg hn r sets ranks hr
      intro P hP
      rw [raw_target_records cfg r stored input hn hs hp hsize sets (pivotTargets P)
        (pivotTargets_valid sets P hP), late_targets_records cfg r stored input sets P ranks hr (fun _ => owners),
        Nat.cast_sum]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Reference.kernel, Reference.choices, Law.expect_map, Law.expect_bind,
        Reference.nodeRecords, hr, ↓reduceIte, add_zero, Law.expect_const]

namespace Reference

theorem kernel_recordMetric_sum (cfg : Config) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (ranks : Fin n → ℕ) (r : ℕ) (S : Finset (Fin n)) :
    (kernel cfg hn stored input ranks r S).expect
        (fun step => ((∑ v : Fin n, recordMetric cfg stored input v r S ranks step.value : ℕ) : ℝ)) =
      (kernel cfg hn stored input ranks r S).expect
        (fun step => (nodeRecords cfg stored input ranks r S step.value : ℝ)) := by
  apply expect_congr_on
  intro z hz
  exact congrArg (fun count : ℕ => (count : ℝ))
    (recordMetric_sum cfg stored input r S ranks z.1.value
      ((kernel_pivots_subset cfg hn stored input ranks r S) z hz))

end Reference

end

end StreamingReachability.Hopset
