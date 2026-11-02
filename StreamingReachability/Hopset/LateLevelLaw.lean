module

public import StreamingReachability.Hopset.LevelLaw
public import StreamingReachability.Hopset.LateSampling

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n ns : ℕ}

theorem expected_late_children_given_pivots (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (P : Fin ns → Finset (Fin n))
    (hP : ∀ i, P i ⊆ sets.get i) (hr : ¬ r < cfg.earlyLevel)
    (f : Finset (Fin n) → ℝ) :
    let targets := pivotTargets P
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    (Code.evaluate handler (pivotLoop cfg r sets reply targets 0)).expect
        (fun result => match result with
          | none => 0
          | some pivots =>
            ((if r < cfg.maximumLevel then lateCore cfg r sets pivots reply else []).map f).sum) =
      ∑ i : Fin ns, (Reference.ownerLaw n cfg).expect (fun owners =>
        ((Reference.children cfg stored input r (sets.get i) ⟨P i, owners⟩).map f).sum) := by
  let targets := pivotTargets P
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  have hselected (i : Fin ns) : selectedVertices targets i = members (P i) :=
    selectedVertices_pivot_targets P i
  dsimp only
  refine expected_pivot_observable handler cfg r sets reply targets P hselected
    (fun pivots => ((if r < cfg.maximumLevel then lateCore cfg r sets pivots reply else []).map f).sum)
    (fun i owners => ((Reference.children cfg stored input r (sets.get i) ⟨P i, owners⟩).map f).sum)
    ?_ ?_
  · intro xs
    have hview := raw_coordinate_node_views cfg r stored input hn hs hp hsize hnum sets targets P
      (pivotTargets_valid sets P hP) hselected xs
    by_cases hl : r < cfg.maximumLevel
    · simp only [hl, ↓reduceIte]
      rw [lateCore_cost cfg r sets _ reply P _ _ hview f]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Reference.children, hr, hl, ↓reduceIte, List.map_singleton, List.sum_singleton]
    · simp only [hl, ↓reduceIte, Reference.children, hr, List.map_nil, List.sum_nil,
        Finset.sum_const_zero]
  · intro i left right he
    rw [Reference.children_owners_congr cfg stored input r (sets.get i) (P i) left right he]

theorem expected_late_blocks_given_pivots (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (P : Fin ns → Finset (Fin n))
    (hP : ∀ i, P i ⊆ sets.get i) (hr : ¬ r < cfg.earlyLevel)
    (f : Finset (Fin n) → ℝ) :
    let targets := pivotTargets P
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    (Code.evaluate handler (pivotLoop cfg r sets reply targets 0)).expect
        (fun result => match result with
          | none => 0
          | some pivots => ((lateBlocks cfg r sets pivots reply).map f).sum) =
      ∑ i : Fin ns, (Reference.ownerLaw n cfg).expect (fun owners =>
        ((Reference.blocks cfg stored input r (sets.get i) ⟨P i, owners⟩).map f).sum) := by
  let targets := pivotTargets P
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  have hselected (i : Fin ns) : selectedVertices targets i = members (P i) :=
    selectedVertices_pivot_targets P i
  dsimp only
  refine expected_pivot_observable handler cfg r sets reply targets P hselected
    (fun pivots => ((lateBlocks cfg r sets pivots reply).map f).sum)
    (fun i owners => ((Reference.blocks cfg stored input r (sets.get i) ⟨P i, owners⟩).map f).sum)
    ?_ ?_
  · intro xs
    have hview := raw_coordinate_node_views cfg r stored input hn hs hp hsize hnum sets targets P
      (pivotTargets_valid sets P hP) hselected xs
    rw [lateBlocks_cost cfg r sets _ reply P _ _ hview f]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Reference.blocks, hr, ↓reduceIte]
  · intro i left right he
    rw [Reference.blocks_owners_congr cfg stored input r (sets.get i) (P i) left right he]

theorem expected_late_children (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (ranks : Fin n → ℕ) (hr : ¬ r < cfg.earlyLevel)
    (f : Finset (Fin n) → ℝ) :
    (Code.evaluate handler (lateTargetLoop cfg hn r sets (List.finRange ns))).expect
        (fun result => match result with
          | none => 0
          | some targets =>
            let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
              (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
            (Code.evaluate handler (pivotLoop cfg r sets reply targets 0)).expect
              (fun result => match result with
                | none => 0
                | some pivots =>
                  ((if r < cfg.maximumLevel then lateCore cfg r sets pivots reply else []).map f).sum)) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input ranks r (sets.get i)).expect
        (fun step => (step.children.map f).sum) := by
  calc
    _ = ∑ i : Fin ns, (Reference.pivotLaw cfg hn r (sets.get i) ranks).expect (fun P =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          ((Reference.children cfg stored input r (sets.get i) ⟨P, owners⟩).map f).sum)) := by
      apply expected_late_targets_observable handler cfg hn r sets ranks hr
      intro P hP
      exact expected_late_children_given_pivots handler cfg r stored input hn hs hp hsize hnum
        sets P hP hr f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Reference.kernel, Reference.choices, Law.expect_map, Law.expect_bind]

theorem expected_late_blocks (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (sets : Vector (Finset (Fin n)) ns) (ranks : Fin n → ℕ) (hr : ¬ r < cfg.earlyLevel)
    (f : Finset (Fin n) → ℝ) :
    (Code.evaluate handler (lateTargetLoop cfg hn r sets (List.finRange ns))).expect
        (fun result => match result with
          | none => 0
          | some targets =>
            let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
              (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
            (Code.evaluate handler (pivotLoop cfg r sets reply targets 0)).expect
              (fun result => match result with
                | none => 0
                | some pivots => ((lateBlocks cfg r sets pivots reply).map f).sum)) =
      ∑ i : Fin ns, (Reference.kernel cfg hn stored input ranks r (sets.get i)).expect
        (fun step => ((Reference.blocks cfg stored input r (sets.get i) step.value).map f).sum) := by
  calc
    _ = ∑ i : Fin ns, (Reference.pivotLaw cfg hn r (sets.get i) ranks).expect (fun P =>
        (Reference.ownerLaw n cfg).expect (fun owners =>
          ((Reference.blocks cfg stored input r (sets.get i) ⟨P, owners⟩).map f).sum)) := by
      apply expected_late_targets_observable handler cfg hn r sets ranks hr
      intro P hP
      exact expected_late_blocks_given_pivots handler cfg r stored input hn hs hp hsize hnum
        sets P hP hr f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Reference.kernel, Reference.choices, Law.expect_map, Law.expect_bind]

end

end StreamingReachability.Hopset
