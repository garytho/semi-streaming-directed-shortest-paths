module

public import StreamingReachability.Hopset.TargetFacts
public import StreamingReachability.Hopset.ReferenceFacts
public import StreamingReachability.Probability.Sequence

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

def lateDraw (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) : Law (Finset (Fin n)) :=
  if r < cfg.maximumLevel then
    Law.subset (fun _ : Fin n => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value)
      (fun _ => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg)
      (fun _ => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one) (members (sets.get i))
  else Law.pure (sets.get i)

def targetsFromSelections : List (Fin ns) → List (Finset (Fin n)) → List (Target n ns)
  | i :: indices, P :: selected =>
      ((members P).map fun v => ⟨i, v, .pivot⟩) ++ targetsFromSelections indices selected
  | _, _ => []

theorem targetsFromSelections_map (indices : List (Fin ns)) (P : Fin ns → Finset (Fin n)) :
    targetsFromSelections indices (indices.map P) =
      indices.flatMap (fun i => (members (P i)).map fun v => ⟨i, v, .pivot⟩) := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [List.map_cons, targetsFromSelections, List.flatMap_cons, ih]

theorem expect_late_chosen (handler : Code.Handler n) (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (f : Option (Finset (Fin n)) → ℝ) :
    (Code.evaluate handler (if r < cfg.maximumLevel then
      Code.subset (PivotProfile.rate n hn cfg.k cfg.logarithm r) (members (sets.get i))
      else Code.pure (sets.get i))).expect f =
      (lateDraw cfg hn r sets i).expect (fun P => f (some P)) := by
  by_cases h : r < cfg.maximumLevel
  · simp only [h, ↓reduceIte, lateDraw]
    exact Code.expect_subset handler _ _ f
  · simp only [h, ↓reduceIte, lateDraw, Code.evaluate, Law.expect_pure]

theorem expect_lateTargetLoop_samples (handler : Code.Handler n)
    (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (indices : List (Fin ns))
    (f : Option (List (Target n ns)) → ℝ) :
    (Code.evaluate handler (lateTargetLoop cfg hn r sets indices)).expect f =
      (Law.sampleIndices (lateDraw cfg hn r sets) indices).expect
        (fun selected => f (some (targetsFromSelections indices selected))) := by
  induction indices generalizing f with
  | nil => simp [lateTargetLoop, Code.evaluate, Law.sampleIndices, targetsFromSelections]
  | cons i indices ih =>
      rw [lateTargetLoop, Code.expect_bind, expect_late_chosen, Law.sampleIndices, Law.expect_bind]
      apply congrArg (lateDraw cfg hn r sets i).expect
      funext P
      dsimp only
      rw [Code.expect_map]
      rw [ih (fun result => f (result.map fun rest =>
        ((members P).map fun v => (⟨i, v, .pivot⟩ : Target n ns)) ++ rest))]
      simp only [Law.expect_map, Option.map_some, targetsFromSelections]

theorem expect_lateTargetLoop (handler : Code.Handler n)
    (cfg : Config) (hn : 0 < n) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (f : Option (List (Target n ns)) → ℝ) :
    (Code.evaluate handler (lateTargetLoop cfg hn r sets (List.finRange ns))).expect f =
      (Law.family ns (lateDraw cfg hn r sets)).expect (fun P => f (some (pivotTargets P))) := by
  rw [expect_lateTargetLoop_samples,
    Law.expect_sampleIndices_projection ns (lateDraw cfg hn r sets) (List.finRange ns)
      (List.nodup_finRange ns)]
  simp_rw [targetsFromSelections_map]
  rfl

theorem lateDraw_pivotLaw (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (ranks : Fin n → ℕ)
    (hr : ¬ r < cfg.earlyLevel) :
    lateDraw cfg hn r sets i = Reference.pivotLaw cfg hn r (sets.get i) ranks := by
  simp only [lateDraw, Reference.pivotLaw, hr, ↓reduceIte]

theorem lateDraw_subset (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) :
    Early.Sampling.Holds (lateDraw cfg hn r sets i) (fun P => P ⊆ sets.get i) := by
  unfold lateDraw
  split_ifs
  · simpa only [members_toFinset] using
      Reference.subset_holds (PivotProfile.rate n hn cfg.k cfg.logarithm r).value
        (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg
        (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one (members (sets.get i))
  · exact Early.Sampling.holds_pure _ _ (Finset.Subset.refl _)

theorem lateFamily_subsets (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) :
    Early.Sampling.Holds (Law.family ns (lateDraw cfg hn r sets)) (fun P => ∀ i, P i ⊆ sets.get i) :=
  Reference.family_holds ns (lateDraw cfg hn r sets) (fun i P => P ⊆ sets.get i)
    (lateDraw_subset cfg hn r sets)

theorem expected_late_targets_observable (handler : Code.Handler n) (cfg : Config) (hn : 0 < n)
    (r : ℕ) (sets : Vector (Finset (Fin n)) ns) (ranks : Fin n → ℕ)
    (hr : ¬ r < cfg.earlyLevel) (value : List (Target n ns) → ℝ)
    (nodes : Fin ns → Finset (Fin n) → ℝ)
    (hvalue : ∀ P, (∀ i, P i ⊆ sets.get i) →
      value (pivotTargets P) = ∑ i : Fin ns, nodes i (P i)) :
    (Code.evaluate handler (lateTargetLoop cfg hn r sets (List.finRange ns))).expect
        (fun result => match result with | none => 0 | some targets => value targets) =
      ∑ i : Fin ns, (Reference.pivotLaw cfg hn r (sets.get i) ranks).expect (nodes i) := by
  rw [expect_lateTargetLoop]
  change (Law.family ns (lateDraw cfg hn r sets)).expect (fun P => value (pivotTargets P)) = _
  have he :
      (Law.family ns (lateDraw cfg hn r sets)).expect (fun P => value (pivotTargets P)) =
        (Law.family ns (lateDraw cfg hn r sets)).expect (fun P => ∑ i : Fin ns, nodes i (P i)) := by
    apply Reference.expect_congr_on
    intro z hz
    exact hvalue z.1 ((lateFamily_subsets cfg hn r sets) z hz)
  rw [he, Law.expect_finset_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Law.family_marginal ns (lateDraw cfg hn r sets) i (nodes i),
    lateDraw_pivotLaw cfg hn r sets i ranks hr]

end

end StreamingReachability.Hopset
