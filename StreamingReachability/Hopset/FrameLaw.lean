module

public import StreamingReachability.Hopset.BatchModel
public import StreamingReachability.Hopset.OwnerRows

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

structure Frame (n : ℕ) (cfg : Config) (ns : ℕ) where
  choices : Fin ns → Reference.Choice n cfg
  result : Step n

def frameFromOwners (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (owners : Fin ns → Reference.Owners n cfg) : Frame n cfg ns :=
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  { choices := fun i => ⟨P i, owners i⟩
    result := assemble cfg r stored sets targets reply
      (pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets owners)) }

def queryFrameLaw (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n)) : Law (Frame n cfg ns) :=
  (Law.family ns (fun _ => Reference.ownerLaw n cfg)).map
    (frameFromOwners cfg r stored input sets targets P)

def frameLaw (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) : Law (Frame n cfg ns) :=
  if r < cfg.earlyLevel then
    queryFrameLaw cfg r stored input sets (earlyTargets cfg r rank sets)
      (fun i => CopyHistory.pivots (sets.get i) r (fun v => rank.get v))
  else (Law.family ns (lateDraw cfg hn r sets)).bind fun P =>
    queryFrameLaw cfg r stored input sets (pivotTargets P) P

theorem queryFrameLaw_result (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (hselected : ∀ i, selectedVertices targets i = members (P i)) (f : Step n → ℝ) :
    (queryFrameLaw cfg r stored input sets targets P).expect (fun frame => f frame.result) =
      (queryLaw cfg r stored input sets targets).expect f := by
  let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
  let g : (Fin ns → Reference.Owners n cfg) → ℝ := fun owners =>
    f (assemble cfg r stored sets targets reply
      (pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets owners)))
  have hg (left right : Fin ns → Reference.Owners n cfg)
      (h : ∀ i v, v ∈ P i → left i v = right i v) : g left = g right := by
    exact congrArg (fun pivots => f (assemble cfg r stored sets targets reply pivots))
      (assignedPivots_congr_rows cfg r sets reply targets P hselected left right h)
  symm
  calc
    _ = (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect (fun xs =>
          g (fun i => ownersFromCoordinates cfg targets i (P i) (hselected i) xs)) := by
      simp only [queryLaw, Law.expect_map]
      apply congrArg (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
      funext xs
      exact congrArg (fun pivots => f (assemble cfg r stored sets targets reply pivots))
        (pivotsFromCoordinates_eq cfg r sets reply targets P hselected xs)
    _ = (Law.family ns (fun _ => Reference.ownerLaw n cfg)).expect g :=
      expected_owner_rows cfg targets P hselected g hg
    _ = _ := by
      simp only [queryFrameLaw, Law.expect_map, frameFromOwners]
      rfl

theorem frameLaw_result (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (f : Step n → ℝ) :
    (frameLaw cfg hn stored input rank r sets).expect (fun frame => f frame.result) =
      (levelLaw cfg hn stored input rank r sets).expect f := by
  by_cases he : r < cfg.earlyLevel
  · simp only [frameLaw, levelLaw, he, ↓reduceIte]
    exact queryFrameLaw_result cfg r stored input sets _ _
      (fun i => earlyTargets_selected cfg r rank sets i he) f
  · simp only [frameLaw, levelLaw, he, ↓reduceIte, Law.expect_bind]
    apply congrArg (Law.family ns (lateDraw cfg hn r sets)).expect
    funext P
    exact queryFrameLaw_result cfg r stored input sets _ P (selectedVertices_pivot_targets P) f

theorem frameLaw_pivots_subset (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) :
    Early.Sampling.Holds (frameLaw cfg hn stored input rank r sets)
      (fun frame => ∀ i, (frame.choices i).pivots ⊆ sets.get i) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [frameLaw, he, ↓reduceIte, queryFrameLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro owners h i
    exact Finset.filter_subset _ _
  · simp only [frameLaw, he, ↓reduceIte]
    refine Reference.holds_bind_on _ _ (fun P => ∀ i, P i ⊆ sets.get i) _
      (lateFamily_subsets cfg hn r sets) ?_
    intro P hP
    simp only [queryFrameLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro owners h i
    exact hP i

end

end StreamingReachability.Hopset.Batched
