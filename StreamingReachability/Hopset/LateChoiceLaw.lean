module

public import StreamingReachability.Hopset.LateStageGeometry
public import StreamingReachability.Hopset.FrameNodeLaw

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem mem_late_block {V : Type*} [Fintype V] (H : Graph V) (S : Finset V) (p : V) (rho D : ℝ) (v : V) :
    v ∈ Late.block H S p rho D ↔ v ∈ S ∧ v ∈ Early.bothBall H p (rho + D) := by
  unfold Late.block
  exact Finset.mem_inter

theorem reference_late_stage (cfg : Config) (hn : 0 < n) (q remaining : ℕ)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (S : Finset (Fin n)) (ranks : Fin n → ℕ) (f : (actualLateConfig n hn cfg).Stage n → ℝ) :
    (Reference.choices cfg hn q S ranks).expect (fun choice => f (lateStage cfg S choice)) =
      if remaining = 0 then ((actualLateConfig n hn cfg).allOwners S.toList).expect f
      else ((actualLateConfig n hn cfg).fresh S remaining).expect f := by
  have he' : ¬ q < cfg.earlyLevel := by omega
  simp only [Reference.choices, Reference.pivotLaw, he', ↓reduceIte, Law.expect_bind, Law.expect_map]
  by_cases hr : remaining = 0
  · have hq : q = cfg.maximumLevel := by omega
    simp only [hq, Nat.lt_irrefl, hr, ↓reduceIte, Law.expect_pure]
    exact late_stage_all cfg hn S f
  · have hq : q < cfg.maximumLevel := by omega
    have hrev : cfg.maximumLevel - remaining = q := by omega
    simp only [hq, hr, ↓reduceIte]
    have h := late_stage_fresh cfg (PivotProfile.rate n hn cfg.k cfg.logarithm q).value
      (PivotProfile.rate n hn cfg.k cfg.logarithm q).value_nonneg
      (PivotProfile.rate n hn cfg.k cfg.logarithm q).value_le_one S f
    simpa only [Late.Config.fresh, Late.Config.owner, actualLateConfig, hrev] using h

theorem frame_late_stage (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (q remaining : ℕ)
    (he : cfg.earlyLevel ≤ q) (hlevel : q + remaining = cfg.maximumLevel)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (f : (actualLateConfig n hn cfg).Stage n → ℝ) :
    (Batched.frameLaw cfg hn stored input rank q sets).expect (fun frame =>
        f (lateStage cfg (sets.get i) (frame.choices i))) =
      if remaining = 0 then ((actualLateConfig n hn cfg).allOwners (sets.get i).toList).expect f
      else ((actualLateConfig n hn cfg).fresh (sets.get i) remaining).expect f :=
  (Batched.frame_node_choice cfg hn stored input rank q sets i (fun choice => f (lateStage cfg (sets.get i) choice))).trans
    (reference_late_stage cfg hn q remaining he hlevel (sets.get i) (fun v => rank.get v) f)

theorem actual_late_blocks (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (q : ℕ) (he : cfg.earlyLevel ≤ q) (S : Finset (Fin n))
    (choice : Reference.Choice n cfg) (hP : choice.pivots ⊆ S) :
    ∀ B ∈ (actualLateConfig n hn cfg).stageBlocks stored (StoredEdges.graphOfEdges input) S
        (Reference.distanceScale cfg q) (lateStage cfg S choice),
      B ∈ Reference.blocks cfg stored input q S choice := by
  intro B hB
  dsimp only [actualLateConfig, Late.Config.stageBlocks, Late.Config.search] at hB
  rw [lateStage_pivots cfg S choice hP] at hB
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hB
  have hpP : p ∈ choice.pivots := Finset.mem_toList.mp hp
  have hrho := lateStage_radius cfg hn q
    (Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) S)) S choice hP p hpP
  dsimp only [actualLateConfig] at hrho
  rw [hrho]
  have he' : ¬ q < cfg.earlyLevel := by omega
  simp only [Reference.blocks, he', ↓reduceIte]
  apply List.mem_map.mpr
  refine ⟨p, (mem_members choice.pivots p).mpr hpP, ?_⟩
  have hsearch : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) S) =
      Backend.roundedRestricted stored input S cfg.inputScale := rfl
  have hblock := congrArg (fun H => Late.block H S p (Reference.radii cfg q H choice.owners p)
    (Reference.distanceScale cfg q)) hsearch
  rw [hblock]
  ext v
  rw [Finset.mem_inter, mem_late_block]

end

end StreamingReachability.Hopset
