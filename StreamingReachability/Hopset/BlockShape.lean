module

public import StreamingReachability.Hopset.TraceBudget

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

namespace Reference

theorem blocks_card_le (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) (hP : choice.pivots ⊆ S)
    (hg : BallsGood cfg stored input r S) :
    ∀ B ∈ blocks cfg stored input r S choice, B.card ≤ 2 * Parameters.ballSize n r := by
  unfold blocks
  split_ifs with he
  · simp
  · intro B hB
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hB
    have hpS := hP ((mem_members choice.pivots p).mp hp)
    let G := Backend.roundedRestricted stored input S cfg.inputScale
    let rho := radii cfg r G choice.owners
    have hr := radii_outer_le_search G cfg hnum r choice.owners p
    have hsub : Early.bothBall G p (rho p + distanceScale cfg r) ⊆
        Early.bothBall G p (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r)) := by
      intro v hv
      rcases (Early.mem_bothBall G p v _).mp hv with ho | hi
      · exact (Early.mem_bothBall G p v _).mpr (Or.inl (Early.within_mono ho hr))
      · exact (Early.mem_bothBall G p v _).mpr (Or.inr (Early.within_mono hi hr))
    have hb := hg p hpS
    apply (Finset.card_le_card Finset.inter_subset_right).trans
    apply (Finset.card_le_card hsub).trans
    apply (Early.bothBall_card_le G p _).trans
    dsimp only [G]
    omega

end Reference

namespace Batched

theorem level_blocks_small (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (hgood : ∀ i, Reference.BallsGood cfg stored input r (sets.get i))
    (hbudget : cfg.earlyLevel ≤ r → 2 * Parameters.ballSize n r ≤ cfg.blockSize) :
    Early.Sampling.Holds (levelLaw cfg hn stored input rank r sets)
      (fun step => ∀ B ∈ step.output.blocks, B.card ≤ cfg.blockSize) := by
  by_cases he : r < cfg.earlyLevel
  · simp only [levelLaw, he, ↓reduceIte, queryLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro xs _
    simp only [assemble, he, ↓reduceIte, List.not_mem_nil, false_implies, implies_true]
  · simp only [levelLaw, he, ↓reduceIte]
    refine Reference.holds_bind_on _ _ (fun P => ∀ i, P i ⊆ sets.get i) _
      (lateFamily_subsets cfg hn r sets) ?_
    intro P hP
    simp only [queryLaw]
    refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
    intro xs _
    let targets := pivotTargets P
    let reply := (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
      (catalog cfg r stored.blocks sets targets) cfg.blockSize) input).records
    let pivots := pivotsFromOwners cfg r sets reply targets 0 xs
    let owners := fun i => ownersFromCoordinates cfg targets i (P i)
      (selectedVertices_pivot_targets P i) xs
    have hview := raw_coordinate_node_views cfg r stored input hn hs hp hsize hnum sets targets P
      (pivotTargets_valid sets P hP) (selectedVertices_pivot_targets P) xs
    intro B hB
    simp only [assemble, he, ↓reduceIte] at hB
    change B ∈ lateBlocks cfg r sets pivots reply at hB
    obtain ⟨p, hpivot, heB⟩ := List.mem_map.mp hB
    have hlocal :
        B ∈ ((pivots.filter fun q => decide (q.setId = p.setId)).map fun q =>
          bothBall cfg r (q.eta + 1) q.shift (sets.get p.setId) reply q.forward q.backward) := by
      exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hpivot, by simp⟩, heB⟩
    rw [(hview p.setId).blocks] at hlocal
    have href : B ∈ Reference.blocks cfg stored input r (sets.get p.setId)
        ⟨P p.setId, owners p.setId⟩ := by
      simpa only [Reference.blocks, he, ↓reduceIte] using hlocal
    exact (Reference.blocks_card_le cfg stored input hnum r (sets.get p.setId) _
      (hP p.setId) (hgood p.setId) B href).trans (hbudget (by omega))

theorem calibrated_level_blocks_small (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (queue : List (Finset (Fin n)))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (hr : r ≤ Parameters.maximumLevel n)
    (hg : AllGood (Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd)
      stored input r queue) :
    Early.Sampling.Holds
      (levelLaw (Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd) hn
        stored input rank r queue.toArray.toVector)
      (fun step => ∀ B ∈ step.output.blocks, B.card ≤ x) := by
  have hx : 0 < x := by
    have hk : 0 < Parameters.k n := by have := Parameters.k_large n; omega
    have he := Parameters.ell_pos n
    have ht : 0 < 4 * 100 * Parameters.k n * Parameters.ell n := by positivity
    omega
  apply level_blocks_small _ hn stored input rank r _ hs hp hsize
    (Parameters.initialNumerator_pos n accuracy x ha) (fun i => hg _ (queue_get_mem queue i))
  intro he
  exact Parameters.late_block_size_budget n x r hx hpoly he hr

end Batched

end

end StreamingReachability.Hopset
