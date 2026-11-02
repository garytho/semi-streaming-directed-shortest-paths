module

public import StreamingReachability.Hopset.ConstructionLimits

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ} {A : Type*}

theorem Certificate.checked (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (program : Code n A)
    (draws calls : ℕ) (P : A → Prop) (h : Certificate input Q word program draws calls P) :
    Backend.Checked input program P := by
  induction program generalizing draws calls with
  | pure value => exact h
  | abort => trivial
  | uniform bound positive next ih => exact fun i => ih i _ _ (h.2.2 i)
  | batch request allowance next ih => exact ih _ _ _ h.2.2

structure OutputLimits (G : Graph (Fin n)) (accuracy x total weight : ℕ) (out : Output n) : Prop where
  sound : out.Sound G
  volume_le : volume out.blocks ≤ blockLimit n
  headers_le : out.blocks.length ≤ headerLimit n
  stars_le : out.explicit.length ≤ recordLimit n accuracy total
  block_sizes : ∀ B ∈ out.blocks, B.card ≤ x
  weights : OutputWords weight out

theorem trial_output_certificate (input : List (StoredEdges.Edge n)) (G : Graph (Fin n))
    (hn : 0 < n) (accuracy x delta total weight count scale : ℕ) (ha : 0 < accuracy) (hd : 0 < delta)
    (stored : Implicit.Representation n) (hstore : StoreBounds G accuracy x total weight count stored)
    (hc : count ≤ total) (hscale : delta ≤ scale)
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (hweight : delta * (8 * Parameters.queryUnit n accuracy x) ≤ weight) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    Certificate input
      (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
        (storeCatalogLimit n accuracy total) scale weight)
      (randomLimit n accuracy x) (fixedGuess cfg hn stored) (drawLimit n accuracy x) (callLimit n)
      (OutputLimits G accuracy x total weight) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
    (storeCatalogLimit n accuracy total) scale weight
  have hQ := store_calls_fit accuracy x delta total weight count ha hd stored hstore hc scale hscale
  have hw : n ≤ randomLimit n accuracy x := by unfold randomLimit; omega
  have hg : cfg.groups ≤ randomLimit n accuracy x := by change Parameters.groups n ≤ _; unfold randomLimit; omega
  have hs : cfg.shifts ≤ randomLimit n accuracy x := by
    change Parameters.ceilDiv (Parameters.initialNumerator n accuracy x) (Parameters.centerDenominator n accuracy) ≤ _
    unfold randomLimit
    omega
  have hcert := fixed_guess_certificate input Q (randomLimit n accuracy x) cfg hn stored hQ hw hg hs
  have hsearch : ∀ r, cfg.searchRadius r ≤ cfg.globalRadius :=
    fun r => (Parameters.searchRadius_le_queryUnit n accuracy x delta (volume stored.blocks) ha hd r).trans
      (by change Parameters.queryUnit n accuracy x ≤ 8 * Parameters.queryUnit n accuracy x; omega)
  have hwords := fixed_guess_words input cfg hn stored weight hsearch hweight
  have hsound := fixedGuess_sound G cfg stored input hn hstore.valid.positive hp hstore.valid.blocks hinput hstore.valid.sound hG
  have hpost := Backend.checked_and input (fixedGuess cfg hn stored) _ _
    (hcert.checked input Q _ _ _ _ _) (Backend.checked_and _ _ _ _ hsound hwords)
  have hlimits : Backend.Checked input (fixedGuess cfg hn stored) (OutputLimits G accuracy x total weight) :=
    Backend.checked_mono input _ _ _ hpost (fun out ho => by
      have hv : volume stored.blocks ≤ total * blockLimit n :=
        hstore.volume_le.trans (Nat.mul_le_mul_right _ hc)
      have hstars : out.explicit.length ≤ recordLimit n accuracy total := by
        apply ho.1.1.stars_le.trans
        change recordFactor n accuracy * (n + volume stored.blocks) ≤ recordFactor n accuracy * (n + total * blockLimit n)
        exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hv n)
      have hheaders : out.blocks.length ≤ headerLimit n := by
        change out.blocks.length ≤ 2 * (cfg.maximumLevel + 1) * cfg.copyCap
        simpa only [zero_add] using ho.1.2
      exact ⟨ho.2.1, ho.1.1.blocks_le, hheaders, hstars, ho.1.1.block_size, ho.2.2⟩)
  have hfinal := hcert.checked_strengthen input Q (randomLimit n accuracy x) _ _ _ _
    (OutputLimits G accuracy x total weight) hlimits
  exact hfinal

end StreamingReachability.Hopset.Measured
