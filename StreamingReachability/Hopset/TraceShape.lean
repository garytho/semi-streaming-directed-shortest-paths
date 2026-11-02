module

public import StreamingReachability.Hopset.TraceAcceptance
public import StreamingReachability.Hopset.BlockShape

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem final_level_children (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (he : cfg.earlyLevel ≤ r) (hr : cfg.maximumLevel ≤ r) :
    Early.Sampling.Holds (levelLaw cfg hn stored input rank r sets) (fun step => step.children = []) := by
  have he' : ¬ r < cfg.earlyLevel := by omega
  have hr' : ¬ r < cfg.maximumLevel := by omega
  simp only [levelLaw, he', ↓reduceIte]
  apply Early.Sampling.holds_bind
  intro P
  simp only [queryLaw]
  refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
  intro xs _
  simp only [assemble, he', hr', ↓reduceIte]

theorem ValidTrace.pending_empty_final {cfg : Config} {hn : 0 < n}
    {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}
    (fuel r : ℕ) (queue : List (Finset (Fin n))) (trace : List (Entry n))
    (h : ValidTrace cfg hn stored input rank (fuel + 1) r queue trace)
    (hcomplete : trace.length = fuel + 1) (htop : r + fuel = cfg.maximumLevel)
    (he : cfg.earlyLevel ≤ cfg.maximumLevel) : pendingQueue queue trace = [] := by
  induction fuel generalizing r queue trace with
  | zero =>
      cases h with
      | stopped => simp at hcomplete
      | @next fuel r queue step tail hg hs ht =>
          cases ht
          obtain ⟨weight, hweight⟩ := hs
          exact (final_level_children cfg hn stored input rank r queue.toArray.toVector
            (by omega) (by omega)) (step, weight) hweight
  | succ fuel ih =>
      cases h with
      | stopped => simp at hcomplete
      | @next fuel' r queue step tail hg hs ht =>
          change pendingQueue step.children tail = []
          exact ih (r + 1) step.children tail ht (by simpa using hcomplete) (by omega)

theorem calibrated_trace_blocks_small (n : ℕ) (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (fuel r : ℕ) (queue : List (Finset (Fin n))) (trace : List (Entry n))
    (h : ValidTrace (Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd)
      hn stored input rank fuel r queue trace) :
    r + fuel ≤ Parameters.maximumLevel n + 1 →
      ∀ entry ∈ trace, ∀ B ∈ entry.step.output.blocks, B.card ≤ x := by
  induction h with
  | done => simp
  | stopped => simp
  | @next fuel r queue step tail hg hstep ht ih =>
      intro hbound entry he
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨weight, hweight⟩ := hstep
        exact (calibrated_level_blocks_small n hn accuracy x delta ha hd stored input rank r queue
          hs hp hsize hpoly (by omega) hg) (step, weight) hweight
      · exact ih (by omega) entry he

theorem complete_copy_cost {cfg : Config} {hn : 0 < n} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n} (trace : List (Entry n))
    (h : ValidTrace cfg hn stored input rank (cfg.maximumLevel + 1) 0 [Finset.univ] trace)
    (hcomplete : trace.length = cfg.maximumLevel + 1) (he : cfg.earlyLevel ≤ cfg.maximumLevel)
    (state : State n) (hc : state.copies = n) :
    (replay state trace).copies = traceCost copyReward trace := by
  have hpending := h.pending_empty_final cfg.maximumLevel 0 [Finset.univ] trace hcomplete (by simp) he
  have ht := h.copy_telescope state
  rw [hpending] at ht
  simp only [volume, List.map_singleton, List.sum_singleton, Finset.card_univ, Fintype.card_fin,
    List.map_nil, List.sum_nil, add_zero, hc] at ht
  omega

end

end StreamingReachability.Hopset.Batched
