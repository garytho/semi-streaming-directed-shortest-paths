module

public import StreamingReachability.Hopset.TrialResourceBounds

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ}

theorem levels_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (cfg : Config) (hn : 0 < n)
    (stored : Implicit.Representation n) (rank : Vector ℕ n)
    (hQ : CallsFit cfg stored Q) (hw : n ≤ word) (hg : cfg.groups ≤ word) (hs : cfg.shifts ≤ word)
    (fuel r : ℕ) (queue : List (Finset (Fin n))) (state : State n) (hb : state.Bounded cfg)
    (hv : volume queue ≤ cfg.copyCap) (hcount : queue.length ≤ 3 * cfg.copyCap) :
    Certificate input Q word (levels cfg hn stored rank fuel r queue state) (5 * cfg.copyCap * fuel) fuel
      (EndBound cfg state.output.blocks.length fuel) := by
  induction fuel generalizing r queue state with
  | zero =>
      exact ⟨hb.output_bounded, by simp [EndBound]⟩
  | succ fuel ih =>
      let sets := queue.toArray.toVector
      have hvSets : setVolume sets ≤ cfg.copyCap := by
        simpa only [sets, setVolume, Array.toVector, Vector.toList_mk, List.toList_toArray] using hv
      have hnSets : queue.toArray.size ≤ 3 * cfg.copyCap := by simpa only [List.size_toArray] using hcount
      dsimp only [levels]
      split
      · let targets := earlyTargets cfg r rank sets
        have ht : targets.length ≤ 2 * setVolume sets := early_targets_count cfg r rank sets
        have htCap : targets.length ≤ 2 * cfg.copyCap := ht.trans (Nat.mul_le_mul_left 2 hvSets)
        have hbatch := batch_certificate input Q word cfg r stored sets targets state hb hQ hnSets hvSets htCap
        let afterBatch : Core.BatchAPI.SparseReply n × State n → Code n (Output n) := fun result =>
          (pivotLoop cfg r sets result.1 targets 0).bind fun pivots =>
            let children := earlyFringes cfg r sets pivots result.1 ++ earlyCore cfg r sets pivots result.1
            let copied := result.2.copies + volume children
            if copied ≤ cfg.copyCap then
              levels cfg hn stored rank fuel (r + 1) children { result.2 with copies := copied }
            else .abort
        have hnext : ∀ result, result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks →
            Certificate input Q word (afterBatch result) (5 * cfg.copyCap * (fuel + 1)) fuel
              (EndBound cfg state.output.blocks.length (fuel + 1)) := by
          intro result hresult
          let afterPivots : List (Pivot n queue.toArray.size) → Code n (Output n) := fun pivots =>
            let children := earlyFringes cfg r sets pivots result.1 ++ earlyCore cfg r sets pivots result.1
            let copied := result.2.copies + volume children
            if copied ≤ cfg.copyCap then
              levels cfg hn stored rank fuel (r + 1) children { result.2 with copies := copied }
            else .abort
          have hpivot := pivot_loop_certificate input Q word cfg r sets result.1 targets 0 hg hs
          have hafter : ∀ pivots, pivots.length ≤ targets.length →
              Certificate input Q word (afterPivots pivots) (5 * cfg.copyCap * fuel) fuel
                (EndBound cfg state.output.blocks.length (fuel + 1)) := by
            intro pivots hp
            dsimp only [afterPivots]
            split
            · rename_i hcopy
              let children := earlyFringes cfg r sets pivots result.1 ++ earlyCore cfg r sets pivots result.1
              have hnew : ({ result.2 with copies := result.2.copies + volume children } : State n).Bounded cfg :=
                ⟨hresult.1.records_le, hresult.1.stars_le, hresult.1.blocks_le, hresult.1.block_size, hcopy⟩
              have hvol : volume children ≤ cfg.copyCap := by dsimp only [children] at *; omega
              have hlen : children.length ≤ 3 * cfg.copyCap :=
                (early_children_count cfg r sets pivots result.1 (hp.trans ht)).trans (Nat.mul_le_mul_left 3 hvSets)
              have hrec := ih (r + 1) children _ hnew hvol hlen
              exact hrec.mono input Q word _ _ _ _ _
                (fun out ho => ho.extend (by
                  change result.2.output.blocks.length ≤ state.output.blocks.length + 2 * cfg.copyCap
                  rw [hresult.2]
                  omega))
            · trivial
          have h := hpivot.bind input Q word _ afterPivots (2 * targets.length) 0
            (5 * cfg.copyCap * fuel) fuel (fun pivots => pivots.length ≤ targets.length)
            (EndBound cfg state.output.blocks.length (fuel + 1)) hafter
          exact h.weaken input Q word _ _ _ _ _ _ (by nlinarith) (by omega)
        have h := hbatch.bind input Q word _ afterBatch 0 1 (5 * cfg.copyCap * (fuel + 1)) fuel
          (fun result => result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks)
          (EndBound cfg state.output.blocks.length (fuel + 1)) hnext
        simpa only [afterBatch, sets, targets, Nat.zero_add, Nat.add_comm] using h
      · have htargets := late_targets_certificate input Q word cfg hn r sets (List.finRange _) hw
        rw [index_volume_all] at htargets
        let afterTargets : List (Target n queue.toArray.size) → Code n (Output n) := fun targets =>
          (batch cfg r stored sets targets state).bind fun result =>
            (pivotLoop cfg r sets result.1 targets 0).bind fun pivots =>
              let blocks := lateBlocks cfg r sets pivots result.1
              let combined := result.2.output.blocks ++ blocks
              if blocks.all (fun B => decide (B.card ≤ cfg.blockSize)) && decide (volume combined ≤ cfg.blockCap) then
                let children := if r < cfg.maximumLevel then lateCore cfg r sets pivots result.1 else []
                let copied := result.2.copies + volume children
                if copied ≤ cfg.copyCap then
                  levels cfg hn stored rank fuel (r + 1) children
                    { result.2 with copies := copied, output := { result.2.output with blocks := combined } }
                else .abort
              else .abort
        have hnext : ∀ targets, targets.length ≤ setVolume sets →
            Certificate input Q word (afterTargets targets) (4 * cfg.copyCap + 5 * cfg.copyCap * fuel) (fuel + 1)
              (EndBound cfg state.output.blocks.length (fuel + 1)) := by
          intro targets ht
          have htCap : targets.length ≤ 2 * cfg.copyCap := (ht.trans hvSets).trans (by omega)
          have hbatch := batch_certificate input Q word cfg r stored sets targets state hb hQ hnSets hvSets htCap
          let afterBatch : Core.BatchAPI.SparseReply n × State n → Code n (Output n) := fun result =>
            (pivotLoop cfg r sets result.1 targets 0).bind fun pivots =>
              let blocks := lateBlocks cfg r sets pivots result.1
              let combined := result.2.output.blocks ++ blocks
              if blocks.all (fun B => decide (B.card ≤ cfg.blockSize)) && decide (volume combined ≤ cfg.blockCap) then
                let children := if r < cfg.maximumLevel then lateCore cfg r sets pivots result.1 else []
                let copied := result.2.copies + volume children
                if copied ≤ cfg.copyCap then
                  levels cfg hn stored rank fuel (r + 1) children
                    { result.2 with copies := copied, output := { result.2.output with blocks := combined } }
                else .abort
              else .abort
          have hresume : ∀ result, result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks →
              Certificate input Q word (afterBatch result) (4 * cfg.copyCap + 5 * cfg.copyCap * fuel) fuel
                (EndBound cfg state.output.blocks.length (fuel + 1)) := by
            intro result hresult
            let afterPivots : List (Pivot n queue.toArray.size) → Code n (Output n) := fun pivots =>
              let blocks := lateBlocks cfg r sets pivots result.1
              let combined := result.2.output.blocks ++ blocks
              if blocks.all (fun B => decide (B.card ≤ cfg.blockSize)) && decide (volume combined ≤ cfg.blockCap) then
                let children := if r < cfg.maximumLevel then lateCore cfg r sets pivots result.1 else []
                let copied := result.2.copies + volume children
                if copied ≤ cfg.copyCap then
                  levels cfg hn stored rank fuel (r + 1) children
                    { result.2 with copies := copied, output := { result.2.output with blocks := combined } }
                else .abort
              else .abort
            have hpivot := pivot_loop_certificate input Q word cfg r sets result.1 targets 0 hg hs
            have hafter : ∀ pivots, pivots.length ≤ targets.length →
                Certificate input Q word (afterPivots pivots) (5 * cfg.copyCap * fuel) fuel
                  (EndBound cfg state.output.blocks.length (fuel + 1)) := by
              intro pivots hp
              dsimp only [afterPivots]
              split
              · rename_i hblocks
                let blocks := lateBlocks cfg r sets pivots result.1
                let combined := result.2.output.blocks ++ blocks
                have hbNew := checked_blocks cfg result.2.output.blocks blocks hresult.1.block_size hblocks
                let children := if r < cfg.maximumLevel then lateCore cfg r sets pivots result.1 else []
                change Certificate input Q word
                  (if result.2.copies + volume children ≤ cfg.copyCap then
                    levels cfg hn stored rank fuel (r + 1) children
                      { result.2 with
                        copies := result.2.copies + volume children
                        output := { result.2.output with blocks := combined } }
                    else .abort) _ _ _
                split
                · rename_i hcopy
                  have hnew : ({ result.2 with
                      copies := result.2.copies + volume children
                      output := { result.2.output with blocks := combined } } : State n).Bounded cfg :=
                    ⟨hresult.1.records_le, hresult.1.stars_le, hbNew.1, hbNew.2, hcopy⟩
                  have hvol : volume children ≤ cfg.copyCap := by omega
                  have hlen : children.length ≤ 3 * cfg.copyCap := by
                    by_cases hr : r < cfg.maximumLevel
                    · simpa only [children, hr, ↓reduceIte, late_core_count] using hnSets
                    · simp [children, hr]
                  have hrec := ih (r + 1) children _ hnew hvol hlen
                  exact hrec.mono input Q word _ _ _ _ _
                    (fun out ho => ho.extend (by
                      change combined.length ≤ state.output.blocks.length + 2 * cfg.copyCap
                      dsimp only [combined]
                      rw [List.length_append, hresult.2, late_blocks_count]
                      have hc := hp.trans (ht.trans hvSets)
                      omega))
                · trivial
              · trivial
            have h := hpivot.bind input Q word _ afterPivots (2 * targets.length) 0
              (5 * cfg.copyCap * fuel) fuel (fun pivots => pivots.length ≤ targets.length)
              (EndBound cfg state.output.blocks.length (fuel + 1)) hafter
            exact h.weaken input Q word _ _ _ _ _ _ (by nlinarith) (by omega)
          have h := hbatch.bind input Q word _ afterBatch 0 1 (4 * cfg.copyCap + 5 * cfg.copyCap * fuel) fuel
            (fun result => result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks)
            (EndBound cfg state.output.blocks.length (fuel + 1)) hresume
          simpa only [afterBatch, Nat.zero_add, Nat.add_comm] using h
        have h := htargets.bind input Q word _ afterTargets (setVolume sets) 0
          (4 * cfg.copyCap + 5 * cfg.copyCap * fuel) (fuel + 1) (fun targets => targets.length ≤ setVolume sets)
          (EndBound cfg state.output.blocks.length (fuel + 1)) hnext
        exact (by
          have hh := h.weaken input Q word _ _ _ (5 * cfg.copyCap * (fuel + 1)) (fuel + 1) _
            (by nlinarith) (by omega)
          simpa only [afterTargets, sets] using hh)

end StreamingReachability.Hopset.Measured
