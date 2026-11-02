module

public import StreamingSSSP.Hopset.SamplingResources
public import StreamingSSSP.Hopset.TrialBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ} {A : Type*}

theorem ensures_pair (program : Code n A) (P T : A → Prop)
    (hp : program.Ensures P) (ht : program.Ensures T) : program.Ensures (fun value => P value ∧ T value) := by
  induction program with
  | pure value => exact ⟨hp, ht⟩
  | abort => trivial
  | uniform bound positive next ih => exact fun i => ih i (hp i) (ht i)
  | batch request allowance next ih => exact fun reply => ih reply (hp reply) (ht reply)

def CallsFit (cfg : Config) (stored : Implicit.Representation n)
    (Q : Core.BatchAPI.Request n → ℕ → Prop) : Prop :=
  ∀ (r m : ℕ) (sets : Vector (Finset (Fin n)) m) (targets : List (Target n m)) (allowance : ℕ),
    m ≤ 3 * cfg.copyCap → setVolume sets ≤ cfg.copyCap → targets.length ≤ 2 * cfg.copyCap →
      allowance ≤ cfg.recordCap →
      Q (Core.BatchAPI.Request.ofCatalog stored.explicit (catalog cfg r stored.blocks sets targets) cfg.blockSize) allowance

def EndBound (cfg : Config) (headers fuel : ℕ) (out : Output n) : Prop :=
  out.Bounded cfg ∧ out.blocks.length ≤ headers + 2 * fuel * cfg.copyCap

theorem EndBound.extend {cfg : Config} {headers current fuel : ℕ} {out : Output n}
    (h : EndBound cfg current fuel out) (hc : current ≤ headers + 2 * cfg.copyCap) :
    EndBound cfg headers (fuel + 1) out := by
  refine ⟨h.1, ?_⟩
  have hh := h.2.trans (Nat.add_le_add_right hc (2 * fuel * cfg.copyCap))
  nlinarith

theorem batch_blocks_unchanged (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) (state : State n) :
    (batch cfg r stored sets targets state).Ensures
      (fun result => result.2.output.blocks = state.output.blocks) := by
  dsimp only [batch, Code.Ensures]
  intro reply
  split <;> first | rfl | trivial

theorem batch_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (state : State n) (hstate : state.Bounded cfg)
    (hq : CallsFit cfg stored Q) (hs : ns ≤ 3 * cfg.copyCap)
    (hv : setVolume sets ≤ cfg.copyCap) (ht : targets.length ≤ 2 * cfg.copyCap) :
    Certificate input Q word (batch cfg r stored sets targets state) 0 1
      (fun result => result.2.Bounded cfg ∧ result.2.output.blocks = state.output.blocks) := by
  have hc : Certificate input Q word (batch cfg r stored sets targets state) 0 1 (fun _ => True) := by
    dsimp only [batch, Certificate]
    refine ⟨by decide, hq r ns sets targets _ hs hv ht (Nat.sub_le _ _), ?_⟩
    split <;> trivial
  exact hc.strengthen input Q word _ _ _ (fun _ => True) _
    (ensures_pair _ _ _ (batch_bounded cfg r stored sets targets state hstate)
      (batch_blocks_unchanged cfg r stored sets targets state))

theorem checked_blocks (cfg : Config) (old blocks : List (Finset (Fin n)))
    (hOld : ∀ B ∈ old, B.card ≤ cfg.blockSize)
    (h : (blocks.all (fun B => decide (B.card ≤ cfg.blockSize)) &&
      decide (volume (old ++ blocks) ≤ cfg.blockCap)) = true) :
    volume (old ++ blocks) ≤ cfg.blockCap ∧ ∀ B ∈ old ++ blocks, B.card ≤ cfg.blockSize := by
  have hb : blocks.all (fun B => decide (B.card ≤ cfg.blockSize)) = true ∧
      decide (volume (old ++ blocks) ≤ cfg.blockCap) = true := by
    simpa only [Bool.and_eq_true] using h
  refine ⟨of_decide_eq_true hb.2, ?_⟩
  intro B hB
  rcases List.mem_append.mp hB with hB | hB
  · exact hOld B hB
  · exact of_decide_eq_true ((List.all_eq_true.mp hb.1) B hB)

end StreamingSSSP.Hopset.Measured
