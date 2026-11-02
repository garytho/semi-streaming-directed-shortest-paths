module

public import StreamingSSSP.Hopset.SignatureDensity
public import StreamingSSSP.Hopset.ConstructionLimits

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ} {A : Type*}

theorem ensures_holds (handler : Code.Handler n) (program : Code n A) (P : A → Prop)
    (h : program.Ensures P) :
    Early.Sampling.Holds (Code.evaluate handler program)
      (fun result => ∀ value, result = some value → P value) := by
  induction program with
  | pure value =>
      refine Early.Sampling.holds_pure _ _ ?_
      intro a ha
      exact Option.some.inj ha ▸ h
  | abort => exact Early.Sampling.holds_pure _ _ (by intro a ha; cases ha)
  | uniform bound positive next ih =>
      exact Early.Sampling.holds_bind _ _ _ (fun i => ih i (h i))
  | batch request allowance next ih =>
      simp only [Code.evaluate]
      refine Early.Sampling.holds_bind _ _ _ ?_
      intro result
      cases result with
      | none => exact Early.Sampling.holds_pure _ _ (by intro a ha; cases ha)
      | some reply => exact ih reply (h reply)

def Returned (handler : Code.Handler n) (program : Code n A) (value : A) : Prop :=
  ∃ weight, (some value, weight) ∈ (Code.evaluate handler program).atoms

theorem Returned.ensures (handler : Code.Handler n) (program : Code n A) (value : A)
    (h : Returned handler program value) (P : A → Prop) (hp : program.Ensures P) : P value := by
  obtain ⟨weight, hw⟩ := h
  exact ensures_holds handler program P hp (some value, weight) hw value rfl

theorem batch_reply_length (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) (state : State n) :
    (batch cfg r stored sets targets state).Ensures (fun result => result.1.length ≤ cfg.recordCap) := by
  dsimp only [batch, Code.Ensures]
  intro reply
  split
  · rename_i hcheck
    change reply.length ≤ cfg.recordCap
    have h := reply_length_le_charge stored.blocks reply
    omega
  · trivial

def outputCells (output : Output n) : ℕ :=
  4 * output.explicit.length + 4 * output.blocks.length + 2 * volume output.blocks

def stateCells (state : State n) : ℕ := outputCells state.output + 32

def storedCells (stored : Implicit.Representation n) : ℕ :=
  4 * stored.explicit.length + 4 * stored.blocks.length + 2 * volume stored.blocks

/-- Both early and late materializations are included to dominate either
branch, including the buffers that exist before a copy or block guard. -/
def geometryCells (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) : ℕ :=
  8 * ns + 4 * setVolume sets + 12 * pivots.length + 8 * reply.length +
    8 * signatureVolume cfg r sets pivots reply +
    4 * (earlyCore cfg r sets pivots reply).length + 2 * volume (earlyCore cfg r sets pivots reply) +
    4 * (earlyFringes cfg r sets pivots reply).length + 2 * volume (earlyFringes cfg r sets pivots reply) +
    4 * (lateCore cfg r sets pivots reply).length + 2 * volume (lateCore cfg r sets pivots reply) +
    4 * (lateBlocks cfg r sets pivots reply).length + 2 * volume (lateBlocks cfg r sets pivots reply) + 32

theorem geometry_cells (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (hids : (pivotIds pivots).Nodup) :
    geometryCells cfg r sets pivots reply ≤ 128 * (ns + setVolume sets + pivots.length + reply.length + 1) := by
  have hs := signatures_record_density cfg r sets pivots reply hids
  have he := early_core_count cfg r sets pivots reply
  have hev := early_core_volume cfg r sets pivots reply
  have hf := fringes_record_density cfg r sets pivots reply hids
  simp only [earlyFringes] at hf
  have hl := late_core_volume cfg r sets pivots reply
  have hb := balls_record_density cfg r sets pivots reply hids
  unfold geometryCells
  simp only [earlyFringes, List.length_map, late_core_count, late_blocks_count]
  omega

theorem guarded_geometry_cells (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (hids : (pivotIds pivots).Nodup) (hsets : ns ≤ 3 * cfg.copyCap)
    (hvolume : setVolume sets ≤ cfg.copyCap) (hpivots : pivots.length ≤ 2 * cfg.copyCap)
    (hreply : reply.length ≤ cfg.recordCap) :
    geometryCells cfg r sets pivots reply ≤ 128 * (6 * cfg.copyCap + cfg.recordCap + 1) :=
  (geometry_cells cfg r sets pivots reply hids).trans (by omega)

theorem state_cells (cfg : Config) (state : State n) (h : state.Bounded cfg)
    (headers : ℕ) (hh : state.output.blocks.length ≤ headers) :
    stateCells state ≤ 4 * cfg.recordCap + 4 * headers + 2 * cfg.blockCap + 32 := by
  have hs := h.stars_le
  have hr := h.records_le
  have hb := h.blocks_le
  unfold stateCells outputCells
  omega

def selectorCells (n : ℕ) (cfg : Config) : ℕ := 4 * n * (cfg.width + 1) + 32

theorem selector_prefix (cfg : Config) (balls : List (Finset (Fin n))) (h : balls.length ≤ cfg.width) :
    4 * volume balls + 4 * n + 32 ≤ selectorCells n cfg := by
  have hv : volume balls ≤ balls.length * n := by
    have hc := List.sum_le_sum (l := balls) (f := Finset.card) (g := fun _ => n)
      (fun B _ => by exact (Finset.card_le_univ B).trans_eq (Fintype.card_fin n))
    simpa [volume] using hc
  have hm := Nat.mul_le_mul_right n h
  unfold selectorCells
  nlinarith

def controllerCells (n : ℕ) (cfg : Config) (stored : Implicit.Representation n) (headers : ℕ) : ℕ :=
  storedCells stored + 4 * cfg.recordCap + 4 * headers + 2 * cfg.blockCap +
    128 * (6 * cfg.copyCap + cfg.recordCap + 1) + 3 * n + 16 * cfg.copyCap +
    selectorCells n cfg + 64

theorem controller_geometry (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) (state : State n) (headers : ℕ)
    (hstate : state.Bounded cfg) (hheaders : state.output.blocks.length ≤ headers)
    (hsets : ns ≤ 3 * cfg.copyCap) (hvolume : setVolume sets ≤ cfg.copyCap)
    (htargets : targets.length ≤ 2 * cfg.copyCap) (hpivots : pivots.length ≤ targets.length)
    (hids : (pivotIds pivots).Nodup) (hreply : reply.length ≤ cfg.recordCap) :
    storedCells stored + stateCells state + geometryCells cfg r sets pivots reply +
      3 * n + 8 * targets.length + selectorCells n cfg ≤ controllerCells n cfg stored headers := by
  have hs := state_cells cfg state hstate headers hheaders
  have hg := guarded_geometry_cells cfg r sets pivots reply hids hsets hvolume (hpivots.trans htargets) hreply
  unfold controllerCells
  omega

end StreamingSSSP.Hopset.Measured
