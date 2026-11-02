module

public import StreamingReachability.Hopset.LateFrontier
public import StreamingReachability.Hopset.FullTraceSplit
public import StreamingReachability.Hopset.PathReplayLaw

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

def gatedLateWork (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (T : ℝ)
    (pre tail : List (GeometricEntry n cfg)) : ℝ :=
  match replayEarly cfg hnum stored input root ranks (pre.map GeometricEntry.control) with
  | none => 0
  | some st =>
      if st.queue = afterQueue root.queue pre ∧ AllGood cfg stored input cfg.earlyLevel st.queue ∧
          (st.primeCount hnum : ℝ) ≤ T then
        lateFrontierWork cfg hn stored input cfg.earlyLevel (cfg.maximumLevel - cfg.earlyLevel)
          st.queue (splitAll cfg cfg.earlyLevel hnum st.paths) tail
      else 0

def fullLateWork (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (T : ℝ)
    (trace : List (GeometricEntry n cfg)) : ℝ :=
  gatedLateWork cfg hn hnum stored input root ranks T
    (trace.take cfg.earlyLevel) (trace.drop cfg.earlyLevel)

theorem gatedLateWork_nonneg (cfg : Config) (hn : 0 < n) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (T : ℝ)
    (pre tail : List (GeometricEntry n cfg)) :
    0 ≤ gatedLateWork cfg hn hnum stored input root ranks T pre tail := by
  unfold gatedLateWork
  split
  · exact le_rfl
  · split_ifs
    · exact lateFrontierWork_nonneg _ _ _ _ _ _ _ _ _
    · exact le_rfl

theorem gatedLateWork_mean (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    ∀ (root : State cfg stored input 0) (ranks : Fin n → ℕ)
      (pre : List (GeometricEntry n cfg)) (T : ℝ), 0 ≤ T →
      (fullTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel - cfg.earlyLevel + 1)
        cfg.earlyLevel (afterQueue root.queue pre)).expect (gatedLateWork cfg hn hnum stored input root ranks T pre) ≤
        (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  dsimp only
  intro root ranks pre T hT
  change (fullTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel - cfg.earlyLevel + 1)
    cfg.earlyLevel (afterQueue root.queue pre)).expect (gatedLateWork cfg hn hnum stored input root ranks T pre) ≤
      (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T
  have hr : cfg.earlyLevel ≤ cfg.maximumLevel := Nat.min_le_left _ _
  cases hstate : replayEarly cfg hnum stored input root ranks (pre.map GeometricEntry.control) with
  | none =>
      have hfun : gatedLateWork cfg hn hnum stored input root ranks T pre = fun _ => 0 := by
        funext tail
        simp only [gatedLateWork, hstate]
      rw [hfun, Law.expect_const]
      positivity
  | some st =>
      by_cases hready : st.queue = afterQueue root.queue pre ∧ AllGood cfg stored input cfg.earlyLevel st.queue ∧
          (st.primeCount hnum : ℝ) ≤ T
      · have hcount : ((splitAll cfg cfg.earlyLevel hnum st.paths).length : ℝ) ≤ T := by
          simpa only [State.primeCount, hready.2.1, ↓reduceIte] using hready.2.2
        have hfun : gatedLateWork cfg hn hnum stored input root ranks T pre =
            lateFrontierWork cfg hn stored input cfg.earlyLevel (cfg.maximumLevel - cfg.earlyLevel)
              st.queue (splitAll cfg cfg.earlyLevel hnum st.paths) := by
          funext tail
          simp only [gatedLateWork, hstate, ite_eq_left hready]
        rw [hfun, ← hready.1]
        have hm := lateFrontierWork_mean hn accuracy x delta blockVolume ha hd stored input (Vector.ofFn ranks)
          cfg.earlyLevel (cfg.maximumLevel - cfg.earlyLevel) le_rfl
          (by change cfg.earlyLevel + (cfg.maximumLevel - cfg.earlyLevel) = cfg.maximumLevel; omega)
          st.queue (splitAll cfg cfg.earlyLevel hnum st.paths) hs hp hsize
          (splitAll_short cfg cfg.earlyLevel hnum st.paths)
        exact hm.trans (mul_le_mul_of_nonneg_left hcount (by positivity))
      · have hfun : gatedLateWork cfg hn hnum stored input root ranks T pre = fun _ => 0 := by
          funext tail
          simp only [gatedLateWork, hstate, ite_eq_right hready]
        rw [hfun, Law.expect_const]
        positivity

theorem fullLateWork_mean (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    ∀ (root : State cfg stored input 0) (ranks : Fin n → ℕ) (T : ℝ), 0 ≤ T →
      (fullTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue).expect
        (fullLateWork cfg hn hnum stored input root ranks T) ≤
        (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  dsimp only
  intro root ranks T hT
  change (fullTraceLaw cfg hn stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue).expect
    (fullLateWork cfg hn hnum stored input root ranks T) ≤
      (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T
  have hr : cfg.earlyLevel ≤ cfg.maximumLevel := Nat.min_le_left _ _
  have hsplit : cfg.earlyLevel + (cfg.maximumLevel - cfg.earlyLevel + 1) = cfg.maximumLevel + 1 := by omega
  rw [← hsplit, fullTrace_split]
  simp only [Nat.zero_add]
  let mu := fullTraceLaw cfg hn stored input (Vector.ofFn ranks) cfg.earlyLevel 0 root.queue
  calc
    _ ≤ mu.expect (fun _ => (14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T) := by
      apply Early.Sampling.expect_mono_on
      refine Early.Sampling.holds_mono (fullTrace_length cfg hn stored input (Vector.ofFn ranks)
        cfg.earlyLevel 0 root.queue) ?_
      intro pre hlen
      have hfun : (fun tail => fullLateWork cfg hn hnum stored input root ranks T (pre ++ tail)) =
          gatedLateWork cfg hn hnum stored input root ranks T pre := by
        funext tail
        have ht : (pre ++ tail).take cfg.earlyLevel = pre := by rw [← hlen, List.take_left]
        have hd : (pre ++ tail).drop cfg.earlyLevel = tail := by rw [← hlen, List.drop_left]
        simp only [fullLateWork, ht, hd]
      rw [hfun]
      exact gatedLateWork_mean hn accuracy x delta blockVolume ha hd stored input hs hp hsize root ranks pre T hT
    _ = _ := Law.expect_const _ _

end

end StreamingReachability.Hopset.Following
