module

public import StreamingSSSP.Hopset.FrontierWitness
public import StreamingSSSP.Hopset.TreeObservedCounts
public import StreamingSSSP.Hopset.TreeFamilyBudgets
public import StreamingSSSP.Hopset.TreeLateWeights

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical BigOperators
open Batched

noncomputable section

variable {n : ℕ}

theorem calibrated_threshold_monotone (n accuracy : ℕ) :
    Monotone (pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ)) := by
  have hC : 0 ≤ Parameters.pathScale n accuracy := (Parameters.pathScale_one_le n accuracy).trans' (by norm_num)
  have hb : (1 : ℝ) ≤ Parameters.split n := by exact_mod_cast (show 1 ≤ Parameters.split n from Parameters.split_pos n)
  intro r s hrs
  have hp := pow_le_pow_right₀ (by linarith : 1 ≤ 100 * (Parameters.split n : ℝ)) hrs
  unfold pieceThreshold
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (by positivity)) (by linarith))
    (sq_nonneg _)

theorem calibrated_forest_bounds (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let T := pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ)
      (Parameters.ell n : ℝ) cfg.earlyLevel
    ∀ (root : State cfg stored input 0) (ranks : Fin n → ℕ) (trace : List (GeometricEntry n cfg))
      (run : FullExecution cfg stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue),
      run.entries = trace → PathEvent cfg hn hnum accuracy stored input root (ranks, trace) →
      (familySize hnum run root.paths : ℝ) ≤ ((Parameters.ell n : ℝ) + 1) * T ∧
      (familyLateWeight hnum hn run root.paths : ℝ) ≤ 32 * ((14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T) ∧
      ∀ (F : Graph (Fin n)) (solve : (P : TrackedPath stored input root.queue.toArray.toVector) → SearchSolution cfg F P),
        (∀ P (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg 0),
          ((solve P).debt : ℝ) ≤ ((shortTree hnum run P hshort).prune cfg.advance).markSum nodeDetour) →
        (((splitAll cfg 0 hnum root.paths).map fun P => (solve P).debt).sum : ℝ) ≤
          (Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let T := pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ)
    (Parameters.ell n : ℝ) cfg.earlyLevel
  dsimp only
  intro root ranks trace run hentries hevent
  have hEarly : cfg.earlyLevel ≤ cfg.maximumLevel := Nat.min_le_left _ _
  have hR : cfg.earlyLevel ≤ Parameters.ell n :=
    (Nat.min_le_left _ _).trans (Parameters.maximumLevel_le_logarithm n)
  have hv : FullValid cfg stored input (Vector.ofFn ranks) (cfg.maximumLevel + 1) 0 root.queue trace := by
    rw [← hentries]
    exact run.fullValid
  obtain ⟨w⟩ := PathEvent.frontier hn hnum accuracy stored input root ranks trace hEarly hevent hv
  have hfollow : followControls cfg hnum stored input (fun v => (Vector.ofFn ranks).get v)
      (run.entries.map GeometricEntry.control) (some ⟨0, root⟩) = some ⟨cfg.earlyLevel, w.state⟩ := by
    simpa only [hentries, Vector.get_ofFn] using w.follow
  have hgood : TraceGood cfg stored input run.entries := by rw [hentries]; exact hevent.1.1
  have hreplay : replayEarly cfg hnum stored input root ranks (trace.map GeometricEntry.control) = some w.state := by
    simp only [replayEarly, w.follow, unpackState, ↓reduceDIte]
  have hfast := hevent.2.1
  rw [hreplay] at hfast
  have hcounts (d : ℕ) (hd : d ≤ cfg.earlyLevel) :
      (familyCount hnum run root.paths d : ℝ) ≤
        pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) d := by
    have h := familyCount_observed hnum hEarly run (Nat.zero_add _) (Nat.zero_le _) hgood
      root.known root.paths root.layers w.state hfollow d (by simpa only [Nat.zero_add] using hd)
    have hn : familyCount hnum run root.paths d ≤ observedCount hnum d (some w.state) := by
      simpa only [Nat.zero_add] using h
    have hc : (familyCount hnum run root.paths d : ℝ) ≤ (observedCount hnum d (some w.state) : ℝ) := by exact_mod_cast hn
    exact hc.trans (hfast d hd)
  have hT : 0 ≤ T := by
    have hC := (Parameters.pathScale_one_le n accuracy).trans' (by norm_num : (0 : ℝ) ≤ 1)
    dsimp only [T, pieceThreshold]
    positivity
  have hsize : (familySize hnum run root.paths : ℝ) ≤ ((Parameters.ell n : ℝ) + 1) * T := by
    rw [familySize_counts]
    simp only [Nat.sub_zero]
    calc
      _ ≤ ∑ _d ∈ Finset.range (cfg.earlyLevel + 1), T := by
        apply Finset.sum_le_sum
        intro d hd
        have hle : d ≤ cfg.earlyLevel := by have h := Finset.mem_range.mp hd; omega
        exact (hcounts d hle).trans (calibrated_threshold_monotone n accuracy hle)
      _ = ((cfg.earlyLevel + 1 : ℕ) : ℝ) * T := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.add_le_add_right hR 1)) hT
  have hlate : (familyLateWeight hnum hn run root.paths : ℝ) ≤
      32 * ((14 : ℝ) ^ (cfg.maximumLevel - cfg.earlyLevel + 1) * T) := by
    have hw := familyLateWeight_replay hnum hn hEarly run (Nat.zero_add _) (Nat.zero_le _) hgood
      root.known root.paths root.layers w.state hfollow
    simp only [Nat.sub_zero, hentries] at hw
    exact (hw.trans w.work_eq.symm).trans_le hevent.2.2
  refine ⟨hsize, hlate, ?_⟩
  intro F solve hsolve
  have hprof := family_debt_profile hnum run root.paths F solve hsolve
  simp only [Nat.sub_zero, Nat.zero_add] at hprof
  calc
    _ ≤ ∑ d ∈ Finset.range (cfg.earlyLevel + 1),
        Reference.detourAt cfg d * (familyCount hnum run root.paths d : ℝ) := hprof
    _ ≤ ∑ d ∈ Finset.range (cfg.earlyLevel + 1), Reference.detourAt cfg d *
        pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) d := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (hcounts d (by have h := Finset.mem_range.mp hd; omega))
        (Reference.detourAt_nonneg cfg d)
    _ = ∑ d ∈ Finset.range (cfg.earlyLevel + 1),
        pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) d *
          Reference.detourAt cfg d := Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ _ := Parameters.total_detour_budget n accuracy x delta blockVolume ha hd

end

end StreamingSSSP.Hopset.Following
