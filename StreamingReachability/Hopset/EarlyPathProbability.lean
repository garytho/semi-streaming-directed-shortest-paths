module

public import StreamingReachability.Hopset.EarlyPieceCounts
public import StreamingReachability.Hopset.LayerCounts
public import StreamingReachability.Hopset.PathPosterior

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical BigOperators

noncomputable section

def pieceThreshold (C b ell : ℝ) (r : ℕ) : ℝ := 8192 * C * (100 * b) ^ r * b * ell ^ 2

theorem simultaneous_piece_bounds {A : Type*} (mu : Law A) (counts : ℕ → A → ℕ)
    (C b : ℝ) (ell horizon : ℕ) (hC : 0 < C) (hb : 0 < b) (he : 0 < ell) (hh : horizon ≤ ell)
    (hmean : ∀ i ≤ horizon, mu.expect (fun state => (counts i state : ℝ)) ≤ pieceEnvelope C b ell i) :
    1 - 1 / 32 ≤ mu.prob (fun state =>
      ∀ i ≤ horizon, (counts i state : ℝ) ≤ pieceThreshold C b ell i) := by
  have heR : (0 : ℝ) < ell := by exact_mod_cast he
  have hthreshold (i : ℕ) : 0 < pieceThreshold C b ell i := by
    unfold pieceThreshold
    positivity
  have hratio (i : ℕ) :
      pieceEnvelope C b ell i / pieceThreshold C b ell i = 1 / (64 * (ell : ℝ)) := by
    unfold pieceEnvelope pieceThreshold
    field_simp [hC.ne', hb.ne', heR.ne']
    <;> ring
  have hbad (i : ℕ) (hi : i ≤ horizon) :
      mu.prob (fun state => pieceThreshold C b ell i < (counts i state : ℝ)) ≤ 1 / (64 * (ell : ℝ)) := by
    calc
      _ ≤ mu.prob (fun state => pieceThreshold C b ell i ≤ (counts i state : ℝ)) :=
        mu.prob_mono (P := fun state => pieceThreshold C b ell i < (counts i state : ℝ))
          (Q := fun state => pieceThreshold C b ell i ≤ (counts i state : ℝ)) (fun _ h => h.le)
      _ ≤ mu.expect (fun state => (counts i state : ℝ)) / pieceThreshold C b ell i :=
        mu.markov _ (fun _ => Nat.cast_nonneg _) _ (hthreshold i)
      _ ≤ pieceEnvelope C b ell i / pieceThreshold C b ell i :=
        div_le_div_of_nonneg_right (hmean i hi) (hthreshold i).le
      _ = _ := hratio i
  have hu :
      mu.prob (fun state => ∃ i ∈ Finset.range (horizon + 1),
        pieceThreshold C b ell i < (counts i state : ℝ)) ≤ 1 / 32 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (horizon + 1),
          mu.prob (fun state => pieceThreshold C b ell i < (counts i state : ℝ)) :=
        mu.finite_union _ _
      _ ≤ ∑ _i ∈ Finset.range (horizon + 1), 1 / (64 * (ell : ℝ)) :=
        Finset.sum_le_sum (fun i hi => hbad i (by have := Finset.mem_range.mp hi; omega))
      _ = ((horizon + 1 : ℕ) : ℝ) / (64 * (ell : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ 1 / 32 := by
        apply (div_le_iff₀ (by positivity : 0 < 64 * (ell : ℝ))).mpr
        have hr : ((horizon + 1 : ℕ) : ℝ) ≤ 2 * (ell : ℝ) := by
          exact_mod_cast (show horizon + 1 ≤ 2 * ell by omega)
        linarith
  let good := fun state : A => ∀ i ≤ horizon, (counts i state : ℝ) ≤ pieceThreshold C b ell i
  have hcompl : mu.prob (fun state => ¬ good state) ≤ 1 / 32 := by
    have heq : mu.prob (fun state => ¬ good state) =
        mu.prob (fun state => ∃ i ∈ Finset.range (horizon + 1),
          pieceThreshold C b ell i < (counts i state : ℝ)) := by
      apply mu.prob_congr
      intro state
      constructor
      · intro h
        simp only [good, not_forall, not_le, exists_prop] at h
        obtain ⟨i, hi, hcount⟩ := h
        exact ⟨i, Finset.mem_range.mpr (by omega), hcount⟩
      · rintro ⟨i, hi, hcount⟩ hg
        have hir : i ≤ horizon := by have := Finset.mem_range.mp hi; omega
        exact not_le_of_gt hcount (hg i hir)
    rw [heq]
    exact hu
  have hc := mu.prob_compl good
  change 1 - 1 / 32 ≤ mu.prob good
  linarith

variable {n : ℕ}

theorem calibrated_fast_pieces (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let ps := Reference.earlyRates n hn x
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    let mu := pathStateLaw cfg ps hnum stored input root (Parameters.threshold n x)
    1 - 1 / 32 ≤ mu.prob (fun state =>
      ∀ r ≤ Parameters.threshold n x,
        (observedCount hnum r state : ℝ) ≤
          pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := Reference.earlyRates n hn x
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let horizon := Parameters.threshold n x
  let mu := pathStateLaw cfg ps hnum stored input root horizon
  have hpast : HistoryPast (some root) := by
    intro layer hl
    change layer ∈ ([] : List (Layer cfg stored input)) at hl
    simp at hl
  apply simultaneous_piece_bounds mu (fun i state => observedCount hnum i state)
    (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n) horizon
    (by have h := Parameters.pathScale_one_le n accuracy; linarith)
    (by exact_mod_cast Parameters.split_pos n) (Parameters.ell_pos n)
    ((Parameters.threshold_le_maximum n x).trans (Parameters.maximumLevel_le_logarithm n))
  intro i hi
  exact (observed_mean_le ps hnum root hpast horizon i hi).trans
    (calibrated_piece_counts hn accuracy x delta blockVolume ha hd stored input Q hweight i hi)

theorem original_fast_pieces (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x) :
    let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
    let ps := Reference.earlyRates n hn x
    let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
    let root := rootState cfg stored input Q
    let mu := (Law.family n (fun _ => Ranks.firstHit ps)).bind fun ranks =>
      (fixedPathStateLaw cfg hnum stored input root ranks (Parameters.threshold n x)).map (fun state => (ranks, state))
    1 - 1 / 32 ≤ mu.prob (fun sample =>
      ∀ r ≤ Parameters.threshold n x,
        (observedCount hnum r sample.2 : ℝ) ≤
          pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := Reference.earlyRates n hn x
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let good := fun state : Option (State cfg stored input (Parameters.threshold n x)) =>
    ∀ r ≤ Parameters.threshold n x,
      (observedCount hnum r state : ℝ) ≤
        pieceThreshold (Parameters.pathScale n accuracy) (Parameters.split n : ℝ) (Parameters.ell n : ℝ) r
  have hprefix : ∀ i < cfg.earlyLevel, i < ps.length ∧ ((ps.take i).map Rate.value).sum ≤ 1 / 2 := by
    intro i hi
    have h := Reference.calibrated_prefix_budget n hn accuracy x delta blockVolume ha hd i hi
    exact ⟨h.1, h.2.1⟩
  have heq := pathState_equiv cfg ps hnum stored input root hprefix (Parameters.threshold n x)
    (fun state => @ite ℝ (good state) (Classical.propDecidable _) 1 0)
  have hgood := calibrated_fast_pieces hn accuracy x delta blockVolume ha hd stored input Q hweight
  simp only [Law.prob_bind, Law.prob_map, Law.prob, Law.expect_bind, Law.expect_map]
  change 1 - 1 / 32 ≤
    (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
      (fixedPathStateLaw cfg hnum stored input root ranks (Parameters.threshold n x)).expect
        (fun state => @ite ℝ (good state) (Classical.propDecidable _) 1 0))
  rw [heq]
  exact hgood

end

end StreamingReachability.Hopset.Following
