module

public import StreamingReachability.Hopset.StageGeometry
public import StreamingReachability.Hopset.BuilderValidity
public import StreamingReachability.Exact.Preprocess

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

def HopProgress (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n)
    (hops : ℕ) (stretch : ℝ) (i : ℕ) : Prop :=
  ∀ s t (d : ℕ), (StoredEdges.graphOfEdges input).dist s t = (d : Distance) →
    ∃ e : ℕ, (stored.graph (StoredEdges.graphOfEdges input)).hopDist
      (hops * Parameters.ceilDiv n (2 ^ i)) s t = (e : Distance) ∧ (e : ℝ) ≤ stretch ^ i * d

theorem hopProgress_zero (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n)
    (hops : ℕ) (hh : 0 < hops) (stretch : ℝ) (hs : stored.Sound (StoredEdges.graphOfEdges input)) :
    HopProgress input stored hops stretch 0 := by
  intro s t d hd
  have hquota : Parameters.ceilDiv n (2 ^ 0) = n := by simp [Parameters.ceilDiv]
  have hcard : Fintype.card (Fin n) ≤ hops * n + 1 := by
    have h := Nat.le_mul_of_pos_left n hh
    simp only [Fintype.card_fin]
    omega
  have he := (stored.graph (StoredEdges.graphOfEdges input)).hopDist_eq_dist_of_card_le (hops * n) s t hcard
  rw [stored.sound_distance (StoredEdges.graphOfEdges input) hs, hd] at he
  refine ⟨d, ?_, ?_⟩
  · simpa only [hquota] using he
  · simp only [pow_zero, one_mul, le_refl]

theorem calibrated_progress_step (accuracy x wmin wmax : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n)) (frozen committed : Implicit.Representation n)
    (i : ℕ) (hi : i < Parameters.ell n)
    (hmin : ∀ u v, u ≠ v → ((wmin * Parameters.queryUnit n accuracy x : ℕ) : Distance) ≤
      StoredEdges.graphOfEdges input u v)
    (hmax : Exact.WeightsBounded (StoredEdges.graphOfEdges input) (wmax * Parameters.queryUnit n accuracy x))
    (hs : frozen.Sound (StoredEdges.graphOfEdges input))
    (hprogress : HopProgress input frozen (Parameters.hopBound n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) i)
    (hquality : StageQuality frozen committed input (Parameters.hopBound n accuracy x)
      (wmin * Parameters.queryUnit n accuracy x) (2 * n * wmax * Parameters.queryUnit n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ))) :
    HopProgress input committed (Parameters.hopBound n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) (i + 1) := by
  let h := Parameters.hopBound n accuracy x
  let U := Parameters.queryUnit n accuracy x
  let stretch : ℝ := 1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)
  have hstretch : 0 ≤ stretch := by dsimp only [stretch]; positivity
  have hpower : stretch ^ i ≤ 2 := (Parameters.stretch_power_bound n accuracy ha i (by omega)).2
  have hminOld : ∀ u v, u ≠ v → ((wmin * U : ℕ) : Distance) ≤ frozen.graph (StoredEdges.graphOfEdges input) u v :=
    fun u v huv => ((StoredEdges.graphOfEdges input).dist_lower_bound _ hmin huv).trans
      (frozen.sound_graph (StoredEdges.graphOfEdges input) hs u v)
  intro s t d hd
  obtain ⟨e, he, herr⟩ := hprogress s t d hd
  have hf : (frozen.graph (StoredEdges.graphOfEdges input)).hopDist
      (h * Parameters.ceilDiv n (2 ^ i)) s t ≠ ⊤ := by
    rw [he]
    exact WithTop.natCast_ne_top _
  obtain ⟨Q, hsimple, hlength, hcost⟩ := Late.exists_backed_hopPath (h * Parameters.ceilDiv n (2 ^ i)) s t hf
  have hm : Q.micro = e := by exact_mod_cast hcost.trans he
  have hdBound : d ≤ n * wmax * U := by
    calc
      _ ≤ (wmax * U) * (n - 1) := by simpa only [Fintype.card_fin] using Exact.dist_bound _ _ hmax hd
      _ ≤ (wmax * U) * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = _ := by ring
  have hweight : Q.micro ≤ 2 * n * wmax * U := by
    have hreal : (Q.micro : ℝ) ≤ ((2 * n * wmax * U : ℕ) : ℝ) := by
      rw [hm]
      calc
        _ ≤ stretch ^ i * d := herr
        _ ≤ 2 * (d : ℝ) := mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg _)
        _ ≤ _ := by
          exact_mod_cast (show 2 * d ≤ 2 * n * wmax * U by nlinarith only [Nat.mul_le_mul_left 2 hdBound])
    exact_mod_cast hreal
  have hroute := stage_chunks frozen committed input h (wmin * U) (2 * n * wmax * U) stretch hstretch
    hminOld hquality (Parameters.ceilDiv n (2 ^ i)) Q hlength hweight
  rw [Parameters.ceilDiv_pow_succ] at hroute
  obtain ⟨next, hnext, hbudget⟩ := hroute.hopDist
  have hmul := mul_le_mul_of_nonneg_left herr hstretch
  refine ⟨next, hnext, ?_⟩
  rw [hm] at hbudget
  change (next : ℝ) ≤ stretch ^ (i + 1) * d
  rw [pow_succ]
  nlinarith only [hbudget, hmul]

theorem hopProgress_final (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n)
    (hs : stored.Sound (StoredEdges.graphOfEdges input))
    (hprogress : HopProgress input stored (Parameters.hopBound n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) (Parameters.ell n)) :
    ∀ s t (d : ℕ), (StoredEdges.graphOfEdges input).dist s t = (d : Distance) →
      ∃ e : ℕ, (stored.graph (StoredEdges.graphOfEdges input)).hopDist (Parameters.hopBound n accuracy x) s t = (e : Distance) ∧
        d ≤ e ∧ (e : ℝ) ≤ (1 + 1 / (5 * (accuracy : ℝ))) * d := by
  have hceil : Parameters.ceilDiv n (2 ^ Parameters.ell n) = 1 :=
    Parameters.ceilDiv_eq_one hn (by positivity) (Parameters.lt_two_pow_ell n).le
  intro s t d hd
  obtain ⟨e, he, herr⟩ := hprogress s t d hd
  rw [hceil, Nat.mul_one] at he
  have hl := (stored.graph (StoredEdges.graphOfEdges input)).dist_le_hopDist (Parameters.hopBound n accuracy x) s t
  rw [stored.sound_distance _ hs, hd, he] at hl
  have hu := mul_le_mul_of_nonneg_right
    (Parameters.stretch_power_bound n accuracy ha (Parameters.ell n) le_rfl).1 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  exact ⟨e, he, WithTop.coe_le_coe.mp hl, herr.trans hu⟩

end

end StreamingReachability.Hopset
