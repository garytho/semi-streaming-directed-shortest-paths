module

public import StreamingSSSP.Hopset.RecordBudget

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

theorem firstHit_lt_bound (ps : List Rate) (q : ℕ) (hq : q ≤ ps.length) :
    (Ranks.firstHit ps).prob (fun rank => rank < q) ≤
      ∑ j ∈ Finset.range q, (Ranks.rate ps j).value := by
  have he : (Ranks.firstHit ps).prob (fun rank => rank < q) =
      (Ranks.firstHit ps).prob (fun rank => ∃ j ∈ Finset.range q, rank = j) := by
    apply Law.prob_congr
    intro rank
    simp
  rw [he]
  apply (Law.finite_union _ (Finset.range q) (fun j rank => rank = j)).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjq : j < q := Finset.mem_range.mp hj
  have hjp : j < ps.length := hjq.trans_le hq
  rw [Ranks.point_probability ps j hjp]
  have hsurvival : Ranks.survival ps j ≤ 1 := by
    rw [← Ranks.firstHit_tail ps j hjp.le]
    exact Law.prob_le_one _ _
  exact mul_le_of_le_one_right (Ranks.rate ps j).value_nonneg hsurvival

theorem geometric_pivot_sum (k : ℝ) (hk : 2 ≤ k) (q : ℕ) :
    (∑ j ∈ Finset.range q, k ^ (j + 1)) ≤ 2 * k ^ q := by
  have he (q : ℕ) :
      (k - 1) * (∑ j ∈ Finset.range q, k ^ (j + 1)) = k ^ (q + 1) - k := by
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Finset.sum_range_succ, mul_add, ih, pow_succ k (q + 1)]
        ring
  have h := he q
  rw [pow_succ] at h
  have hpositive := mul_nonneg (show 0 ≤ k - 2 by linarith) (pow_nonneg (by linarith : 0 ≤ k) q)
  by_contra hn
  have hstrict : 0 < (k - 1) * ((∑ j ∈ Finset.range q, k ^ (j + 1)) - 2 * k ^ q) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

theorem earlyRate_sum_bound (n : ℕ) (hn : 0 < n) (x q : ℕ)
    (hq : q ≤ (earlyRates n hn x).length) :
    (∑ j ∈ Finset.range q, (Ranks.rate (earlyRates n hn x) j).value) ≤
      200 * (Parameters.k n : ℝ) ^ q * Parameters.ell n / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (2 : ℝ) ≤ Parameters.k n := by
    exact_mod_cast (show 2 ≤ Parameters.k n by have := Parameters.k_large n; omega)
  calc
    _ ≤ ∑ j ∈ Finset.range q,
        100 * (Parameters.k n : ℝ) ^ (j + 1) * Parameters.ell n / n := by
      apply Finset.sum_le_sum
      intro j hj
      have hjq : j < q := Finset.mem_range.mp hj
      have hjcut : j < Parameters.threshold n x := by
        have hlength := PivotProfile.length_rates n hn (Parameters.k n) (Parameters.ell n)
          (Parameters.threshold n x)
        dsimp only [earlyRates] at hq
        omega
      rw [earlyRates, PivotProfile.lookup n hn (Parameters.k n) (Parameters.ell n)
        (Parameters.threshold n x) j hjcut]
      change ((min (100 * Parameters.k n ^ (j + 1) * Parameters.ell n) n : ℕ) : ℝ) / n ≤ _
      apply div_le_div_of_nonneg_right _ hnR.le
      have h := Nat.min_le_left (100 * Parameters.k n ^ (j + 1) * Parameters.ell n) n
      exact_mod_cast h
    _ = (100 * (Parameters.ell n : ℝ) / n) *
        (∑ j ∈ Finset.range q, (Parameters.k n : ℝ) ^ (j + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (100 * (Parameters.ell n : ℝ) / n) * (2 * (Parameters.k n : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_left (geometric_pivot_sum _ hk q) (by positivity)
    _ = _ := by ring

theorem firstHit_early_lt_bound (n : ℕ) (hn : 0 < n) (x q L : ℕ)
    (hq : q ≤ (earlyRates n hn x).length) (hqL : q ≤ L) :
    (Ranks.firstHit (earlyRates n hn x)).prob (fun rank => rank < q) ≤
      200 * (Parameters.k n : ℝ) ^ L * Parameters.ell n / n := by
  apply ((firstHit_lt_bound _ q hq).trans (earlyRate_sum_bound n hn x q hq)).trans
  have hk : (1 : ℝ) ≤ Parameters.k n := by
    exact_mod_cast (show 1 ≤ Parameters.k n by have := Parameters.k_large n; omega)
  gcongr

def globalCentres {n : ℕ} (cfg : Config) (ranks : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => globalWanted cfg (ranks p) = true

theorem globalCentre_mean (n : ℕ) (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => ((globalCentres (Parameters.configuration n accuracy x delta blockVolume ha hd) ranks).card : ℝ)) ≤
      200 * (Parameters.k n : ℝ) ^ Parameters.advance n accuracy * Parameters.ell n := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let ps := earlyRates n hn x
  let q := min cfg.earlyLevel cfg.advance
  have hfn :
      (fun ranks : Fin n → ℕ => ((globalCentres cfg ranks).card : ℝ)) =
        fun ranks => ∑ v : Fin n, if ranks v < q then (1 : ℝ) else 0 := by
    funext ranks
    simp only [globalCentres, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro v _
    have hp : globalWanted cfg (ranks v) = true ↔ ranks v < q := by
      simp only [globalWanted, decide_eq_true_eq, q, lt_min_iff]
    by_cases h : ranks v < q <;> simp [h, hp]
  change (Law.family n (fun _ => Ranks.firstHit ps)).expect _ ≤ _
  rw [hfn, Law.expect_finset_sum]
  have hprob : (Ranks.firstHit ps).prob (fun rank => rank < q) ≤
      200 * (Parameters.k n : ℝ) ^ cfg.advance * Parameters.ell n / n :=
    firstHit_early_lt_bound n hn x q cfg.advance
      (by dsimp [ps, earlyRates]; rw [PivotProfile.length_rates]; exact Nat.min_le_left _ _)
      (Nat.min_le_right _ _)
  calc
    _ ≤ ∑ _v : Fin n, 200 * (Parameters.k n : ℝ) ^ cfg.advance * Parameters.ell n / n := by
      apply Finset.sum_le_sum
      intro v _
      rw [Law.expect_indicator (Law.family n (fun _ => Ranks.firstHit ps)) (fun ranks => ranks v < q)]
      rw [Law.family_marginal_probability n (fun _ => Ranks.firstHit ps) v (fun rank => rank < q)]
      exact hprob
    _ = _ := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hnR]
      exact mul_comm _ _

variable {n : ℕ}

theorem searchRecords_le (stored : Implicit.Representation n) (G : Graph (Fin n))
    (p : Fin n) (radius : ℕ) :
    searchRecords stored G Finset.univ p radius ≤ 2 * (n + volume stored.blocks) := by
  calc
    _ ≤ ∑ v : Fin n, (vertexWeight stored v + vertexWeight stored v) := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> omega
    _ = 2 * (∑ v : Fin n, vertexWeight stored v) := by rw [Finset.sum_add_distrib]; omega
    _ = _ := by rw [vertexWeight_sum]

theorem globalRecords_le (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) :
    globalRecords cfg stored input ranks ≤
      2 * (globalCentres cfg ranks).card * (n + volume stored.blocks) := by
  calc
    _ ≤ ∑ _p ∈ globalCentres cfg ranks, 2 * (n + volume stored.blocks) := by
      apply Finset.sum_le_sum
      intro p _
      exact searchRecords_le stored _ p cfg.globalRadius
    _ = _ := by simp; ring

theorem expected_global_records (n : ℕ) (hn : 0 < n) (accuracy x delta blockVolume : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) :
    (Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))).expect
        (fun ranks => (globalRecords (Parameters.configuration n accuracy x delta blockVolume ha hd)
          stored input ranks : ℝ)) ≤
      400 * (Parameters.k n : ℝ) ^ Parameters.advance n accuracy * Parameters.ell n *
        (n + volume stored.blocks) := by
  let cfg := Parameters.configuration n accuracy x delta blockVolume ha hd
  let mu := Law.family n (fun _ => Ranks.firstHit (earlyRates n hn x))
  have hmono : mu.expect (fun ranks => (globalRecords cfg stored input ranks : ℝ)) ≤
      mu.expect (fun ranks =>
        (2 * (n + volume stored.blocks) : ℝ) * ((globalCentres cfg ranks).card : ℝ)) := by
    apply Law.expect_mono
    intro ranks
    have h := globalRecords_le cfg stored input ranks
    have hR : (globalRecords cfg stored input ranks : ℝ) ≤
        2 * ((globalCentres cfg ranks).card : ℝ) * (n + volume stored.blocks) := by exact_mod_cast h
    nlinarith
  apply hmono.trans
  rw [Law.expect_mul]
  have h := mul_le_mul_of_nonneg_left (globalCentre_mean n hn accuracy x delta blockVolume ha hd)
    (show (0 : ℝ) ≤ 2 * (n + volume stored.blocks) by positivity)
  exact h.trans_eq (by ring)

end

end StreamingSSSP.Hopset.Reference
