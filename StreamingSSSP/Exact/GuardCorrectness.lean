module

public import StreamingSSSP.Exact.TraceBounds

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

theorem approx_answer_bound (G : Graph V) (s : V) (denominator bound : ℕ)
    (answer : V → ℕ) (hden : 0 < denominator)
    (hanswer : IntegerApprox G s denominator answer)
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ bound) :
    ∀ v, answer v ≤ 2 * bound := by
  intro v
  obtain ⟨d, hd, hdb⟩ := hreach v
  have ha := (hanswer v d hd).2
  have hcoef : denominator + 1 ≤ 2 * denominator := by omega
  have hp := Nat.mul_le_mul hcoef hdb
  nlinarith

theorem levelTrace_reachable (call : Oracle (Option V)) (G : Graph V)
    (M rounds slope : ℕ) (labels : V → ℕ) :
    ∀ q ∈ levelTrace call G M rounds slope labels,
      0 < q.denominator → ∀ v, q.graph.dist q.source v ≠ ⊤ := by
  induction rounds generalizing slope labels with
  | zero => simp [levelTrace]
  | succ rounds ih =>
      intro q hq hden v
      simp only [levelTrace, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · cases v with
        | none => simp
        | some v =>
            obtain ⟨d, hd⟩ := level_dist_finite G labels (slope + 1)
              (8 * (M * (2 * 2 ^ rounds))) 0 v
            simp [hd]
      · cases v with
        | none => simp
        | some v =>
            obtain ⟨d, hd⟩ := level_dist_finite G labels (slope + 1)
              (8 * (M * (2 * 2 ^ rounds))) (4 * (M * (2 * 2 ^ rounds))) v
            simp [hd]
      · exact ih _ _ q hq hden v

theorem levelTrace_denominator (call : Oracle (Option V)) (G : Graph V)
    (M rounds slope : ℕ) (labels : V → ℕ) :
    ∀ q ∈ levelTrace call G M rounds slope labels, q.denominator = 100 * M := by
  induction rounds generalizing slope labels with
  | zero => simp [levelTrace]
  | succ rounds ih =>
      intro q hq
      simp only [levelTrace, List.mem_cons] at hq
      rcases hq with rfl | rfl | hq
      · rfl
      · rfl
      · exact ih _ _ q hq

def Query.Reachable (q : Query V) : Prop :=
  ∀ v, q.graph.dist q.source v ≠ ⊤

theorem Query.reachable_positive (q : Query V) (h : q.Reachable) : q.positive.Reachable := by
  intro v
  lift q.graph.dist q.source v to ℕ using h v with d hd
  obtain ⟨e, he, _, _⟩ := affine_dist_bounds q.graph
    (3 * Fintype.card V * q.denominator) 1 hd.symm
  simp [Query.positive, he]

theorem smoothingTrace_reachable (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) (hreach : ∀ v, G.dist s v ≠ ⊤) :
    ∀ q ∈ smoothingTrace baseCall levelCall G s rounds,
      q.elim (fun q => 0 < q.positive.denominator ∧ q.positive.Reachable)
        (fun q => 0 < q.positive.denominator ∧ q.positive.Reachable) := by
  intro q hq
  simp only [smoothingTrace, List.mem_cons, List.mem_map] at hq
  rcases hq with rfl | ⟨q, hq, rfl⟩
  · exact ⟨show 0 < (3 : ℕ) from by decide, Query.reachable_positive _ hreach⟩
  · have hM : 0 < smoothingScale rounds + rounds := by
      have hh := smoothingScale_pos rounds
      omega
    have hden := levelTrace_denominator levelCall G (smoothingScale rounds + rounds)
      rounds (smoothingScale rounds) _ q hq
    have hdenpos : 0 < q.denominator := by rw [hden]; positivity
    refine ⟨by dsimp [Query.positive]; positivity, ?_⟩
    apply Query.reachable_positive
    exact levelTrace_reachable levelCall G _ rounds _ _ q hq hdenpos

theorem smoothingQueryWeightBound_good (n rounds W r : ℕ)
    (hr : 1024 ≤ r) (hn : n ≤ r) (hM : smoothingScale rounds + rounds ≤ r)
    (hT : 2 ^ rounds ≤ r ^ 8) (hW : W ≤ r ^ 3) :
    smoothingQueryWeightBound n rounds W ≤ r ^ 18 := by
  let M := smoothingScale rounds + rounds
  have htheta : 300 * (n + 1) * M ≤ r ^ 3 := by
    calc
      _ ≤ 300 * (r + 1) * r := by gcongr
      _ ≤ r ^ 2 * r := Nat.mul_le_mul_right _ (by nlinarith)
      _ = r ^ 3 := by ring
  have h8 : 8 ≤ r ^ 3 := by
    calc
      8 = 2 ^ 3 := by decide
      _ ≤ r ^ 3 := by gcongr; omega
  have hsmall : 8 * 2 ^ rounds ≤ r ^ 11 := by
    calc
      _ ≤ r ^ 3 * r ^ 8 := Nat.mul_le_mul h8 hT
      _ = r ^ 11 := by ring
  have hsum : 8 * 2 ^ rounds + W ≤ r ^ 12 := by
    calc
      _ ≤ r ^ 11 + r ^ 3 := Nat.add_le_add hsmall hW
      _ = r ^ 3 + r ^ 11 := by omega
      _ ≤ r ^ 12 := pow_sum_bound r 3 11 (by omega) (by omega)
  have hinner : W + M * (8 * 2 ^ rounds + W) ≤ r ^ 14 := by
    calc
      _ ≤ r ^ 3 + r * r ^ 12 := by gcongr
      _ = r ^ 3 + r ^ 13 := by ring
      _ ≤ r ^ 14 := pow_sum_bound r 3 13 (by omega) (by omega)
  unfold smoothingQueryWeightBound
  change 300 * (n + 1) * M * (W + M * (8 * 2 ^ rounds + W)) + 1 ≤ _
  calc
    _ ≤ r ^ 3 * r ^ 14 + 1 := Nat.add_le_add_right (Nat.mul_le_mul htheta hinner) 1
    _ = r ^ 0 + r ^ 17 := by ring
    _ ≤ r ^ 18 := pow_sum_bound r 0 17 (by omega) (by omega)

theorem capped_query_accurate (r : ℕ) (hr : 1024 ≤ r) (call : Oracle V)
    (q : Query V) (hden : 0 < q.denominator) (hreach : q.Reachable)
    (hcard : Fintype.card V ≤ r ^ 2) (hW : WeightsBounded q.graph (r ^ 18))
    (hraw : q.Accurate call) : q.Accurate (cappedOracle (r ^ 32) call) := by
  apply cappedOracle_preserves_accuracy _ _ _ hraw
  have hdist : ∀ v, ∃ d : ℕ, q.graph.dist q.source v = d ∧ d ≤ r ^ 20 := by
    intro v
    lift q.graph.dist q.source v to ℕ using hreach v with d hd
    refine ⟨d, rfl, ?_⟩
    have hb := dist_bound q.graph (r ^ 18) hW hd.symm
    calc
      d ≤ r ^ 18 * (Fintype.card V - 1) := hb
      _ ≤ r ^ 18 * r ^ 2 := by gcongr; omega
      _ = r ^ 20 := by ring
  have ha := approx_answer_bound q.graph q.source q.denominator (r ^ 20) _ hden hraw hdist
  intro v
  calc
    call q.graph q.source q.denominator q.clock v ≤ 2 * r ^ 20 := ha v
    _ ≤ r ^ 21 := by
      rw [show r ^ 21 = r ^ 20 * r from pow_succ r 20]
      exact (Nat.mul_le_mul_right (r ^ 20) (show 2 ≤ r by omega)).trans_eq
        (Nat.mul_comm r (r ^ 20))
    _ ≤ r ^ 32 := by gcongr; omega

theorem guarded_smoothing_success (r : ℕ) (hr : 1024 ≤ r)
    (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ)
    (hn : Fintype.card V ≤ r) (hM : smoothingScale rounds + rounds ≤ r)
    (hT : 2 ^ rounds ≤ r ^ 8) (hW : WeightsBounded G (r ^ 3))
    (hreach : ∀ v, G.dist s v ≠ ⊤)
    (hs : ∀ q ∈ smoothingTrace
      (nonnegativeOracle (cappedOracle (r ^ 32) positiveBase))
      (nonnegativeOracle (cappedOracle (r ^ 32) positiveLevel)) G s rounds,
      PositiveAccurate positiveBase positiveLevel q) :
    FullSmoothingSuccess (nonnegativeOracle (cappedOracle (r ^ 32) positiveBase))
      (nonnegativeOracle (cappedOracle (r ^ 32) positiveLevel)) G s rounds := by
  apply smoothingTrace_success
  intro q hq
  have hbounds := smoothingTrace_positive_bounds _ _ G s rounds (r ^ 3) hW q hq
  have hgood := smoothingQueryWeightBound_good (Fintype.card V) rounds (r ^ 3) r hr hn hM hT le_rfl
  have hreachable := smoothingTrace_reachable _ _ G s rounds hreach q hq
  have hraw := hs q hq
  cases q with
  | inl q =>
      exact capped_query_accurate r hr positiveBase q.positive hreachable.1 hreachable.2
        (by nlinarith) (weightsBounded_mono _ hbounds.2 hgood) hraw
  | inr q =>
      exact capped_query_accurate r hr positiveLevel q.positive hreachable.1 hreachable.2
        (by rw [Fintype.card_option]; nlinarith)
        (weightsBounded_mono _ hbounds.2 hgood) hraw

theorem guarded_outer_success (r : ℕ) (hr : 1024 ≤ r)
    (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations D : ℕ) (potential : V → ℕ)
    (hn : Fintype.card V ≤ r) (hM : smoothingScale rounds + rounds ≤ r)
    (hP : inflation (Fintype.card V) ≤ r) (hT : 2 ^ rounds ≤ r ^ 8)
    (hD : D ≤ r) (hW : WeightsBounded G r)
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ D)
    (hbudget : 2 * smoothingScale rounds *
      (inflation (Fintype.card V) * D + Fintype.card V) ≤ 2 ^ rounds)
    (hfeasible : Feasible G potential) (hsource : potential s = 0)
    (hresidual : ResidualBound G s potential D)
    (hs : ∀ q ∈ outerTrace
      (nonnegativeOracle (cappedOracle (r ^ 32) positiveBase))
      (nonnegativeOracle (cappedOracle (r ^ 32) positiveLevel)) G s rounds iterations potential,
      PositiveAccurate positiveBase positiveLevel q) :
    OuterSuccess (nonnegativeOracle (cappedOracle (r ^ 32) positiveBase))
      (nonnegativeOracle (cappedOracle (r ^ 32) positiveLevel))
      G s rounds iterations potential := by
  induction iterations generalizing potential with
  | zero => trivial
  | succ iterations ih =>
      let offset := iterations * (1 + 2 * rounds)
      let base := nonnegativeOracle (cappedOracle (r ^ 32) positiveBase)
      let level := nonnegativeOracle (cappedOracle (r ^ 32) positiveLevel)
      let currentBase := offsetOracle offset base
      let currentLevel := offsetOracle offset level
      let next := potentialStep currentBase currentLevel G s rounds potential
      have hp : ∀ v, potential v ≤ r := by
        intro v
        obtain ⟨d, hd, hdb⟩ := hreach v
        exact (feasible_le_dist G potential hfeasible hsource hd).trans (hdb.trans hD)
      have hR := reweight_weightsBounded G r r potential hW hp
      have hB := affine_weightsBounded (reweight G potential) (r + r)
        (inflation (Fintype.card V)) 1 hR
      have hB' : WeightsBounded (positiveResidual G potential) (r ^ 3) := by
        apply weightsBounded_mono _ hB
        calc
          inflation (Fintype.card V) * (r + r) + 1 ≤ r * (r + r) + 1 := by gcongr
          _ ≤ r ^ 3 := by
            have hh : 2 * r + 1 ≤ r ^ 2 := by nlinarith
            have hh' := Nat.mul_le_mul_right r hh
            nlinarith
      have hBreach : ∀ v, (positiveResidual G potential).dist s v ≠ ⊤ := by
        intro v
        obtain ⟨d, hd, _⟩ := hresidual v
        obtain ⟨e, he, _, _⟩ := affine_dist_bounds (reweight G potential)
          (inflation (Fintype.card V)) 1 hd
        simp [positiveResidual, he]
      have hc : FullSmoothingSuccess currentBase currentLevel (positiveResidual G potential) s rounds := by
        change FullSmoothingSuccess
          (offsetOracle offset (nonnegativeOracle (cappedOracle (r ^ 32) positiveBase)))
          (offsetOracle offset (nonnegativeOracle (cappedOracle (r ^ 32) positiveLevel))) _ _ _
        rw [← nonnegativeOracle_offset, ← nonnegativeOracle_offset]
        change FullSmoothingSuccess
          (nonnegativeOracle (cappedOracle (r ^ 32) (offsetOracle offset positiveBase)))
          (nonnegativeOracle (cappedOracle (r ^ 32) (offsetOracle offset positiveLevel))) _ _ _
        apply guarded_smoothing_success r hr _ _ _ s rounds hn hM hT hB' hBreach
        intro q hq
        have hh := hs (offsetQuery offset q) (by
          apply List.mem_append_left
          exact List.mem_map.mpr ⟨q, hq, rfl⟩)
        cases q <;> exact hh
      have hnext := potentialStep_correct currentBase currentLevel G s rounds D potential
        hbudget hfeasible hsource hresidual hc
      refine ⟨hc, ih next hnext.1 hnext.2.1 ?_ ?_⟩
      · intro v
        obtain ⟨d, hd, hdb⟩ := hnext.2.2 v
        exact ⟨d, hd, hdb.trans (Nat.div_le_self D 2)⟩
      · intro q hq
        exact hs q (List.mem_append_right _ hq)

theorem exact_guarded_raw_correct (positiveBase : Oracle V) (positiveLevel : Oracle (Option V))
    (G : Graph V) (s : V) (bits : ℕ)
    (hn : Fintype.card V ≤ 2 ^ bits) (hW : WeightsBounded G (2 ^ bits))
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ 2 ^ bits)
    (hs : ∀ q ∈ outerTrace
      (nonnegativeOracle (cappedOracle (replyCap bits) positiveBase))
      (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel))
      G s (smoothingRounds bits) (bits + 1) (fun _ => 0),
      PositiveAccurate positiveBase positiveLevel q) :
    ∀ v, G.dist s v =
      (exactDistances
        (nonnegativeOracle (cappedOracle (replyCap bits) positiveBase))
        (nonnegativeOracle (cappedOracle (replyCap bits) positiveLevel)) G s bits v : Distance) := by
  have hb := schedule_small_bounds bits (Fintype.card V) (2 ^ bits) hn le_rfl
  apply exactDistances_correct _ _ G s bits hn hreach
  apply guarded_outer_success (smallBound bits) hb.1 positiveBase positiveLevel G s
    (smoothingRounds bits) (bits + 1) (2 ^ bits) (fun _ => 0)
    hb.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.2 hb.2.2.1
    (weightsBounded_mono _ hW hb.2.2.1) hreach
    (exact_schedule_budget bits _ _ hn le_rfl) (zero_feasible G) rfl
    (by simpa [ResidualBound] using hreach) hs

end StreamingSSSP.Exact
