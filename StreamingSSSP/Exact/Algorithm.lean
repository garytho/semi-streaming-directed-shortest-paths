module

public import StreamingSSSP.Exact.Potential

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

theorem smoothingScale_pos (rounds : ℕ) : 0 < smoothingScale rounds := by
  unfold smoothingScale
  positivity

def ResidualBound (G : Graph V) (s : V) (potential : V → ℕ) (bound : ℕ) : Prop :=
  ∀ v, ∃ d : ℕ, (reweight G potential).dist s v = d ∧ d ≤ bound

def positiveResidual (G : Graph V) (potential : V → ℕ) : Graph V :=
  affineGraph (reweight G potential) (inflation (Fintype.card V)) 1

def potentialIncrement (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) (potential : V → ℕ) : V → ℕ :=
  roundedUpdate
    (smoothing baseCall levelCall (positiveResidual G potential) s rounds)
    (smoothingScale rounds) (smoothingScale_pos rounds)

def potentialStep (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) (potential : V → ℕ) : V → ℕ :=
  fun v => potential v + potentialIncrement baseCall levelCall G s rounds potential v

theorem potentialIncrement_correct (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds bound : ℕ) (potential : V → ℕ)
    (hbudget : 2 * smoothingScale rounds *
      (inflation (Fintype.card V) * bound + Fintype.card V) ≤ 2 ^ rounds)
    (hresidual : ResidualBound G s potential bound)
    (hsuccess : FullSmoothingSuccess baseCall levelCall (positiveResidual G potential) s rounds) :
    let update := potentialIncrement baseCall levelCall G s rounds potential
    update s = 0 ∧ Feasible (reweight G potential) update ∧
      ∀ v (d : ℕ), (reweight G potential).dist s v = d → d ≤ 2 * update v := by
  let R := reweight G potential
  let P := inflation (Fintype.card V)
  let B := positiveResidual G potential
  let C := smoothingScale rounds
  let labels := smoothing baseCall levelCall B s rounds
  have hBbound : ∀ v, ∃ d : ℕ, B.dist s v = d ∧ d ≤ P * bound + Fintype.card V := by
    intro v
    obtain ⟨d, hd, hdb⟩ := hresidual v
    obtain ⟨e, he, _, hu⟩ := affine_dist_bounds R P 1 hd
    exact ⟨e, he, by nlinarith [Nat.mul_le_mul_left P hdb, Nat.sub_le (Fintype.card V) 1]⟩
  have hs := smoothing_correct baseCall levelCall B s rounds _ hBbound hbudget hsuccess
  refine ⟨roundedUpdate_source labels C (smoothingScale_pos rounds) hs.1, ?_, ?_⟩
  · apply roundedUpdate_feasible R labels C (smoothingScale_pos rounds)
    intro u v w hw
    have he : B u v = ((P * w + 1 : ℕ) : Distance) := by
      exact mapWeights_coe R _ hw
    exact hs.2.2.1 u v (P * w + 1) he (Nat.succ_pos _)
  · intro v d hd
    obtain ⟨e, he, hl, _⟩ := affine_dist_bounds R P 1 hd
    have hnon := hs.2.1 v e he
    apply roundedUpdate_halves labels C (smoothingScale_pos rounds)
    nlinarith [Nat.mul_le_mul_left C hl]

theorem potentialStep_correct (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds bound : ℕ) (potential : V → ℕ)
    (hbudget : 2 * smoothingScale rounds *
      (inflation (Fintype.card V) * bound + Fintype.card V) ≤ 2 ^ rounds)
    (hfeasible : Feasible G potential) (hsource : potential s = 0)
    (hresidual : ResidualBound G s potential bound)
    (hsuccess : FullSmoothingSuccess baseCall levelCall (positiveResidual G potential) s rounds) :
    let next := potentialStep baseCall levelCall G s rounds potential
    Feasible G next ∧ next s = 0 ∧ ResidualBound G s next (bound / 2) := by
  let update := potentialIncrement baseCall levelCall G s rounds potential
  have hu := potentialIncrement_correct baseCall levelCall G s rounds bound potential
    hbudget hresidual hsuccess
  have hupdatezero : update s = 0 := hu.1
  refine ⟨feasible_add G potential update hfeasible hu.2.1, ?_, ?_⟩
  · change potential s + update s = 0
    rw [hsource, hupdatezero, zero_add]
  · intro v
    obtain ⟨d, hd, hdb⟩ := hresidual v
    obtain ⟨r, hr, hrt⟩ := reweight_dist (reweight G potential) update hu.2.1 hd
    have hdq := hu.2.2 v d hd
    change d ≤ 2 * update v at hdq
    rw [hupdatezero, Nat.add_zero] at hrt
    have hbound : r ≤ bound / 2 := by omega
    refine ⟨r, ?_, hbound⟩
    change (reweight G (fun v => potential v + update v)).dist s v = r
    rw [reweight_add G potential update hfeasible hu.2.1]
    exact hr

def outerFrom (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) : ℕ → (V → ℕ) → V → ℕ
  | 0, potential => potential
  | iterations + 1, potential =>
      let offset := iterations * (1 + 2 * rounds)
      outerFrom baseCall levelCall G s rounds iterations
        (potentialStep (offsetOracle offset baseCall) (offsetOracle offset levelCall)
          G s rounds potential)

def OuterSuccess (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) : ℕ → (V → ℕ) → Prop
  | 0, _ => True
  | iterations + 1, potential =>
      let offset := iterations * (1 + 2 * rounds)
      FullSmoothingSuccess (offsetOracle offset baseCall) (offsetOracle offset levelCall)
        (positiveResidual G potential) s rounds ∧
      OuterSuccess baseCall levelCall G s rounds iterations
        (potentialStep (offsetOracle offset baseCall) (offsetOracle offset levelCall)
          G s rounds potential)

theorem outerFrom_correct (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations bound : ℕ) (potential : V → ℕ)
    (hbudget : 2 * smoothingScale rounds *
      (inflation (Fintype.card V) * bound + Fintype.card V) ≤ 2 ^ rounds)
    (hfeasible : Feasible G potential) (hsource : potential s = 0)
    (hresidual : ResidualBound G s potential bound)
    (hsuccess : OuterSuccess baseCall levelCall G s rounds iterations potential) :
    let out := outerFrom baseCall levelCall G s rounds iterations potential
    Feasible G out ∧ out s = 0 ∧ ResidualBound G s out (bound / 2 ^ iterations) := by
  induction iterations generalizing potential bound with
  | zero =>
      exact ⟨hfeasible, hsource, by simpa [outerFrom] using hresidual⟩
  | succ iterations ih =>
      let offset := iterations * (1 + 2 * rounds)
      let currentBase := offsetOracle offset baseCall
      let currentLevel := offsetOracle offset levelCall
      have hs := potentialStep_correct currentBase currentLevel G s rounds bound potential
        hbudget hfeasible hsource hresidual hsuccess.1
      have hb : 2 * smoothingScale rounds *
          (inflation (Fintype.card V) * (bound / 2) + Fintype.card V) ≤ 2 ^ rounds := by
        exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right
          (Nat.mul_le_mul_left _ (Nat.div_le_self bound 2)) _)).trans hbudget
      have hi := ih (bound / 2) (potentialStep currentBase currentLevel G s rounds potential)
        hb hs.1 hs.2.1 hs.2.2 hsuccess.2
      refine ⟨hi.1, hi.2.1, ?_⟩
      change ResidualBound G s
        (outerFrom baseCall levelCall G s rounds iterations
          (potentialStep currentBase currentLevel G s rounds potential)) (bound / 2 ^ (iterations + 1))
      simpa only [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using hi.2.2

/-- Exactness is a consequence of the actual successful approximation trace;
neither smoothness nor a prior exact-to-approximate reduction is assumed. -/
theorem exact_from_approximate (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds iterations bound : ℕ)
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ bound)
    (hbudget : 2 * smoothingScale rounds *
      (inflation (Fintype.card V) * bound + Fintype.card V) ≤ 2 ^ rounds)
    (hiterations : bound < 2 ^ iterations)
    (hsuccess : OuterSuccess baseCall levelCall G s rounds iterations (fun _ => 0)) :
    ∀ v, G.dist s v =
      (outerFrom baseCall levelCall G s rounds iterations (fun _ => 0) v : Distance) := by
  have hi := outerFrom_correct baseCall levelCall G s rounds iterations bound (fun _ => 0)
    hbudget (zero_feasible G) rfl (by simpa [ResidualBound] using hreach) hsuccess
  have hzero : bound / 2 ^ iterations = 0 := Nat.div_eq_of_lt hiterations
  intro v
  obtain ⟨d, hd, _⟩ := hreach v
  obtain ⟨r, hr, hrv⟩ := reweight_dist G
    (outerFrom baseCall levelCall G s rounds iterations (fun _ => 0)) hi.1 hd
  obtain ⟨q, hq, hqbound⟩ := hi.2.2 v
  have hqr : q = r := WithTop.coe_eq_coe.mp (hq.symm.trans hr)
  have heq : d = outerFrom baseCall levelCall G s rounds iterations (fun _ => 0) v := by
    rw [hi.2.1] at hrv
    omega
  simpa [heq] using hd

end StreamingSSSP.Exact
