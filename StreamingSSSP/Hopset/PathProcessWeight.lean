module

public import StreamingSSSP.Hopset.PathProcess

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {r : ℕ}

def WeightBound (W : ℕ) : Option (State cfg stored input r) → Prop
  | none => True
  | some st => weight cfg.inputScale st.paths ≤ W

theorem pathStep_weight (ps : List Rate) (hnum : 0 < cfg.initialNumerator) (W : ℕ)
    (state : Option (State cfg stored input r)) (hw : WeightBound W state) :
    Early.Sampling.Holds (pathStep cfg ps hnum stored input r state) (WeightBound W) := by
  cases state with
  | none => exact Early.Sampling.holds_pure none _ trivial
  | some st =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : Batched.AllGood cfg stored input r st.queue
        · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte]
          refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
          intro sample _
          exact (st.update_weight_le hnum he sample).trans hw
        · simpa only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte] using
            Early.Sampling.holds_pure (none : Option (State cfg stored input (r + 1))) (WeightBound W) trivial
      · simpa only [pathStep, he, ↓reduceDIte] using
          Early.Sampling.holds_pure (none : Option (State cfg stored input (r + 1))) (WeightBound W) trivial

theorem pathStateLaw_weight (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (root : State cfg stored input 0) (W : ℕ) (hroot : weight cfg.inputScale root.paths ≤ W) (r : ℕ) :
    Early.Sampling.Holds (pathStateLaw cfg ps hnum stored input root r) (WeightBound W) := by
  induction r with
  | zero => exact Early.Sampling.holds_pure (some root) _ hroot
  | succ r ih =>
      exact Reference.holds_bind_on _ _ (WeightBound W) (WeightBound W) ih
        (fun state hw => pathStep_weight ps hnum W state hw)

theorem liftCount_add {A : Type*} (f g : A → ℕ) :
    liftCount (fun a => f a + g a) = fun state => liftCount f state + liftCount g state := by
  funext state
  cases state <;> simp [liftCount]

theorem liftCount_nonneg {A : Type*} (f : A → ℕ) (state : Option A) : 0 ≤ liftCount f state := by
  cases state <;> simp [liftCount]

theorem splitCount_expect_le (hnum : 0 < cfg.initialNumerator) (mu : Law (Option (State cfg stored input r)))
    (W : ℕ) (hw : Early.Sampling.Holds mu (WeightBound W)) :
    mu.expect (liftCount (State.splitCount hnum)) ≤ (W : ℝ) / Reference.distanceScale cfg r := by
  have hD := Reference.distanceScale_pos cfg hnum r
  have hpoint : Early.Sampling.Holds mu (fun state =>
      liftCount (State.splitCount hnum) state ≤ (W : ℝ) / Reference.distanceScale cfg r) := by
    refine Early.Sampling.holds_mono hw ?_
    intro state hs
    cases state with
    | none => exact div_nonneg (Nat.cast_nonneg W) hD.le
    | some st =>
        change (st.splitCount hnum : ℝ) ≤ (W : ℝ) / Reference.distanceScale cfg r
        apply (le_div_iff₀ hD).mpr
        exact (st.splitCount_credit hnum).trans (by exact_mod_cast hs)
  exact (Early.Sampling.expect_mono_on mu hpoint).trans_eq (Law.expect_const mu _)

theorem primeCount_expect_le (hnum : 0 < cfg.initialNumerator) (mu : Law (Option (State cfg stored input r)))
    (W : ℕ) (hw : Early.Sampling.Holds mu (WeightBound W)) :
    mu.expect (liftCount (State.primeCount hnum)) ≤
      mu.expect (liftCount State.rawCount) + (W : ℝ) / Reference.distanceScale cfg r := by
  have hf : (liftCount (State.primeCount hnum) : Option (State cfg stored input r) → ℝ) = fun state =>
      liftCount State.rawCount state + liftCount (State.splitCount hnum) state := by
    funext state
    cases state <;> simp only [liftCount, State.primeCount_eq, Nat.cast_add, add_zero]
  rw [hf, Law.expect_add]
  have hs := splitCount_expect_le hnum mu W hw
  linarith

theorem primeRelated_expect_le (hnum : 0 < cfg.initialNumerator) (mu : Law (Option (State cfg stored input r)))
    (W : ℕ) (hw : Early.Sampling.Holds mu (WeightBound W)) (hb : 1 ≤ Parameters.ballSize n r) :
    mu.expect (liftCount (State.primeRelated hnum)) ≤
      mu.expect (liftCount State.rawRelated) + 2 * Parameters.ballSize n r * ((W : ℝ) / Reference.distanceScale cfg r) := by
  have hpoint : ∀ state : Option (State cfg stored input r),
      liftCount (State.primeRelated hnum) state ≤
        liftCount State.rawRelated state + 2 * Parameters.ballSize n r * liftCount (State.splitCount hnum) state := by
    intro state
    cases state with
    | none => simp [liftCount]
    | some st =>
        have hs := st.primeRelated_le hnum hb
        simp only [liftCount]
        exact_mod_cast hs
  have hm := Law.expect_mono mu hpoint
  rw [Law.expect_add, Law.expect_mul] at hm
  exact hm.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (splitCount_expect_le hnum mu W hw) (by positivity)))

end

end StreamingSSSP.Hopset.Following
