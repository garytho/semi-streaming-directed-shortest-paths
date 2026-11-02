module

public import StreamingSSSP.Hopset.PathProcessMoments
public import StreamingSSSP.Hopset.PathProcessWeight
public import StreamingSSSP.Hopset.PathNumerics

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

section Means

variable (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (root : State cfg stored input 0)

def meanZ (r : ℕ) : ℝ :=
  (pathStateLaw cfg ps hnum stored input root r).expect (liftCount (State.primeCount hnum))

def meanY (r : ℕ) : ℝ :=
  (pathStateLaw cfg ps hnum stored input root r).expect (liftCount (State.primeRelated hnum))

def meanRawZ (r : ℕ) : ℝ :=
  (pathStateLaw cfg ps hnum stored input root r).expect (liftCount State.rawCount)

def meanRawY (r : ℕ) : ℝ :=
  (pathStateLaw cfg ps hnum stored input root r).expect (liftCount State.rawRelated)

theorem meanZ_nonneg (r : ℕ) : 0 ≤ meanZ cfg ps hnum stored input root r :=
  Law.expect_nonneg _ _ (liftCount_nonneg _)

theorem meanY_nonneg (r : ℕ) : 0 ≤ meanY cfg ps hnum stored input root r :=
  Law.expect_nonneg _ _ (liftCount_nonneg _)

theorem meanRawZ_step (r : ℕ) (hnumeric : EarlyNumerics n cfg ps r) :
    meanRawZ cfg ps hnum stored input root (r + 1) ≤
      2 * meanZ cfg ps hnum stored input root r +
        2 * (Ranks.rate ps r).value * meanY cfg ps hnum stored input root r := by
  let mu := pathStateLaw cfg ps hnum stored input root r
  calc
    _ = mu.expect (fun state => (pathStep cfg ps hnum stored input r state).expect (liftCount State.rawCount)) := by
      rw [meanRawZ, pathStateLaw, Law.expect_bind]
    _ ≤ mu.expect (fun state =>
        2 * liftCount (State.primeCount hnum) state +
          2 * (Ranks.rate ps r).value * liftCount (State.primeRelated hnum) state) :=
      Law.expect_mono mu (pathStep_count cfg ps hnum stored input r hnumeric.before hnumeric.balls
        hnumeric.grid hnumeric.cuts)
    _ = _ := by
      rw [Law.expect_add, Law.expect_mul, Law.expect_mul]
      rfl

theorem meanRawY_step (r : ℕ) (hnumeric : EarlyNumerics n cfg ps r) :
    meanRawY cfg ps hnum stored input root (r + 1) ≤
      (18 / (Ranks.rate ps r).value) * meanZ cfg ps hnum stored input root r := by
  let mu := pathStateLaw cfg ps hnum stored input root r
  calc
    _ = mu.expect (fun state => (pathStep cfg ps hnum stored input r state).expect (liftCount State.rawRelated)) := by
      rw [meanRawY, pathStateLaw, Law.expect_bind]
    _ ≤ mu.expect (fun state =>
        (18 / (Ranks.rate ps r).value) * liftCount (State.primeCount hnum) state) :=
      Law.expect_mono mu (pathStep_related cfg ps hnum stored input r hnumeric.before hnumeric.rankIndex hnumeric.prefixHalf
        hnumeric.balls hnumeric.grid hnumeric.groups hnumeric.positive hnumeric.related)
    _ = _ := by
      rw [Law.expect_mul]
      rfl

theorem meanZ_split (W r : ℕ) (hroot : weight cfg.inputScale root.paths ≤ W) :
    meanZ cfg ps hnum stored input root r ≤
      meanRawZ cfg ps hnum stored input root r + (W : ℝ) / Reference.distanceScale cfg r :=
  primeCount_expect_le hnum _ W (pathStateLaw_weight ps hnum root W hroot r)

theorem meanY_split (W r : ℕ) (hroot : weight cfg.inputScale root.paths ≤ W) (hb : 1 ≤ Parameters.ballSize n r) :
    meanY cfg ps hnum stored input root r ≤
      meanRawY cfg ps hnum stored input root r +
        2 * Parameters.ballSize n r * ((W : ℝ) / Reference.distanceScale cfg r) :=
  primeRelated_expect_le hnum _ W (pathStateLaw_weight ps hnum root W hroot r) hb

end Means

theorem scalar_piece_recurrence (z₀ z₁ z₂ y rawY B₁ B₂ p₀ p₁ b k ell : ℝ)
    (hz : 0 ≤ z₀) (hB : 0 ≤ B₁) (hp₀ : 0 < p₀) (hp₁ : 0 ≤ p₁)
    (hrate : p₁ ≤ k * p₀) (hbalance : b * p₁ ≤ 200 * k * ell)
    (hraw : rawY ≤ (18 / p₀) * z₀) (hy : y ≤ rawY + 2 * b * B₁)
    (hstep : z₂ ≤ 2 * z₁ + 2 * p₁ * y + B₂) :
    z₂ ≤ 2 * z₁ + 36 * k * z₀ + B₂ + 800 * k * ell * B₁ := by
  have hr : p₁ / p₀ ≤ k := (div_le_iff₀ hp₀).mpr hrate
  have hterm : 2 * p₁ * ((18 / p₀) * z₀) ≤ 36 * k * z₀ := by
    calc
      _ = (p₁ / p₀) * (36 * z₀) := by ring
      _ ≤ k * (36 * z₀) := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  have hboost : (2 * p₁) * (2 * b * B₁) ≤ 800 * k * ell * B₁ := by
    calc
      _ = (b * p₁) * (4 * B₁) := by ring
      _ ≤ (200 * k * ell) * (4 * B₁) := mul_le_mul_of_nonneg_right hbalance (by positivity)
      _ = _ := by ring
  have hraw' := mul_le_mul_of_nonneg_left hraw (show 0 ≤ 2 * p₁ by positivity)
  have hy' := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2 * p₁ by positivity)
  linarith

theorem meanZ_recurrence (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (root : State cfg stored input 0)
    (W r : ℕ) (hroot : weight cfg.inputScale root.paths ≤ W)
    (hnum₀ : EarlyNumerics n cfg ps r) (hnum₁ : EarlyNumerics n cfg ps (r + 1))
    (hrate : (Ranks.rate ps (r + 1)).value ≤ (cfg.k : ℝ) * (Ranks.rate ps r).value) :
    meanZ cfg ps hnum stored input root (r + 2) ≤
      2 * meanZ cfg ps hnum stored input root (r + 1) + 36 * cfg.k * meanZ cfg ps hnum stored input root r +
        (W : ℝ) / Reference.distanceScale cfg (r + 2) +
        800 * cfg.k * cfg.logarithm * ((W : ℝ) / Reference.distanceScale cfg (r + 1)) := by
  have hz := meanZ_split cfg ps hnum stored input root W (r + 2) hroot
  have hnext := meanRawZ_step cfg ps hnum stored input root (r + 1) hnum₁
  have hy := meanY_split cfg ps hnum stored input root W (r + 1) hroot hnum₁.balls
  have hraw := meanRawY_step cfg ps hnum stored input root r hnum₀
  have hstep : meanZ cfg ps hnum stored input root (r + 2) ≤
      2 * meanZ cfg ps hnum stored input root (r + 1) +
        2 * (Ranks.rate ps (r + 1)).value * meanY cfg ps hnum stored input root (r + 1) +
        (W : ℝ) / Reference.distanceScale cfg (r + 2) := by
    have he : r + 1 + 1 = r + 2 := by omega
    rw [he] at hnext
    linarith
  exact scalar_piece_recurrence _ _ _ _ _ _ _ _ _ _ _ _
    (meanZ_nonneg cfg ps hnum stored input root r)
    (div_nonneg (Nat.cast_nonneg W) (Reference.distanceScale_pos cfg hnum (r + 1)).le)
    hnum₀.positive hnum₁.positive.le hrate hnum₁.balance hraw hy hstep

end

end StreamingSSSP.Hopset.Following
