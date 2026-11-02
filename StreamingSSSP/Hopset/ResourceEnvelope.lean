module

public import StreamingSSSP.Hopset.AsymptoticCalibration
public import StreamingSSSP.Approx.SolveResources
public import StreamingSSSP.Approx.MetadataWordBounds

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingSSSP.Hopset.Measured

open Parameters

def envelopeLevel (coefficient : ℕ) : ℕ := 40 * coefficient + 21

def envelopeBase (coefficient exponent confidence : ℕ) : ℕ :=
  2 ^ 40 * (100 ^ (envelopeLevel coefficient + 3) * 4097 ^ (envelopeLevel coefficient + 3) +
    (confidence + 17) * (2 * exponent + 4) + 20 * coefficient + exponent + confidence +
    coefficient + 16785409 + 1)

def envelopeDegree (coefficient : ℕ) : ℕ := 10 * envelopeLevel coefficient + 100

def envelope (n coefficient exponent confidence : ℕ) : ℕ :=
  envelopeBase coefficient exponent confidence ^ 10 * ell n ^ envelopeDegree coefficient

theorem envelope_base_facts (coefficient exponent confidence : ℕ) :
    1024 ≤ envelopeBase coefficient exponent confidence ∧
      20 * coefficient ≤ envelopeBase coefficient exponent confidence ∧
      (confidence + 17) * (2 * exponent + 4) ≤ envelopeBase coefficient exponent confidence ∧
      4097 ^ (envelopeLevel coefficient + 3) ≤ envelopeBase coefficient exponent confidence ∧
      2 ^ 31 * 100 ^ (envelopeLevel coefficient + 2) *
        4097 ^ (envelopeLevel coefficient + 3) ≤ envelopeBase coefficient exponent confidence := by
  have h100 : 1 ≤ 100 ^ (envelopeLevel coefficient + 3) := by change 0 < _; positivity
  have h4097 : 1 ≤ 4097 ^ (envelopeLevel coefficient + 3) := by change 0 < _; positivity
  have hpow : 100 ^ (envelopeLevel coefficient + 2) ≤ 100 ^ (envelopeLevel coefficient + 3) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hprod := Nat.mul_le_mul_right (4097 ^ (envelopeLevel coefficient + 3)) hpow
  unfold envelopeBase
  norm_num only [Nat.reducePow]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  · nlinarith

theorem envelope_dominates (n coefficient exponent confidence a b : ℕ)
    (ha : a ≤ 10) (hb : b ≤ envelopeDegree coefficient) :
    envelopeBase coefficient exponent confidence ^ a * ell n ^ b ≤
      envelope n coefficient exponent confidence := by
  have hbase : 1 ≤ envelopeBase coefficient exponent confidence :=
    (by have h := (envelope_base_facts coefficient exponent confidence).1; omega)
  have he : 1 ≤ ell n := ell_pos n
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hbase ha) (Nat.pow_le_pow_right he hb)

theorem envelope_large (n coefficient exponent confidence : ℕ) :
    1024 ≤ envelope n coefficient exponent confidence := by
  have hb := (envelope_base_facts coefficient exponent confidence).1
  have h := envelope_dominates n coefficient exponent confidence 1 0 (by omega) (by unfold envelopeDegree; omega)
  simp only [pow_one, pow_zero, mul_one] at h
  omega

theorem envelope_logarithm (n coefficient exponent confidence : ℕ) :
    4 * ell n ≤ envelope n coefficient exponent confidence := by
  have hb := (envelope_base_facts coefficient exponent confidence).1
  have h := envelope_dominates n coefficient exponent confidence 1 1 (by omega) (by unfold envelopeDegree; omega)
  simp only [pow_one] at h
  exact (Nat.mul_le_mul_right (ell n) (le_trans (by norm_num : 4 ≤ 1024) hb)).trans h

theorem envelope_copy (n coefficient exponent confidence : ℕ) :
    copyLimit n ≤ n * envelope n coefficient exponent confidence := by
  have hb : 2 ^ 30 ≤ envelopeBase coefficient exponent confidence := by
    have h := (envelope_base_facts coefficient exponent confidence).2.2.2.2
    have hp : 1 ≤ 100 ^ (envelopeLevel coefficient + 2) * 4097 ^ (envelopeLevel coefficient + 3) := by
      change 0 < _
      positivity
    have hmul := Nat.mul_le_mul_left (2 ^ 31) hp
    norm_num only [Nat.reducePow] at *
    nlinarith
  have h := (Nat.mul_le_mul_right (ell n ^ 4) hb).trans
    (by simpa only [pow_one] using (envelope_dominates n coefficient exponent confidence 1 4
      (by omega) (by unfold envelopeDegree; omega)))
  unfold copyLimit
  nlinarith [Nat.mul_le_mul_left n h]

theorem envelope_block (n coefficient exponent confidence : ℕ) :
    blockLimit n ≤ n * envelope n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  have hb : 2 ^ 30 ≤ B := by
    have hbase := (envelope_base_facts coefficient exponent confidence).2.2.2.2
    have hp : 1 ≤ 100 ^ (envelopeLevel coefficient + 2) * 4097 ^ (envelopeLevel coefficient + 3) := by
      change 0 < _
      positivity
    have hm := Nat.mul_le_mul_left (2 ^ 31) hp
    dsimp only [B]
    norm_num only [Nat.reducePow] at *
    nlinarith
  have h4097 : 4097 ≤ B := by
    have h := (envelope_base_facts coefficient exponent confidence).2.2.2.1
    have hp : 4097 ^ 1 ≤ 4097 ^ (envelopeLevel coefficient + 3) :=
      Nat.pow_le_pow_right (by decide) (by unfold envelopeLevel; omega)
    simpa only [pow_one] using hp.trans h
  have hk : k n ≤ B ^ 2 * ell n ^ 2 := by
    have hs : split n ≤ B * ell n := (split_upper n).trans (Nat.mul_le_mul_right _ h4097)
    simpa only [k, mul_pow] using Nat.pow_le_pow_left hs 2
  have hf : 2 ^ 30 * k n * ell n ^ 4 ≤ envelope n coefficient exponent confidence := by
    calc
      _ ≤ B * (B ^ 2 * ell n ^ 2) * ell n ^ 4 := by gcongr
      _ = B ^ 3 * ell n ^ 6 := by ring
      _ ≤ _ := envelope_dominates n coefficient exponent confidence 3 6
        (by omega) (by unfold envelopeDegree; omega)
  unfold blockLimit
  nlinarith [Nat.mul_le_mul_left n hf]

theorem envelope_records (n accuracy coefficient exponent confidence : ℕ)
    (ha : accuracy ≤ coefficient * ell n) :
    recordFactor n accuracy ≤ envelope n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  let L := envelopeLevel coefficient
  have hL : advance n accuracy ≤ L := advance_upper n accuracy coefficient ha
  have hs : 1 ≤ split n := split_pos n
  have hb : 2 ^ 30 ≤ B := by
    have h := (envelope_base_facts coefficient exponent confidence).2.2.2.2
    have hp : 1 ≤ 100 ^ (envelopeLevel coefficient + 2) * 4097 ^ (envelopeLevel coefficient + 3) := by
      change 0 < _
      positivity
    have hm := Nat.mul_le_mul_left (2 ^ 31) hp
    dsimp only [B]
    norm_num only [Nat.reducePow] at *
    nlinarith
  have h4097 : 4097 ^ (L + 3) ≤ B := (envelope_base_facts coefficient exponent confidence).2.2.2.1
  have hp : 4097 ^ (2 * L + 4) ≤ B ^ 2 := by
    calc
      _ ≤ 4097 ^ ((L + 3) * 2) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = (4097 ^ (L + 3)) ^ 2 := pow_mul _ _ _
      _ ≤ _ := Nat.pow_le_pow_left h4097 2
  have hk : k n ^ (advance n accuracy + 2) ≤ B ^ 2 * ell n ^ (2 * L + 4) := by
    calc
      _ = split n ^ (2 * (advance n accuracy + 2)) := (pow_mul _ _ _).symm
      _ ≤ split n ^ (2 * L + 4) := Nat.pow_le_pow_right hs (by omega)
      _ ≤ (4097 * ell n) ^ (2 * L + 4) := Nat.pow_le_pow_left (split_upper n) _
      _ = 4097 ^ (2 * L + 4) * ell n ^ (2 * L + 4) := mul_pow _ _ _
      _ ≤ _ := Nat.mul_le_mul_right _ hp
  unfold recordFactor
  calc
    _ ≤ B * (B ^ 2 * ell n ^ (2 * L + 4)) * ell n ^ 4 := by gcongr
    _ = B ^ 3 * ell n ^ (2 * L + 8) := by
      rw [show 2 * L + 8 = (2 * L + 4) + 4 by omega, pow_add]
      ring
    _ ≤ _ := envelope_dominates n coefficient exponent confidence 3 (2 * L + 8)
      (by omega) (by dsimp only [L]; unfold envelopeDegree; omega)

theorem envelope_level (n coefficient exponent confidence : ℕ) :
    maximumLevel n + 2 ≤ envelope n coefficient exponent confidence := by
  have h := maximumLevel_le_logarithm n
  have he := ell_pos n
  have hb := envelope_logarithm n coefficient exponent confidence
  omega

theorem envelope_headers (n coefficient exponent confidence : ℕ) :
    headerLimit n ≤ n * envelope n coefficient exponent confidence ^ 3 := by
  let E := envelope n coefficient exponent confidence
  have hc := envelope_copy n coefficient exponent confidence
  have hr := envelope_level n coefficient exponent confidence
  have hE : 2 ≤ E := by have h := envelope_large n coefficient exponent confidence; omega
  unfold headerLimit
  calc
    _ ≤ 2 * E * (n * E) := by gcongr <;> omega
    _ ≤ E * E * (n * E) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right E hE)
    _ = _ := by ring

theorem guess_exponent_upper (n wmin wmax exponent : ℕ) (hwmin : 0 < wmin)
    (hw : wmax ≤ (2 * n) ^ exponent) :
    guessExponent n wmin wmax ≤ (2 * exponent + 2) * ell n := by
  have he := ell_pos n
  have hn : 2 * n ≤ 2 ^ (ell n + 1) := by
    rw [pow_succ]
    have h := lt_two_pow_ell n
    omega
  have hm : 2 * n * wmax ≤ 2 ^ ((2 * exponent + 2) * ell n) := by
    calc
      _ ≤ 2 ^ (ell n + 1) * (2 ^ (ell n + 1)) ^ exponent :=
        Nat.mul_le_mul hn (hw.trans (Nat.pow_le_pow_left hn exponent))
      _ = 2 ^ ((ell n + 1) * (exponent + 1)) := by rw [pow_succ, pow_mul]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hbase : 2 ^ ((2 * exponent + 2) * ell n) ≤
      wmin * 2 ^ ((2 * exponent + 2) * ell n) := Nat.le_mul_of_pos_left _ hwmin
  exact firstCross_upper _ _ _ _ _ (hm.trans hbase)

theorem envelope_guesses (n wmin wmax coefficient exponent confidence : ℕ) (hwmin : 0 < wmin)
    (hw : wmax ≤ (2 * n) ^ exponent) :
    guessExponent n wmin wmax + 1 ≤ envelope n coefficient exponent confidence := by
  have hg := guess_exponent_upper n wmin wmax exponent hwmin hw
  have he := ell_pos n
  have hbase := (envelope_base_facts coefficient exponent confidence).2.2.1
  have hconst : 2 * exponent + 3 ≤ envelopeBase coefficient exponent confidence := by nlinarith
  have h := envelope_dominates n coefficient exponent confidence 1 1 (by omega) (by unfold envelopeDegree; omega)
  have hmul := Nat.mul_le_mul_right (ell n) hconst
  simp only [pow_one] at h
  nlinarith

theorem envelope_trials (n wmin wmax coefficient exponent confidence : ℕ) (hwmin : 0 < wmin)
    (hw : wmax ≤ (2 * n) ^ exponent) :
    executionCount n confidence wmin wmax ≤ envelope n coefficient exponent confidence := by
  have hg := guess_exponent_upper n wmin wmax exponent hwmin hw
  have he := ell_pos n
  have hcount : guessExponent n wmin wmax + 1 ≤ (2 * exponent + 3) * ell n := by nlinarith
  have hbase := (envelope_base_facts coefficient exponent confidence).2.2.1
  have hcoeff : (confidence + 16) * (2 * exponent + 3) ≤ envelopeBase coefficient exponent confidence := by
    nlinarith
  unfold executionCount
  calc
    _ ≤ ell n * (((confidence + 16) * ell n) * ((2 * exponent + 3) * ell n)) := by gcongr
    _ = ((confidence + 16) * (2 * exponent + 3)) * ell n ^ 3 := by ring
    _ ≤ envelopeBase coefficient exponent confidence * ell n ^ 3 := Nat.mul_le_mul_right _ hcoeff
    _ ≤ _ := by simpa only [pow_one] using (envelope_dominates n coefficient exponent confidence 1 3
      (by omega) (by unfold envelopeDegree; omega))

theorem envelope_solve_calls (n wmin wmax coefficient exponent confidence : ℕ) (hwmin : 0 < wmin)
    (hw : wmax ≤ (2 * n) ^ exponent) :
    Approx.Measured.solveCallLimit n confidence wmin wmax ≤
      envelope n coefficient exponent confidence ^ 3 := by
  let E := envelope n coefficient exponent confidence
  have ht := envelope_trials n wmin wmax coefficient exponent confidence hwmin hw
  have hg := envelope_guesses n wmin wmax coefficient exponent confidence hwmin hw
  have hr := envelope_level n coefficient exponent confidence
  have hE : 2 ≤ E := by have h := envelope_large n coefficient exponent confidence; omega
  unfold Approx.Measured.solveCallLimit callLimit
  calc
    _ ≤ E * E + E := by gcongr <;> omega
    _ = E ^ 1 + E ^ 2 := by ring
    _ ≤ _ := Exact.pow_sum_bound E 1 2 hE (by omega)

theorem envelope_record_limit (n accuracy count coefficient exponent confidence : ℕ)
    (ha : accuracy ≤ coefficient * ell n) (hc : count ≤ envelope n coefficient exponent confidence) :
    recordLimit n accuracy count ≤ n * envelope n coefficient exponent confidence ^ 4 := by
  let E := envelope n coefficient exponent confidence
  have hf := envelope_records n accuracy coefficient exponent confidence ha
  have hb := envelope_block n coefficient exponent confidence
  have hE : 2 ≤ E := by have h := envelope_large n coefficient exponent confidence; omega
  unfold recordLimit
  calc
    _ ≤ E * (n + E * (n * E)) := by gcongr
    _ = n * (E ^ 1 + E ^ 3) := by ring
    _ ≤ _ := Nat.mul_le_mul_left n (Exact.pow_sum_bound E 1 3 hE (by omega))

end StreamingSSSP.Hopset.Measured
