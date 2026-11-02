module

public import StreamingSSSP.Hopset.ResourceEnvelope

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingSSSP.Hopset.Measured

open Parameters

theorem envelope_catalog (n accuracy count coefficient exponent confidence : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) (hc : count ≤ envelope n coefficient exponent confidence) :
    storeCatalogLimit n accuracy count ≤ n * envelope n coefficient exponent confidence ^ 6 := by
  let E := envelope n coefficient exponent confidence
  let F := n * E ^ 5
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hcopy := envelope_copy n coefficient exponent confidence
  have hblock := envelope_block n coefficient exponent confidence
  have hheader := envelope_headers n coefficient exponent confidence
  have hrecord := envelope_record_limit n accuracy count coefficient exponent confidence ha hc
  have hp1 : E ≤ E ^ 5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ E) (by omega : 1 ≤ 5)
  have hp2 : E ^ 2 ≤ E ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp4 : E ^ 4 ≤ E ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hh : count * headerLimit n ≤ F := by
    calc
      _ ≤ E * (n * E ^ 3) := Nat.mul_le_mul hc hheader
      _ = n * E ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left n hp4
  have hr : count * recordLimit n accuracy count ≤ F := by
    calc
      _ ≤ E * (n * E ^ 4) := Nat.mul_le_mul hc hrecord
      _ = _ := by ring
  have hb : count * blockLimit n ≤ F := by
    calc
      _ ≤ E * (n * E) := Nat.mul_le_mul hc hblock
      _ = n * E ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left n hp2
  have hcp : copyLimit n ≤ F := hcopy.trans (Nat.mul_le_mul_left n hp1)
  have hF : 1 ≤ F := by change 0 < F; dsimp only [F]; positivity
  unfold storeCatalogLimit
  calc
    _ ≤ 43 * F := by omega
    _ ≤ E * F := Nat.mul_le_mul_right F (by omega)
    _ = _ := by dsimp only [F]; ring

theorem envelope_memory (n accuracy count coefficient exponent confidence : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) (hc : count ≤ envelope n coefficient exponent confidence) :
    memoryLimit n (recordLimit n accuracy count) (storeCatalogLimit n accuracy count) ≤
      n * envelope n coefficient exponent confidence ^ 7 := by
  let E := envelope n coefficient exponent confidence
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hr := envelope_record_limit n accuracy count coefficient exponent confidence ha hc
  have hcatal := envelope_catalog n accuracy count coefficient exponent confidence hn ha hc
  change recordLimit n accuracy count ≤ n * E ^ 4 at hr
  change storeCatalogLimit n accuracy count ≤ n * E ^ 6 at hcatal
  have hp : E ^ 4 ≤ E ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hR : recordLimit n accuracy count ≤ n * E ^ 6 := hr.trans (Nat.mul_le_mul_left n hp)
  have hN : n ≤ n * E ^ 6 := Nat.le_mul_of_pos_right _ (by positivity)
  have hOne : 1 ≤ n * E ^ 6 := by change 0 < _; positivity
  unfold memoryLimit
  calc
    _ ≤ 772 * (n * E ^ 6) := by omega
    _ ≤ E * (n * E ^ 6) := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

theorem envelope_unit (n accuracy coefficient exponent confidence : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) :
    queryUnit n accuracy (blockSize n) ≤
      blockSize n * 100 ^ maximumLevel n * envelope n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  let L := envelopeLevel coefficient
  have hB : 1024 ≤ B := (envelope_base_facts coefficient exponent confidence).1
  have hcoeff : 20 * coefficient ≤ B := (envelope_base_facts coefficient exponent confidence).2.1
  have hconst : 2 ^ 31 * 100 ^ (L + 2) * 4097 ^ (L + 3) ≤ B :=
    (envelope_base_facts coefficient exponent confidence).2.2.2.2
  have hconst' : 2 ^ 31 * 100 ^ (40 * coefficient + 23) * 4097 ^ (40 * coefficient + 24) ≤ B := by
    simpa only [L, envelopeLevel, Nat.add_assoc] using hconst
  have hh : hopBound n accuracy (blockSize n) ≤ B * blockSize n * ell n ^ (L + 3) * 100 ^ maximumLevel n :=
    (cube_hop_upper n accuracy coefficient hn ha).trans (by
      have h := Nat.mul_le_mul_right (100 ^ maximumLevel n)
        (Nat.mul_le_mul_right (ell n ^ (40 * coefficient + 24))
          (Nat.mul_le_mul_right (blockSize n) hconst'))
      simpa only [L, envelopeLevel, Nat.add_assoc] using h)
  have hd : accuracyDenominator n accuracy ≤ B * ell n ^ 2 := by
    calc
      _ ≤ 20 * (coefficient * ell n) * ell n := by unfold accuracyDenominator; gcongr
      _ = (20 * coefficient) * ell n ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ hcoeff
  have hp : B ^ 3 * ell n ^ (L + 5) ≤ envelope n coefficient exponent confidence :=
    envelope_dominates n coefficient exponent confidence 3 (L + 5) (by omega)
      (by dsimp only [L]; unfold envelopeDegree; omega)
  unfold queryUnit
  calc
    _ ≤ B * (B * blockSize n * ell n ^ (L + 3) * 100 ^ maximumLevel n) * (B * ell n ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (le_trans (by norm_num : 8 ≤ 1024) hB) hh) hd
    _ = (blockSize n * 100 ^ maximumLevel n) * (B ^ 3 * ell n ^ (L + 5)) := by
      rw [show L + 5 = (L + 3) + 2 by omega, pow_add]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ hp

theorem envelope_pass (n accuracy count coefficient exponent confidence : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) (hc : count ≤ envelope n coefficient exponent confidence) :
    passLimit n (blockSize n) (8 * queryUnit n accuracy (blockSize n)) (recordLimit n accuracy count) ≤
      blockSize n * 100 ^ maximumLevel n * envelope n coefficient exponent confidence ^ 6 := by
  let E := envelope n coefficient exponent confidence
  let S := blockSize n * 100 ^ maximumLevel n
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hS : 1 ≤ S := by change 0 < S; dsimp only [S]; have h := blockSize_pos n; positivity
  have hU := envelope_unit n accuracy coefficient exponent confidence hn ha
  change queryUnit n accuracy (blockSize n) ≤ S * E at hU
  have hr := envelope_record_limit n accuracy count coefficient exponent confidence ha hc
  have hlog : Nat.log 2 (blockSize n) + 3 ≤ E := by
    have hm := Nat.log_mono_right (b := 2) (blockSize_le_n n hn)
    simp only [← Nat.log2_eq_log_two] at hm
    rw [← Nat.log2_eq_log_two]
    have he := envelope_logarithm n coefficient exponent confidence
    have hp := ell_pos n
    unfold ell at *
    omega
  have hrad : 8 * queryUnit n accuracy (blockSize n) + 1 ≤ S * E ^ 2 := by
    have hone : 1 ≤ S * E := by change 0 < _; positivity
    have h8 : 9 * (S * E) ≤ E * (S * E) := Nat.mul_le_mul_right _ (by omega)
    have h1 : 8 * queryUnit n accuracy (blockSize n) + 1 ≤ 9 * (S * E) := by omega
    exact (h1.trans h8).trans_eq (by ring)
  have hfirst : (8 * queryUnit n accuracy (blockSize n) + 1) * (Nat.log 2 (blockSize n) + 3) ≤ S * E ^ 3 := by
    exact (Nat.mul_le_mul hrad hlog).trans_eq (by ring)
  have hdiv : 32 * blockSize n * recordLimit n accuracy count / n ≤ S * E ^ 5 := by
    calc
      _ ≤ (32 * blockSize n * (n * E ^ 4)) / n :=
        Nat.div_le_div_right (Nat.mul_le_mul_left _ hr)
      _ = 32 * blockSize n * E ^ 4 := by
        rw [show 32 * blockSize n * (n * E ^ 4) = (32 * blockSize n * E ^ 4) * n by ring,
          Nat.mul_div_cancel _ hn]
      _ ≤ E * S * E ^ 4 := by
        gcongr
        · omega
        · exact Nat.le_mul_of_pos_right _ (by positivity)
      _ = S * E ^ 5 := by ring
  unfold passLimit
  exact (Nat.add_le_add hfirst hdiv).trans (by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left S (Exact.pow_sum_bound E 3 5 (by omega) (by omega)))

theorem envelope_solve_passes (n accuracy wmin wmax coefficient exponent confidence : ℕ) (hn : 0 < n)
    (ha : accuracy ≤ coefficient * ell n) (hwmin : 0 < wmin) (hw : wmax ≤ (2 * n) ^ exponent) :
    1 + Approx.Measured.solveCallLimit n confidence wmin wmax *
      passLimit n (blockSize n) (8 * queryUnit n accuracy (blockSize n))
        (recordLimit n accuracy (executionCount n confidence wmin wmax)) ≤
      blockSize n * 100 ^ maximumLevel n * envelope n coefficient exponent confidence ^ 10 := by
  let E := envelope n coefficient exponent confidence
  let S := blockSize n * 100 ^ maximumLevel n
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hS : 1 ≤ S := by change 0 < S; dsimp only [S]; have h := blockSize_pos n; positivity
  have hc := envelope_solve_calls n wmin wmax coefficient exponent confidence hwmin hw
  have ht := envelope_trials n wmin wmax coefficient exponent confidence hwmin hw
  have hp := envelope_pass n accuracy _ coefficient exponent confidence hn ha ht
  calc
    _ ≤ S * 1 + E ^ 3 * (S * E ^ 6) := Nat.add_le_add (by omega) (Nat.mul_le_mul hc hp)
    _ = S * (E ^ 0 + E ^ 9) := by ring
    _ ≤ _ := Nat.mul_le_mul_left S (Exact.pow_sum_bound E 0 9 (by omega) (by omega))

theorem envelope_draws (n accuracy x coefficient exponent confidence : ℕ) :
    drawLimit n accuracy x ≤ n * envelope n coefficient exponent confidence ^ 4 := by
  let E := envelope n coefficient exponent confidence
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hr := envelope_level n coefficient exponent confidence
  change maximumLevel n + 2 ≤ E at hr
  have hc := envelope_copy n coefficient exponent confidence
  change copyLimit n ≤ n * E at hc
  have ht : threshold n x ≤ E := (threshold_le_maximum n x).trans (by omega)
  have hfirst : n * threshold n x ≤ n * E := Nat.mul_le_mul_left n ht
  have hlast : 5 * copyLimit n * (maximumLevel n + 1) ≤ n * E ^ 3 := by
    calc
      _ ≤ E * (n * E) * E := by gcongr <;> omega
      _ = _ := by ring
  unfold drawLimit
  exact (Nat.add_le_add hfirst hlast).trans (by
    rw [show n * E + n * E ^ 3 = n * (E ^ 1 + E ^ 3) by ring]
    exact Nat.mul_le_mul_left n (Exact.pow_sum_bound E 1 3 (by omega) (by omega)))

end StreamingSSSP.Hopset.Measured
