module

public import StreamingReachability.Approx.PhysicalWordBounds

@[expose] public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace StreamingReachability.Hopset.Measured

open Parameters

theorem envelope_power (n coefficient exponent confidence i j : ℕ) (hn : 0 < n)
    (hi : i ≤ 8) (hj : j ≤ 20) :
    n ^ i * envelope n coefficient exponent confidence ^ j ≤
      n ^ 8 * envelope n coefficient exponent confidence ^ 20 := by
  have hE := envelope_large n coefficient exponent confidence
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hn hi) (Nat.pow_le_pow_right (by omega) hj)

theorem center_envelope (n accuracy coefficient exponent confidence : ℕ)
    (ha : accuracy ≤ coefficient * ell n) :
    centerDenominator n accuracy ≤ envelope n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  let L := envelopeLevel coefficient
  have hL : advance n accuracy ≤ L := advance_upper n accuracy coefficient ha
  have hs : 1 ≤ split n := split_pos n
  have hB := (envelope_base_facts coefficient exponent confidence).2.2.2.2
  have hcoeff : 100 ^ L * 4097 ^ L ≤ B := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 1 ≤ 100) (show L ≤ L + 2 by omega))
      (Nat.pow_le_pow_right (by decide : 1 ≤ 4097) (show L ≤ L + 3 by omega))
    exact h.trans ((Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2 ^ 31)).trans
      (by simpa only [Nat.mul_assoc] using hB))
  unfold centerDenominator
  calc
    _ ≤ 100 ^ L * split n ^ L := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hL)
      (Nat.pow_le_pow_right hs (by omega))
    _ ≤ 100 ^ L * (4097 * ell n) ^ L := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (split_upper n) L)
    _ = (100 ^ L * 4097 ^ L) * ell n ^ L := by rw [mul_pow]; ring
    _ ≤ B * ell n ^ L := Nat.mul_le_mul_right _ hcoeff
    _ ≤ _ := by simpa only [pow_one] using (envelope_dominates n coefficient exponent confidence 1 L
      (by omega) (by dsimp only [L]; unfold envelopeDegree; omega))

theorem groups_envelope (n coefficient exponent confidence : ℕ) :
    groups n ≤ envelope n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  have hB : 2 ^ 31 ≤ B := by
    have h := (envelope_base_facts coefficient exponent confidence).2.2.2.2
    have hp : 1 ≤ 100 ^ (envelopeLevel coefficient + 2) * 4097 ^ (envelopeLevel coefficient + 3) := by change 0 < _; positivity
    exact (Nat.mul_le_mul_left (2 ^ 31) hp).trans (by simpa only [Nat.mul_assoc] using h)
  have hk : k n ≤ B ^ 2 * ell n ^ 2 := by
    have hs : split n ≤ B * ell n := (split_upper n).trans (Nat.mul_le_mul_right _ (by
      norm_num only [Nat.reducePow] at hB
      omega))
    simpa only [k, mul_pow] using Nat.pow_le_pow_left hs 2
  have hconstant : 384 * 100 ^ 2 ≤ B := (by norm_num : 384 * 100 ^ 2 ≤ 2 ^ 31).trans hB
  unfold groups
  calc
    _ ≤ B * (B ^ 2 * ell n ^ 2) ^ 2 * ell n ^ 2 := by gcongr
    _ = B ^ 5 * ell n ^ 6 := by ring
    _ ≤ _ := envelope_dominates n coefficient exponent confidence 5 6
      (by omega) (by unfold envelopeDegree; omega)

def _root_.StreamingReachability.Hopset.Config.scalarWords (cfg : Config) (r : ℕ) : List ℕ :=
  [cfg.split, cfg.groups, cfg.shifts, cfg.logarithm, cfg.maximumLevel, cfg.earlyLevel, cfg.advance,
    cfg.initialNumerator, cfg.initialDenominator, cfg.inputScale, cfg.globalRadius, cfg.blockSize,
    cfg.copyCap, cfg.blockCap, cfg.recordCap, cfg.denominatorAt r]

theorem configuration_word_range (n accuracy delta total volume coefficient exponent confidence r : ℕ)
    (hn : 0 < n) (ha : 0 < accuracy) (hd : 0 < delta)
    (haccuracy : accuracy ≤ coefficient * ell n) (hdelta : delta ≤ (2 * n) ^ (exponent + 10))
    (htotal : total ≤ envelope n coefficient exponent confidence)
    (hvolume : volume ≤ total * blockLimit n) (hr : r ≤ maximumLevel n + 1) :
    let cfg := configuration n accuracy (blockSize n) delta volume ha hd
    ∀ value ∈ cfg.scalarWords r, value ≤ valueCapacity n coefficient exponent confidence := by
  let E := envelope n coefficient exponent confidence
  let M := n ^ 8 * E ^ 20
  let cfg := configuration n accuracy (blockSize n) delta volume ha hd
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hmono (i j : ℕ) (hi : i ≤ 8) (hj : j ≤ 20) : n ^ i * E ^ j ≤ M :=
    envelope_power n coefficient exponent confidence i j hn hi hj
  have hnM : n ≤ M := by simpa only [pow_one, pow_zero, mul_one] using hmono 1 0 (by omega) (by omega)
  have hEM : E ≤ M := by simpa only [pow_one, pow_zero, one_mul] using hmono 0 1 (by omega) (by omega)
  have hk : k n ≤ E := envelope_k n coefficient exponent confidence
  have hsplit : split n ≤ E := (Nat.le_self_pow (by decide : 2 ≠ 0) (split n)).trans hk
  have hgroups : groups n ≤ E := groups_envelope n coefficient exponent confidence
  have hlog : ell n ≤ E := (logarithm_le_k n).trans hk
  have hlevel : maximumLevel n ≤ E := (maximumLevel_le_logarithm n).trans hlog
  have hadvance : advance n accuracy ≤ E := by
    have h := advance_upper n accuracy coefficient haccuracy
    have hb := (envelope_base_facts coefficient exponent confidence).2.1
    have hlarge := (envelope_base_facts coefficient exponent confidence).1
    have hL : 40 * coefficient + 21 ≤ envelopeBase coefficient exponent confidence ^ 2 := by nlinarith
    exact h.trans (hL.trans (by simpa only [pow_zero, mul_one] using envelope_dominates n coefficient exponent confidence 2 0 (by omega) (by unfold envelopeDegree; omega)))
  have hcenter : centerDenominator n accuracy ≤ E := center_envelope n accuracy coefficient exponent confidence haccuracy
  have hU : queryUnit n accuracy (blockSize n) ≤ n ^ 2 * E := unit_polynomial n accuracy coefficient exponent confidence hn haccuracy
  have hlog3 : ell n ^ 3 ≤ E := by
    have h := envelope_dominates n coefficient exponent confidence 0 3 (by omega) (by unfold envelopeDegree; omega)
    simpa only [pow_zero, one_mul] using h
  have hinitial : initialNumerator n accuracy (blockSize n) ≤ n ^ 2 * E ^ 2 :=
    (Nat.mul_le_mul hU hlog3).trans_eq (by ring)
  have hshift : cfg.shifts ≤ n ^ 2 * E ^ 3 := by
    have h := Nat.div_le_self (initialNumerator n accuracy (blockSize n) + centerDenominator n accuracy - 1)
      (centerDenominator n accuracy)
    change ceilDiv _ _ ≤ _
    unfold ceilDiv
    have hN : 1 ≤ n ^ 2 := by change 0 < _; positivity
    have hcp : E ≤ n ^ 2 * E ^ 2 := by
      have he : E ≤ E ^ 2 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ E) (by omega : 1 ≤ 2)
      exact he.trans (Nat.le_mul_of_pos_left _ hN)
    calc
      _ ≤ 2 * (n ^ 2 * E ^ 2) := by omega
      _ ≤ E * (n ^ 2 * E ^ 2) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hcopy : copyLimit n ≤ M := (envelope_copy n coefficient exponent confidence).trans
    (by simpa only [pow_one] using hmono 1 1 (by omega) (by omega))
  have hblock : blockLimit n ≤ M := (envelope_block n coefficient exponent confidence).trans
    (by simpa only [pow_one] using hmono 1 1 (by omega) (by omega))
  have hrecord : cfg.recordCap ≤ M :=
    ((Nat.mul_le_mul_left (recordFactor n accuracy) (Nat.add_le_add_left hvolume n)).trans
      (envelope_record_limit n accuracy total coefficient exponent confidence haccuracy htotal)).trans
        (by simpa only [pow_one] using hmono 1 4 (by omega) (by omega))
  have h100 : 100 ^ r ≤ 100 * n := by
    have hheight : 100 ^ maximumLevel n ≤ n :=
      (Nat.pow_le_pow_left (by have h := k_large n; omega : 100 ≤ k n) _).trans (power_maximumLevel_le n hn)
    exact (Nat.pow_le_pow_right (by decide) hr).trans (by rw [pow_succ]; nlinarith)
  have hsplitPower : split n ^ r ≤ E * n := by
    have h := (Nat.pow_le_pow_left (Nat.le_self_pow (by decide : 2 ≠ 0) (split n)) (maximumLevel n)).trans
      (power_maximumLevel_le n hn)
    exact (Nat.pow_le_pow_right (split_pos n) hr).trans (by rw [pow_succ]; exact (Nat.mul_le_mul h hsplit).trans_eq (Nat.mul_comm _ _))
  have h4 : 4 ^ r ≤ 4 * n := by
    have hheight : 4 ^ maximumLevel n ≤ n :=
      (Nat.pow_le_pow_left (by have h := k_large n; omega : 4 ≤ k n) _).trans (power_maximumLevel_le n hn)
    exact (Nat.pow_le_pow_right (by decide) hr).trans (by rw [pow_succ]; nlinarith)
  have hden : cfg.denominatorAt r ≤ n ^ 3 * E ^ 3 := by
    have hmin : (100 * split n) ^ min r (threshold n (blockSize n)) ≤ 100 ^ r * split n ^ r := by
      rw [mul_pow]
      exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (Nat.min_le_left _ _))
        (Nat.pow_le_pow_right (split_pos n) (Nat.min_le_left _ _))
    have hlast : 4 ^ (r - threshold n (blockSize n)) ≤ 4 ^ r := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    change centerDenominator n accuracy * _ * _ ≤ _
    calc
      _ ≤ E * (100 ^ r * split n ^ r) * 4 ^ r := Nat.mul_le_mul (Nat.mul_le_mul hcenter hmin) hlast
      _ ≤ E * (100 * n * (E * n)) * (4 * n) := by gcongr
      _ = 400 * n ^ 3 * E ^ 2 := by ring
      _ ≤ E * n ^ 3 * E ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega : 400 ≤ E))
      _ = _ := by ring
  have hMcap : M ≤ valueCapacity n coefficient exponent confidence := capacity_monomial n coefficient exponent confidence 8 20 hn (by omega) (by omega)
  have hdeltaCap : delta ≤ valueCapacity n coefficient exponent confidence := by
    have he : 1 ≤ E ^ 100 := by change 0 < _; positivity
    exact hdelta.trans ((Nat.pow_le_pow_right (by omega : 1 ≤ 2 * n) (by omega : exponent + 10 ≤ exponent + 100)).trans (Nat.le_mul_of_pos_right _ he))
  have hglobal : cfg.globalRadius ≤ M := by
    have h := Nat.mul_le_mul_left 8 hU
    exact h.trans ((Nat.mul_le_mul_right (n ^ 2 * E) (by omega : 8 ≤ E)).trans
      ((by ring : E * (n ^ 2 * E) = n ^ 2 * E ^ 2).le.trans (hmono 2 2 (by omega) (by omega))))
  have hshiftM := hshift.trans (hmono 2 3 (by omega) (by omega))
  have hinitialM := hinitial.trans (hmono 2 2 (by omega) (by omega))
  have hdenM := hden.trans (hmono 3 3 (by omega) (by omega))
  change ∀ value ∈ cfg.scalarWords r, value ≤ _
  intro value hv
  simp only [Config.scalarWords, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hsplit.trans hEM).trans hMcap
  · exact (hgroups.trans hEM).trans hMcap
  · exact hshiftM.trans hMcap
  · exact (hlog.trans hEM).trans hMcap
  · exact (hlevel.trans hEM).trans hMcap
  · exact ((threshold_le_maximum n (blockSize n)).trans (hlevel.trans hEM)).trans hMcap
  · exact (hadvance.trans hEM).trans hMcap
  · exact hinitialM.trans hMcap
  · exact (hcenter.trans hEM).trans hMcap
  · exact hdeltaCap
  · exact hglobal.trans hMcap
  · exact ((blockSize_le_n n hn).trans hnM).trans hMcap
  · exact hcopy.trans hMcap
  · exact hblock.trans hMcap
  · exact hrecord.trans hMcap
  · exact hdenM.trans hMcap

end StreamingReachability.Hopset.Measured
