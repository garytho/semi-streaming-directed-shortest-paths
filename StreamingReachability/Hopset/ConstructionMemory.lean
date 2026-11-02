module

public import StreamingReachability.Hopset.LevelsSpace
public import StreamingReachability.Hopset.EnvelopeCosts

@[expose] public section

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace StreamingReachability.Hopset.Measured

open Parameters

variable {n : ℕ}

theorem envelope_k (n coefficient exponent confidence : ℕ) :
    k n ≤ envelope n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  have hb : 4097 ≤ B := by
    have h := (envelope_base_facts coefficient exponent confidence).2.2.2.1
    have hp : 4097 ^ 1 ≤ 4097 ^ (envelopeLevel coefficient + 3) :=
      Nat.pow_le_pow_right (by decide) (by unfold envelopeLevel; omega)
    simpa only [pow_one] using hp.trans h
  have hs : split n ≤ B * ell n := (split_upper n).trans (Nat.mul_le_mul_right _ hb)
  have hk : k n ≤ B ^ 2 * ell n ^ 2 := by simpa only [k, mul_pow] using Nat.pow_le_pow_left hs 2
  exact hk.trans (envelope_dominates n coefficient exponent confidence 2 2
    (by omega) (by unfold envelopeDegree; omega))

theorem store_memory {G : Graph (Fin n)} {accuracy x total weight count coefficient exponent confidence : ℕ}
    {stored : Implicit.Representation n} (h : StoreBounds G accuracy x total weight count stored)
    (hn : 0 < n) (ha : accuracy ≤ coefficient * ell n) (hc : count ≤ total)
    (ht : total ≤ envelope n coefficient exponent confidence) :
    storedCells stored ≤ n * envelope n coefficient exponent confidence ^ 6 := by
  let E := envelope n coefficient exponent confidence
  let F := n * E ^ 5
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hs := h.stars_le.trans (Nat.mul_le_mul_right _ hc)
  have hh := h.headers_le.trans (Nat.mul_le_mul_right _ hc)
  have hv := h.volume_le.trans (Nat.mul_le_mul_right _ hc)
  have hr := envelope_record_limit n accuracy total coefficient exponent confidence ha ht
  have hb := envelope_block n coefficient exponent confidence
  have hheader := envelope_headers n coefficient exponent confidence
  have hstar : stored.explicit.length ≤ F :=
    hs.trans ((Nat.mul_le_mul ht hr).trans_eq (by ring))
  have hhead : stored.blocks.length ≤ F := by
    calc
      _ ≤ total * headerLimit n := hh
      _ ≤ E * (n * E ^ 3) := Nat.mul_le_mul ht hheader
      _ = n * E ^ 4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by omega) (by omega))
  have hvol : volume stored.blocks ≤ F := by
    calc
      _ ≤ total * blockLimit n := hv
      _ ≤ E * (n * E) := Nat.mul_le_mul ht hb
      _ = n * E ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by omega) (by omega))
  unfold storedCells
  calc
    _ ≤ 10 * F := by omega
    _ ≤ E * F := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by dsimp only [F]; ring

theorem calibrated_controller_memory {G : Graph (Fin n)}
    (accuracy x delta total weight count coefficient exponent confidence : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (h : StoreBounds G accuracy x total weight count stored) (hn : 0 < n)
    (haccuracy : accuracy ≤ coefficient * ell n) (hc : count ≤ total)
    (ht : total ≤ envelope n coefficient exponent confidence) :
    let cfg := configuration n accuracy x delta (volume stored.blocks) ha hd
    controllerCells n cfg stored (headerLimit n) ≤ n * envelope n coefficient exponent confidence ^ 8 := by
  let E := envelope n coefficient exponent confidence
  let F := n * E ^ 6
  let cfg := configuration n accuracy x delta (volume stored.blocks) ha hd
  have hE : 1024 ≤ E := envelope_large n coefficient exponent confidence
  have hstored := store_memory h hn haccuracy hc ht
  change storedCells stored ≤ F at hstored
  have hcopy := envelope_copy n coefficient exponent confidence
  have hblock := envelope_block n coefficient exponent confidence
  have hheader := envelope_headers n coefficient exponent confidence
  have hvol : volume stored.blocks ≤ total * blockLimit n :=
    h.volume_le.trans (Nat.mul_le_mul_right _ hc)
  have hrecord : cfg.recordCap ≤ n * E ^ 4 :=
    (Nat.mul_le_mul_left (recordFactor n accuracy) (Nat.add_le_add_left hvol n)).trans
      (envelope_record_limit n accuracy total coefficient exponent confidence haccuracy ht)
  have hp1 : n * E ≤ F := Nat.mul_le_mul_left n (by simpa only [pow_one] using
    (Nat.pow_le_pow_right (by omega : 1 ≤ E) (by omega : 1 ≤ 6)))
  have hp3 : n * E ^ 3 ≤ F := Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by omega) (by omega))
  have hp4 : n * E ^ 4 ≤ F := Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by omega) (by omega))
  have hcp : cfg.copyCap ≤ F := hcopy.trans hp1
  have hbp : cfg.blockCap ≤ F := hblock.trans hp1
  have hhp : headerLimit n ≤ F := hheader.trans hp3
  have hrp : cfg.recordCap ≤ F := hrecord.trans hp4
  have hk : cfg.k ≤ E := envelope_k n coefficient exponent confidence
  have hnF : n ≤ F := Nat.le_mul_of_pos_right _ (by positivity)
  have hF : 1 ≤ F := by change 0 < F; dsimp only [F]; positivity
  have hselector : selectorCells n cfg ≤ 52 * F := by
    unfold selectorCells Config.width
    have hm := Nat.mul_le_mul_left n hk
    nlinarith
  change controllerCells n cfg stored (headerLimit n) ≤ _
  unfold controllerCells
  calc
    _ ≤ 1170 * F := by omega
    _ ≤ E ^ 2 * F := Nat.mul_le_mul_right F (by nlinarith)
    _ = _ := by dsimp only [F]; ring

end StreamingReachability.Hopset.Measured
