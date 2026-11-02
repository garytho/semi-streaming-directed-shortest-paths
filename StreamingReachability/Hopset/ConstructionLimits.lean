module

public import StreamingReachability.Hopset.BuilderResourceCertificate
public import StreamingReachability.Hopset.BuilderValidity

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ}

def copyLimit (n : ℕ) : ℕ := 2 ^ 30 * n * Parameters.ell n ^ 4
def blockLimit (n : ℕ) : ℕ := 2 ^ 30 * n * Parameters.k n * Parameters.ell n ^ 4
def recordFactor (n accuracy : ℕ) : ℕ :=
  2 ^ 30 * Parameters.k n ^ (Parameters.advance n accuracy + 2) * Parameters.ell n ^ 4
def headerLimit (n : ℕ) : ℕ := 2 * (Parameters.maximumLevel n + 1) * copyLimit n
def drawLimit (n accuracy x : ℕ) : ℕ :=
  n * Parameters.threshold n x + 5 * copyLimit n * (Parameters.maximumLevel n + 1)
def callLimit (n : ℕ) : ℕ := Parameters.maximumLevel n + 2
def randomLimit (n accuracy x : ℕ) : ℕ :=
  n + Parameters.groups n + Parameters.ceilDiv (Parameters.initialNumerator n accuracy x)
    (Parameters.centerDenominator n accuracy)

def recordLimit (n accuracy total : ℕ) : ℕ :=
  recordFactor n accuracy * (n + total * blockLimit n)

def storeCatalogLimit (n accuracy total : ℕ) : ℕ :=
  4 * (total * headerLimit n + 7 * copyLimit n + 1) +
    3 * (total * recordLimit n accuracy total) + 2 * (total * blockLimit n) + 2 * copyLimit n

structure StoreBounds (G : Graph (Fin n)) (accuracy x total weight count : ℕ)
    (stored : Implicit.Representation n) : Prop where
  valid : StoredValid G x stored
  volume_le : volume stored.blocks ≤ count * blockLimit n
  headers_le : stored.blocks.length ≤ count * headerLimit n
  stars_le : stored.explicit.length ≤ count * recordLimit n accuracy total
  weights : ∀ e ∈ stored.explicit, e.weight ≤ weight

theorem StoreBounds.enlarge {G : Graph (Fin n)} {accuracy x total weight count larger : ℕ}
    {stored : Implicit.Representation n} (h : StoreBounds G accuracy x total weight count stored)
    (hc : count ≤ larger) : StoreBounds G accuracy x total weight larger stored :=
  ⟨h.valid, h.volume_le.trans (Nat.mul_le_mul_right _ hc),
    h.headers_le.trans (Nat.mul_le_mul_right _ hc), h.stars_le.trans (Nat.mul_le_mul_right _ hc), h.weights⟩

theorem StoreBounds.catalog {G : Graph (Fin n)} {accuracy x total weight count : ℕ}
    {stored : Implicit.Representation n} (h : StoreBounds G accuracy x total weight count stored)
    (hc : count ≤ total) :
    catalogLimit stored (copyLimit n) ≤ storeCatalogLimit n accuracy total := by
  have hv := h.volume_le.trans (Nat.mul_le_mul_right _ hc)
  have hh := h.headers_le.trans (Nat.mul_le_mul_right _ hc)
  have hs := h.stars_le.trans (Nat.mul_le_mul_right _ hc)
  unfold catalogLimit storeCatalogLimit
  omega

theorem StoreBounds.commit {G : Graph (Fin n)} {accuracy x total weight count : ℕ}
    {stored : Implicit.Representation n} (h : StoreBounds G accuracy x total weight count stored)
    (out : Output n) (hsound : out.Sound G)
    (hvolume : volume out.blocks ≤ blockLimit n) (hheaders : out.blocks.length ≤ headerLimit n)
    (hstars : out.explicit.length ≤ recordLimit n accuracy total)
    (hsize : ∀ B ∈ out.blocks, B.card ≤ x) (hw : OutputWords weight out) :
    StoreBounds G accuracy x total weight (count + 1) (commit stored out) := by
  refine ⟨h.valid.commit out hsound hsize, ?_, ?_, ?_, ?_⟩
  · change volume (stored.blocks ++ out.blocks) ≤ _
    rw [volume_append]
    have hv := h.volume_le
    nlinarith
  · change (stored.blocks ++ out.blocks).length ≤ _
    rw [List.length_append]
    have hh := h.headers_le
    nlinarith
  · change (stored.explicit ++ out.explicit).length ≤ _
    rw [List.length_append]
    have hs := h.stars_le
    nlinarith
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.weights e he
    · exact hw e he

theorem store_calls_fit {G : Graph (Fin n)} (accuracy x delta total weight count : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (h : StoreBounds G accuracy x total weight count stored) (hc : count ≤ total) (scale : ℕ) (hscale : delta ≤ scale) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    CallsFit cfg stored (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
      (storeCatalogLimit n accuracy total) scale weight) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  change CallsFit cfg stored _
  intro r m sets targets allowance hsets hvolume htargets hallowance
  have hq := catalog_query_bounds cfg r stored sets targets allowance scale weight h.valid.positive
    h.weights h.valid.blocks hscale
    ((Parameters.searchRadius_le_queryUnit n accuracy x delta (volume stored.blocks) ha hd r).trans
      (by change Parameters.queryUnit n accuracy x ≤ 8 * Parameters.queryUnit n accuracy x; omega))
    hallowance hsets hvolume htargets
  have hv : volume stored.blocks ≤ total * blockLimit n :=
    h.volume_le.trans (Nat.mul_le_mul_right _ hc)
  have hr : cfg.recordCap ≤ recordLimit n accuracy total := by
    change recordFactor n accuracy * (n + volume stored.blocks) ≤ recordFactor n accuracy * (n + total * blockLimit n)
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hv n)
  exact ⟨hq.workspace, hq.radius_le, hq.allowance_le.trans hr, hq.catalog_le.trans (h.catalog hc),
    hq.scale_pos, hq.scale_le, hq.explicit_positive, hq.explicit_weights, hq.blocks⟩

end StreamingReachability.Hopset.Measured
