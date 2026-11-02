module

public import StreamingSSSP.Hopset.Backend
public import StreamingSSSP.Hopset.ProtocolQueries
public import StreamingSSSP.Hopset.Scaling
public import StreamingSSSP.Late.Protocol

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

theorem bounded_fraction_clip (d : Distance) (num den : ℕ) (hd : 0 < den)
    (radius : ℝ) (hr : radius ≤ (num : ℝ) / den) :
    Early.Bounded (Late.clippedDistance d (num / den)) radius ↔ Early.Bounded d radius := by
  by_cases h : d ≤ ((num / den : ℕ) : Distance)
  · simp [Late.clippedDistance, h]
  · simp only [Late.clippedDistance, ite_eq_right h]
    constructor
    · rintro ⟨q, hq, _⟩
      simp at hq
    · intro hb
      apply False.elim
      have hcap := Early.bounded_mono_radius hb hr
      have hbool := (Late.withinFraction_iff_bounded d num den hd).mpr hcap
      have hle : d ≤ ((num / den : ℕ) : Distance) := by
        simpa only [withinFraction, decide_eq_true_eq] using hbool
      exact h hle

theorem accurate_fraction_clip {n : ℕ} (H : Graph (Fin n)) (S : Finset (Fin n))
    (p : Fin n) (reply : Core.BatchAPI.SparseReply n) (forward backward num den : ℕ)
    (hd : 0 < den)
    (hf : ∀ v ∈ S, lookup reply forward v = Late.clippedDistance (H.dist p v) (num / den))
    (hb : ∀ v ∈ S, lookup reply backward v = Late.clippedDistance (H.dist v p) (num / den)) :
    Late.AccurateBalls H S p reply forward backward ((num : ℝ) / den) := by
  intro v hv radius hr
  rw [hf v hv, hb v hv]
  exact ⟨bounded_fraction_clip _ num den hd radius hr,
    bounded_fraction_clip _ num den hd radius hr⟩

theorem searchRadius_real (cfg : Config) (r : ℕ) :
    Early.searchRadius cfg.k cfg.groups ((cfg.initialNumerator : ℝ) / cfg.denominatorAt r) =
      (((cfg.etaMax * cfg.initialNumerator : ℕ) : ℝ) / cfg.denominatorAt r) := by
  simp only [Early.searchRadius, Early.lambda, Config.etaMax, Config.lambda, Config.width,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem raw_query_pair_fraction {n nb ns nq : ℕ} (c : Core.Shared.Catalog n nb ns nq)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hn : 0 < n) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hp : ∀ e ∈ input, 0 < e.weight) (hblocks : c.blocks.toList = stored.blocks)
    (hA : 0 < c.scale) (workspace : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ workspace)
    (i : Fin ns) (p : Fin n)
    (forward backward : Fin nq) (num den : ℕ) (hd : 0 < den)
    (hf : c.searches.get forward = ⟨i, p, false, num / den⟩)
    (hb : c.searches.get backward = ⟨i, p, true, num / den⟩) :
    Late.AccurateBalls (Backend.roundedRestricted stored input (c.sets.get i) c.scale)
      (c.sets.get i) p
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit c workspace) input).records
      forward.val backward.val ((num : ℝ) / den) := by
  apply accurate_fraction_clip _ _ _ _ _ _ num den hd
  · intro v _
    have h := Backend.raw_lookup c stored input hn hs hp hblocks hA workspace hx forward v
    simpa only [Core.Shared.vertices, hf, Bool.false_eq_true, ↓reduceIte,
      Late.clippedDistance] using h
  · intro v _
    have h := Backend.raw_lookup c stored input hn hs hp hblocks hA workspace hx backward v
    simpa only [Core.Shared.vertices, hb, ↓reduceIte, Graph.dist_reverse,
      Late.clippedDistance] using h

end StreamingSSSP.Hopset
