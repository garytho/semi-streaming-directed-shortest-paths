module

public import StreamingSSSP.Hopset.StarRoutes
public import StreamingSSSP.Hopset.StarTargets

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem shortcut_metric_budget (H : Graph (Fin n)) (y p z : Fin n) (radius : ℝ) (W : ℕ) (B : ℝ)
    (hin : Early.Within H y p radius) (hout : Early.Within H p z radius)
    (hstar : Early.StarShortcut (Early.starGraph H p radius) y p z ((W : ℝ) + B)) :
    Early.Bounded (H.dist y p + H.dist p z) ((W : ℝ) + B) := by
  obtain ⟨a, b, ha, hb, hab⟩ := hstar
  rw [Early.starGraph_in H p y radius hin] at ha
  rw [Early.starGraph_out H p z radius hout] at hb
  refine ⟨a + b, ?_, ?_⟩
  · rw [ha, hb]
    rfl
  · simpa only [Nat.cast_add] using hab

theorem raw_advance_bridge (cfg : Config) (q r : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target) (hk : target.kind = .advanceStar)
    (Hchild : Graph (Fin n))
    (outer : Early.ShortPath (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
      (Reference.distanceScale cfg q))
    (inner : Early.ShortPath Hchild (Reference.distanceScale cfg r))
    (hnested : inner.vertices.IsInfix outer.vertices) (y z : Fin n)
    (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist u v ≤ Hchild.dist u v)
    (hbridge : Early.Bridge inner target.vertex (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)))
    (hscale : Reference.distanceScale cfg r ≤ Reference.distanceScale cfg q / 2)
    (F : Graph (Fin n))
    (hF : ∀ e ∈ emittedStars cfg targets
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg q stored.blocks sets targets) cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance)) :
    ∃ debt : ℕ, (debt : ℝ) ≤ 3 * cfg.etaMax * Reference.distanceScale cfg r ∧
      ∃ T : Late.Route F y z (cfg.inputScale * (outer.cost + debt)), T.hops ≤ 2 := by
  let H := Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale
  have heta : (2 : ℝ) ≤ cfg.etaMax := by
    have h : 2 ≤ cfg.etaMax := by unfold Config.etaMax; omega
    exact_mod_cast h
  have hb : Early.Bridge inner target.vertex ((cfg.etaMax : ℝ) * Reference.distanceScale cfg r) := by
    simpa only [searchRadius_eta] using hbridge
  have h := Early.nested_advance_star_of_infix H Hchild outer inner hnested hends hmono hb hscale heta
  have hleft : H.dist y target.vertex ≤ (cfg.searchRadius q : Distance) :=
    (within_search_iff cfg q H y target.vertex).mp (by simpa only [searchRadius_eta] using h.1)
  have hright : H.dist target.vertex z ≤ (cfg.searchRadius q : Distance) :=
    (within_search_iff cfg q H target.vertex z).mp (by simpa only [searchRadius_eta] using h.2.1)
  have hin : Early.Within H y target.vertex (targetRadius cfg q target.kind : ℝ) := by
    rw [hk]
    exact (bounded_integer_iff _ _).mpr hleft
  have hout : Early.Within H target.vertex z (targetRadius cfg q target.kind : ℝ) := by
    rw [hk]
    exact (bounded_integer_iff _ _).mpr hright
  have hbudget := shortcut_metric_budget H y target.vertex z
    ((cfg.etaMax : ℝ) * Reference.distanceScale cfg q) outer.cost
    (3 * cfg.etaMax * Reference.distanceScale cfg r) h.1 h.2.1 h.2.2
  have hD := inner.scale_nonneg
  exact raw_two_star_route cfg q stored input hn hs hp hsize sets targets index target ht
    (by simpa only [hk] using (show TargetKind.advanceStar ≠ .pivot by decide))
    y z outer.cost _ (by positivity) hin hout hbudget F hF

theorem raw_global_bridge (cfg : Config) (r Delta : ℕ) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (index : ℕ) (target : Target n ns) (ht : targets[index]? = some target) (hk : target.kind = .globalStar)
    (hradius : cfg.globalRadius = 8 * Delta) (Hchild : Graph (Fin n))
    (outer : Early.ShortPath (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale)
      (3 * (Delta : ℝ))) (inner : Early.ShortPath Hchild (Reference.distanceScale cfg r))
    (hnested : inner.vertices.IsInfix outer.vertices) (y z : Fin n)
    (hends : Graph.Endpoints outer.vertices y z)
    (hmono : ∀ u v, (Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale).dist u v ≤ Hchild.dist u v)
    (hbridge : Early.Bridge inner target.vertex (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)))
    (hsearch : (cfg.etaMax : ℝ) * Reference.distanceScale cfg r ≤ 5 * Delta)
    (F : Graph (Fin n))
    (hF : ∀ e ∈ emittedStars cfg targets
      (Core.BatchAPI.run (Core.BatchAPI.Request.ofCatalog stored.explicit
        (catalog cfg 0 stored.blocks sets targets) cfg.blockSize) input).records,
        F e.source e.target ≤ (e.weight : Distance)) :
    ∃ debt : ℕ, (debt : ℝ) ≤ 3 * cfg.etaMax * Reference.distanceScale cfg r ∧
      ∃ T : Late.Route F y z (cfg.inputScale * (outer.cost + debt)), T.hops ≤ 2 := by
  let H := Backend.roundedRestricted stored input (sets.get target.setId) cfg.inputScale
  have heta : (2 : ℝ) ≤ cfg.etaMax := by
    have h : 2 ≤ cfg.etaMax := by unfold Config.etaMax; omega
    exact_mod_cast h
  have hb : Early.Bridge inner target.vertex ((cfg.etaMax : ℝ) * Reference.distanceScale cfg r) := by
    simpa only [searchRadius_eta] using hbridge
  have h := Early.global_advance_star_from_initial_scale H Hchild outer inner hnested hends hmono hb
    le_rfl hsearch heta
  have hin : Early.Within H y target.vertex (targetRadius cfg 0 target.kind : ℝ) := by
    simpa only [hk, targetRadius, hradius, Nat.cast_mul, Nat.cast_ofNat] using h.1
  have hout : Early.Within H target.vertex z (targetRadius cfg 0 target.kind : ℝ) := by
    simpa only [hk, targetRadius, hradius, Nat.cast_mul, Nat.cast_ofNat] using h.2.1
  have hbudget := shortcut_metric_budget H y target.vertex z (8 * (Delta : ℝ)) outer.cost
    (3 * cfg.etaMax * Reference.distanceScale cfg r) h.1 h.2.1 h.2.2
  have hD := inner.scale_nonneg
  exact raw_two_star_route cfg 0 stored input hn hs hp hsize sets targets index target ht
    (by simpa only [hk] using (show TargetKind.globalStar ≠ .pivot by decide))
    y z outer.cost _ (by positivity) hin hout hbudget F hF

end

end StreamingSSSP.Hopset
