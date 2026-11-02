module

public import StreamingReachability.Hopset.NodeQueries
public import StreamingReachability.Hopset.LocalEarly
public import StreamingReachability.Hopset.History

@[expose] public section

namespace StreamingReachability.Hopset.Geometry

open scoped Classical

noncomputable section

variable {n : ℕ}

def labels (G : Graph (Fin n)) (P : Finset (Fin n)) (rho : Fin n → ℝ)
    (v : Fin n) : List ℕ :=
  (members P).flatMap fun p =>
    (if Early.Within G v p (rho p) then [2 * p.val] else []) ++
      if Early.Within G p v (rho p) then [2 * p.val + 1] else []

theorem label_even (G : Graph (Fin n)) (P : Finset (Fin n)) (rho : Fin n → ℝ)
    (p v : Fin n) :
    2 * p.val ∈ labels G P rho v ↔ p ∈ P ∧ Early.Within G v p (rho p) := by
  constructor
  · intro h
    obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp ht with hin | hout
    · by_cases hr : Early.Within G v q (rho q)
      · simp only [hr, ↓reduceIte, List.mem_singleton] at hin
        have hqp : q = p := Fin.ext (by omega)
        subst q
        exact ⟨(mem_members P p).mp hq, hr⟩
      · simp [hr] at hin
    · by_cases hr : Early.Within G q v (rho q) <;>
        simp only [hr, ↓reduceIte, List.mem_singleton, List.not_mem_nil] at hout <;> omega
  · rintro ⟨hp, hv⟩
    apply List.mem_flatMap.mpr
    refine ⟨p, (mem_members P p).mpr hp, ?_⟩
    apply List.mem_append.mpr
    exact Or.inl (by simp [hv])

theorem label_odd (G : Graph (Fin n)) (P : Finset (Fin n)) (rho : Fin n → ℝ)
    (p v : Fin n) :
    2 * p.val + 1 ∈ labels G P rho v ↔ p ∈ P ∧ Early.Within G p v (rho p) := by
  constructor
  · intro h
    obtain ⟨q, hq, ht⟩ := List.mem_flatMap.mp h
    rcases List.mem_append.mp ht with hin | hout
    · by_cases hr : Early.Within G v q (rho q) <;>
        simp only [hr, ↓reduceIte, List.mem_singleton, List.not_mem_nil] at hin <;> omega
    · by_cases hr : Early.Within G q v (rho q)
      · simp only [hr, ↓reduceIte, List.mem_singleton] at hout
        have hqp : q = p := Fin.ext (by omega)
        subst q
        exact ⟨(mem_members P p).mp hq, hr⟩
      · simp [hr] at hout
  · rintro ⟨hp, hv⟩
    apply List.mem_flatMap.mpr
    refine ⟨p, (mem_members P p).mpr hp, ?_⟩
    apply List.mem_append.mpr
    exact Or.inr (by simp [hv])

theorem labels_equal_iff (G : Graph (Fin n)) (P : Finset (Fin n)) (rho : Fin n → ℝ)
    (u v : Fin n) :
    labels G P rho u = labels G P rho v ↔ Early.labels G P rho u = Early.labels G P rho v := by
  constructor
  · intro h
    apply Prod.ext
    · ext p
      have he : 2 * p.val ∈ labels G P rho u ↔ 2 * p.val ∈ labels G P rho v := by rw [h]
      simpa only [label_even, Early.labels, Finset.mem_filter] using he
    · ext p
      have he : 2 * p.val + 1 ∈ labels G P rho u ↔ 2 * p.val + 1 ∈ labels G P rho v := by rw [h]
      simpa only [label_odd, Early.labels, Finset.mem_filter] using he
  · intro h
    unfold labels
    apply List.flatMap_congr
    intro p hp
    have hpP := (mem_members P p).mp hp
    have hi : Early.Within G u p (rho p) ↔ Early.Within G v p (rho p) := by
      have he : p ∈ (Early.labels G P rho u).1 ↔ p ∈ (Early.labels G P rho v).1 := by
        rw [congrArg Prod.fst h]
      simpa only [Early.labels, Finset.mem_filter, hpP, true_and] using he
    have ho : Early.Within G p u (rho p) ↔ Early.Within G p v (rho p) := by
      have he : p ∈ (Early.labels G P rho u).2 ↔ p ∈ (Early.labels G P rho v).2 := by
        rw [congrArg Prod.snd h]
      simpa only [Early.labels, Finset.mem_filter, hpP, true_and] using he
    simp only [propext hi, propext ho]

def core (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) :
    List (Finset (Fin n)) :=
  grouped S (fun v => decide (Early.remaining G P rho v)) (labels G P rho)

def fringes (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) (D : ℝ) :
    List (Finset (Fin n)) :=
  (members P).map fun p => S ∩ Early.fringe G p (rho p) D

theorem core_subset (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) :
    ∀ T ∈ core G S P rho, T ⊆ S :=
  grouped_subset _ _ _

theorem core_class (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ)
    (T : Finset (Fin n)) (hT : T ∈ core G S P rho) :
    ∃ L, ∀ v ∈ T, v ∈ Early.coreClass G P rho L := by
  obtain ⟨v0, hv0⟩ := grouped_nonempty S _ _ T hT
  obtain ⟨key, _, hkey⟩ := List.mem_map.mp hT
  refine ⟨Early.labels G P rho v0, ?_⟩
  intro v hv
  have hv' : v ∈ S.filter (fun w => decide (Early.remaining G P rho w) = true ∧
      labels G P rho w = key) := hkey.symm ▸ hv
  have hv0' : v0 ∈ S.filter (fun w => decide (Early.remaining G P rho w) = true ∧
      labels G P rho w = key) := hkey.symm ▸ hv0
  have hd := (Finset.mem_filter.mp hv').2
  have hd0 := (Finset.mem_filter.mp hv0').2
  exact ⟨of_decide_eq_true hd.1,
    (labels_equal_iff G P rho v v0).mp (hd.2.trans hd0.2.symm)⟩

theorem core_disjoint_pivots (G : Graph (Fin n)) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (hrho : ∀ p ∈ P, 0 ≤ rho p) :
    ∀ T ∈ core G S P rho, Disjoint T P := by
  intro T hT
  obtain ⟨L, hL⟩ := core_class G S P rho T hT
  apply Finset.disjoint_left.mpr
  intro v hv hvP
  have hself := Early.within_self G v (hrho v hvP)
  exact (hL v hv).1 v hvP ⟨hself, hself⟩

theorem core_count_at (G : Graph (Fin n)) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (v : Fin n) :
    ((core G S P rho).map fun T => if v ∈ T then (1 : ℝ) else 0).sum ≤ 1 :=
  grouped_sum_at _ _ _ _

theorem fringe_subset (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) (D : ℝ) :
    ∀ T ∈ fringes G S P rho D, T ⊆ S := by
  intro T hT
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hT
  exact Finset.inter_subset_left

theorem fringe_center_not_mem (G : Graph (Fin n)) (S : Finset (Fin n))
    (rho : Fin n → ℝ) (D : ℝ) (p : Fin n) (hrho : D ≤ rho p) :
    p ∉ S ∩ Early.fringe G p (rho p) D := by
  intro hp
  have hfringe := (Finset.mem_inter.mp hp).2
  have hinner := (Early.mem_fringe G p p (rho p) D).mp hfringe |>.2
  exact hinner (Or.inl (Early.within_self G p (by linarith)))

theorem core_history (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ)
    (history : List (CopyHistory.Observation n)) (h : CopyHistory.compatible history S)
    (r : ℕ) (hrho : ∀ p ∈ P, 0 ≤ rho p) (T : Finset (Fin n)) (hT : T ∈ core G S P rho) :
    CopyHistory.compatible (history ++ [.core r S P]) T :=
  CopyHistory.compatible_append history _ h (core_subset G S P rho T hT)
    ⟨core_subset G S P rho T hT, core_disjoint_pivots G S P rho hrho T hT⟩

theorem fringe_history (G : Graph (Fin n)) (S : Finset (Fin n)) (rho : Fin n → ℝ)
    (history : List (CopyHistory.Observation n)) (h : CopyHistory.compatible history S)
    (r : ℕ) (D : ℝ) (p : Fin n) (hrho : D ≤ rho p) :
    CopyHistory.compatible (history ++ [.fringe r p]) (S ∩ Early.fringe G p (rho p) D) :=
  CopyHistory.compatible_append history _ h Finset.inter_subset_left
    (fringe_center_not_mem G S rho D p hrho)

theorem inball_subset (F : Graph (Fin n)) (T : Finset (Fin n))
    (hF : Implicit.induced F T = F) (v : Fin n) (hv : v ∈ T) (t : ℝ) :
    Early.searchIn F v t ⊆ T := by
  intro u hu
  apply Late.bothBall_subset_of_induced F T hF hv t
  exact (Early.mem_bothBall F v u t).mpr (Or.inr (Finset.mem_filter.mp hu).2)

theorem outball_subset (F : Graph (Fin n)) (T : Finset (Fin n))
    (hF : Implicit.induced F T = F) (v : Fin n) (hv : v ∈ T) (t : ℝ) :
    Early.searchOut F v t ⊆ T := by
  intro u hu
  apply Late.bothBall_subset_of_induced F T hF hv t
  exact (Early.mem_bothBall F v u t).mpr (Or.inl (Finset.mem_filter.mp hu).2)

theorem core_inball_shrink (G F : Graph (Fin n)) (T P : Finset (Fin n))
    (rho : Fin n → ℝ) (L : Finset (Fin n) × Finset (Fin n))
    (hcore : ∀ u ∈ T, u ∈ Early.coreClass G P rho L)
    (hF : Implicit.induced F T = F) (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (v : Fin n) (hv : v ∈ T) (t : ℝ) (hsmall : ∀ p ∈ P, t ≤ rho p) (b : ℕ)
    (hhit : ∀ u ∈ Early.searchIn G v t,
      b ≤ 2 * Tournament.degree (Early.searchIn G v t) (Early.inComparison G) u →
        ∃ p ∈ P ∩ Early.searchIn G v t, Early.inComparison G u p) :
    (Early.searchIn F v t).card ≤ b := by
  have hsub : Early.searchIn F v t ⊆
      Tournament.survivors (Early.searchIn G v t) (P ∩ Early.searchIn G v t)
        (Early.inComparison G) := by
    intro u hu
    have huT := inball_subset F T hF v hv t hu
    have hdist := Early.bounded_mono_distance (hmono u v) (Finset.mem_filter.mp hu).2
    apply (Early.mem_tournament_survivors _ _ _ _).mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, ?_⟩
    intro p hp
    obtain ⟨hpP, hpA⟩ := Finset.mem_inter.mp hp
    exact Early.core_in_knockout G P rho L (hcore u huT) (hcore v hv) hpP
      (Early.within_mono (Finset.mem_filter.mp hpA).2 (hsmall p hpP))
  exact (Finset.card_le_card hsub).trans
    (Tournament.survivors_card_le _ _ _ b
      (fun u _ p _ => Early.inComparison_total G u p) hhit)

theorem core_outball_shrink (G F : Graph (Fin n)) (T P : Finset (Fin n))
    (rho : Fin n → ℝ) (L : Finset (Fin n) × Finset (Fin n))
    (hcore : ∀ u ∈ T, u ∈ Early.coreClass G P rho L)
    (hF : Implicit.induced F T = F) (hmono : ∀ u v, G.dist u v ≤ F.dist u v)
    (v : Fin n) (hv : v ∈ T) (t : ℝ) (hsmall : ∀ p ∈ P, t ≤ rho p) (b : ℕ)
    (hhit : ∀ u ∈ Early.searchOut G v t,
      b ≤ 2 * Tournament.degree (Early.searchOut G v t) (Early.outComparison G) u →
        ∃ p ∈ P ∩ Early.searchOut G v t, Early.outComparison G u p) :
    (Early.searchOut F v t).card ≤ b := by
  have hsub : Early.searchOut F v t ⊆
      Tournament.survivors (Early.searchOut G v t) (P ∩ Early.searchOut G v t)
        (Early.outComparison G) := by
    intro u hu
    have huT := outball_subset F T hF v hv t hu
    have hdist := Early.bounded_mono_distance (hmono v u) (Finset.mem_filter.mp hu).2
    apply (Early.mem_tournament_survivors _ _ _ _).mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, ?_⟩
    intro p hp
    obtain ⟨hpP, hpA⟩ := Finset.mem_inter.mp hp
    exact Early.core_out_knockout G P rho L (hcore u huT) (hcore v hv) hpP
      (Early.within_mono (Finset.mem_filter.mp hpA).2 (hsmall p hpP))
  exact (Finset.card_le_card hsub).trans
    (Tournament.survivors_card_le _ _ _ b
      (fun u _ p _ => Early.outComparison_total G u p) hhit)

theorem runtime_fringe_size (G : Graph (Fin n)) (S : Finset (Fin n)) (p : Fin n)
    (D : ℝ) (k M N b : ℕ) (hk : 0 < k) (hD : 0 < D) (z : Fin M × Fin N)
    (hin : (Early.searchIn G p (Early.searchRadius k M D)).card ≤ b)
    (hout : (Early.searchOut G p (Early.searchRadius k M D)).card ≤ b) :
    (S ∩ Early.fringe G p (Late.radius G D k M N hk p z) D).card ≤ b / k := by
  apply (Finset.card_le_card Finset.inter_subset_right).trans
  rw [runtime_minimum_card]
  exact Early.early_fringe_card_le G p k M N b hk hD z hin hout

theorem child_edge_mono (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {S T : Finset (Fin n)} (hTS : T ⊆ S)
    (u v : Fin n) :
    Backend.roundedRestricted stored input S cfg.inputScale u v ≤
      Backend.roundedRestricted stored input T cfg.inputScale u v :=
  Core.roundDistance_mono cfg.inputScale_pos (stored.restricted_mono _ hTS u v)

theorem child_distance_mono (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {S T : Finset (Fin n)} (hTS : T ⊆ S)
    (u v : Fin n) :
    (Backend.roundedRestricted stored input S cfg.inputScale).dist u v ≤
      (Backend.roundedRestricted stored input T cfg.inputScale).dist u v :=
  Graph.dist_mono (child_edge_mono cfg stored input hTS) u v

end

end StreamingReachability.Hopset.Geometry
