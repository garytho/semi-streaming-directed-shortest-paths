module

public import StreamingSSSP.Late.Paths

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {V : Type*} [Fintype V]

def block (H : Graph V) (S : Finset V) (p : V) (rho D : ℝ) : Finset V :=
  S ∩ bothBall H p (rho + D)

def coreChild (H : Graph V) (S P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) : Finset V :=
  S.filter fun v => v ∈ coreClass H P rho L

def emptyChild (H : Graph V) (S P : Finset V) (rho : V → ℝ) : Finset V :=
  S.filter fun v => ∀ p ∈ P, ¬ Within H v p (rho p) ∧ ¬ Within H p v (rho p)

@[simp] theorem mem_emptyChild (H : Graph V) (S P : Finset V)
    (rho : V → ℝ) (v : V) :
    v ∈ emptyChild H S P rho ↔
      v ∈ S ∧ ∀ p ∈ P, ¬ Within H v p (rho p) ∧ ¬ Within H p v (rho p) := by
  simp [emptyChild]

theorem emptyChild_eq_core (H : Graph V) (S P : Finset V) (rho : V → ℝ) :
    emptyChild H S P rho = coreChild H S P rho (∅, ∅) := by
  ext v
  simp only [mem_emptyChild, coreChild, Finset.mem_filter, coreClass, Set.mem_ofPred_eq,
    labels, Prod.mk.injEq, Finset.filter_eq_empty_iff]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, (fun p hp h' => (h p hp).1 h'.1),
      (fun p hp => (h p hp).1), (fun p hp => (h p hp).2)⟩
  · rintro ⟨hv, _, hin, hout⟩
    exact ⟨hv, fun _ hp => ⟨hin hp, hout hp⟩⟩

def Separates (P : V → Prop) (u v z : V) : Prop :=
  (P u ∧ P v ∧ ¬ P z) ∨ (¬ P u ∧ ¬ P v ∧ P z)

def BallSeparation (H : Graph V) (p : V) (rho : ℝ) (u v z : V) : Prop :=
  Separates (fun x => Within H p x rho) u v z ∨
    Separates (fun x => Within H x p rho) u v z

omit [Fintype V] in
theorem separates_of_diff {P : V → Prop} {u v z : V}
    (huv : P u ↔ P v) (hz : ¬ (P z ↔ P u)) : Separates P u v z := by
  by_cases hu : P u <;> by_cases hv : P v <;> by_cases hzz : P z <;>
    simp_all [Separates]

omit [Fintype V] in
theorem iff_of_not_separates {P : V → Prop} {u v z : V}
    (huv : P u ↔ P v) (hn : ¬ Separates P u v z) : P z ↔ P u := by
  by_contra h
  exact hn (separates_of_diff huv h)

theorem core_cut (H : Graph V) (S P : Finset V) (rho : V → ℝ)
    (L : Finset V × Finset V) {u v z : V}
    (hu : u ∈ coreChild H S P rho L) (hv : v ∈ coreChild H S P rho L)
    (hzS : z ∈ S) (hz : z ∉ coreChild H S P rho L) :
    ∃ p ∈ P, BallSeparation H p (rho p) u v z := by
  have huC := (Finset.mem_filter.mp hu).2
  have hvC := (Finset.mem_filter.mp hv).2
  have huv : labels H P rho u = labels H P rho v := huC.2.trans hvC.2.symm
  have hinuv (p : V) (hp : p ∈ P) : Within H u p (rho p) ↔ Within H v p (rho p) := by
    have h := Finset.ext_iff.mp (congrArg Prod.fst huv) p
    simpa [labels, hp] using h
  have houtuv (p : V) (hp : p ∈ P) : Within H p u (rho p) ↔ Within H p v (rho p) := by
    have h := Finset.ext_iff.mp (congrArg Prod.snd huv) p
    simpa [labels, hp] using h
  by_contra hn
  have hsep (p : V) (hp : p ∈ P) : ¬ BallSeparation H p (rho p) u v z :=
    fun h => hn ⟨p, hp, h⟩
  have hin (p : V) (hp : p ∈ P) : Within H z p (rho p) ↔ Within H u p (rho p) :=
    iff_of_not_separates (hinuv p hp) (fun h => hsep p hp (Or.inr h))
  have hout (p : V) (hp : p ∈ P) : Within H p z (rho p) ↔ Within H p u (rho p) :=
    iff_of_not_separates (houtuv p hp) (fun h => hsep p hp (Or.inl h))
  apply hz
  apply Finset.mem_filter.mpr
  refine ⟨hzS, ?_, ?_⟩
  · intro p hp h
    exact huC.1 p hp ⟨(hin p hp).mp h.1, (hout p hp).mp h.2⟩
  · apply Eq.trans _ huC.2
    apply Prod.ext <;> ext p <;> simp only [labels, Finset.mem_filter]
    · exact and_congr_right (hin p)
    · exact and_congr_right (hout p)

/-- No pivots, old or new, are deleted from this fringe. The direction
assumption is supplied by the no-bridge event, not by resampling it. -/
theorem fringe_cut (H : Graph V) (p : V) (rho D : ℝ) {u v z : V}
    (hu : u ∈ fringe H p rho D) (hv : v ∈ fringe H p rho D)
    (hz : z ∉ fringe H p rho D)
    (hdir : (¬ Within H u p (rho + D) ∧ ¬ Within H v p (rho + D)) ∨
      (¬ Within H p u (rho + D) ∧ ¬ Within H p v (rho + D))) :
    BallSeparation H p (rho - D) u v z ∨
      BallSeparation H p (rho + D) u v z := by
  have hu' := (mem_fringe _ _ _ _ _).mp hu
  have hv' := (mem_fringe _ _ _ _ _).mp hv
  by_cases hzi : Within H p z (rho - D) ∨ Within H z p (rho - D)
  · left
    rcases hzi with h | h
    · exact Or.inl (Or.inr ⟨fun h => hu'.2 (Or.inl h), fun h => hv'.2 (Or.inl h), h⟩)
    · exact Or.inr (Or.inr ⟨fun h => hu'.2 (Or.inr h), fun h => hv'.2 (Or.inr h), h⟩)
  · have hzo : ¬ (Within H p z (rho + D) ∨ Within H z p (rho + D)) := by
      intro h
      exact hz ((mem_fringe _ _ _ _ _).mpr ⟨h, hzi⟩)
    right
    rcases hdir with h | h
    · exact Or.inl (Or.inl ⟨hu'.1.resolve_right h.1, hv'.1.resolve_right h.2,
        fun h => hzo (Or.inl h)⟩)
    · exact Or.inr (Or.inl ⟨hu'.1.resolve_left h.1, hv'.1.resolve_left h.2,
        fun h => hzo (Or.inr h)⟩)

def Window (d : Distance) (a : ℝ) (backward : Bool) (rho : ℝ) : Prop :=
  ∃ q : ℕ, d = q ∧
    if backward then (q : ℝ) - a ≤ rho ∧ rho < q
    else (q : ℝ) ≤ rho ∧ rho < q + a

def windows (H : Graph V) (p u v : V) (a rho : ℝ) : Prop :=
  Window (H.dist p u) a false rho ∨
  Window (H.dist p v) a true rho ∨
  Window (H.dist v p) a false rho ∨
  Window (H.dist u p) a true rho

theorem window_positive {d : Distance} {a r : ℝ} {b : Bool}
    (h : Window d a b r) : 0 < a := by
  obtain ⟨q, _, h⟩ := h
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> linarith

theorem windows_positive (H : Graph V) {p u v : V} {a r : ℝ}
    (h : windows H p u v a r) : 0 < a := by
  rcases h with h | h | h | h <;> exact window_positive h

theorem not_within_lt {H : Graph V} {u v : V} {r : ℝ} {q : ℕ}
    (hd : H.dist u v = q) (h : ¬ Within H u v r) : r < q := by
  by_contra hn
  exact h ⟨q, hd, le_of_not_gt hn⟩

theorem separation_windows (H : Graph V) {p u v z : V} {a r : ℝ}
    (huz : Within H u z a) (hzv : Within H z v a)
    (h : BallSeparation H p r u v z) : windows H p u v a r := by
  rcases h with (⟨hu, _, hz⟩ | ⟨_, hv, hz⟩) | (⟨_, hv, hz⟩ | ⟨hu, _, hz⟩)
  · obtain ⟨q, hq, hqr⟩ := hu
    have hbound := within_trans (show Within H p u (q : ℝ) from ⟨q, hq, le_rfl⟩) huz
    have hlt : r < (q : ℝ) + a := by
      by_contra hn
      exact hz (within_mono hbound (le_of_not_gt hn))
    exact Or.inl ⟨q, hq, hqr, hlt⟩
  · obtain ⟨q, hq, hqr⟩ := within_trans hz hzv
    have hlt := not_within_lt hq hv
    exact Or.inr (Or.inl ⟨q, hq, by dsimp; constructor <;> linarith⟩)
  · obtain ⟨q, hq, hqr⟩ := hv
    have hbound := within_trans hzv (show Within H v p (q : ℝ) from ⟨q, hq, le_rfl⟩)
    have hlt : r < (q : ℝ) + a := by
      by_contra hn
      exact hz (within_mono hbound (by linarith))
    exact Or.inr (Or.inr (Or.inl ⟨q, hq, hqr, hlt⟩))
  · obtain ⟨q, hq, hqr⟩ := within_trans huz hz
    have hlt := not_within_lt hq hu
    exact Or.inr (Or.inr (Or.inr ⟨q, hq, by dsimp; constructor <;> linarith⟩))

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t u : Fin n}

theorem prefix_support_in_block (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S : Finset (Fin n)) (hS : Q.Inside S) (p : Fin n) (rho D : ℝ)
    (hD : (Q.searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) t p rho) :
    ∀ z ∈ Q.support, z ∈ block (rounded A (R.restricted G S)) S p rho D := by
  classical
  intro z hz
  simp only [block, Finset.mem_inter, mem_bothBall]
  refine ⟨hS z hz, Or.inr ?_⟩
  exact within_mono (within_trans (Q.support_to_end A hA hS hz) hp) (by linarith)

theorem suffix_support_in_block (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S : Finset (Fin n)) (hS : Q.Inside S) (p : Fin n) (rho D : ℝ)
    (hD : (Q.searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) p s rho) :
    ∀ z ∈ Q.support, z ∈ block (rounded A (R.restricted G S)) S p rho D := by
  classical
  intro z hz
  simp only [block, Finset.mem_inter, mem_bothBall]
  refine ⟨hS z hz, Or.inl ?_⟩
  exact within_mono (within_trans hp (Q.start_to_support A hA hS hz)) (by linarith)

theorem weighted_closure_edge (Q : Path R G s t) (B : Finset (Fin n))
    (hB : Q.Inside B) (hst : s ≠ t) :
    closure (R.base G) B s t ≤ (Q.micro : Distance) := by
  classical
  have hs := hB s Q.endpoints_support.1
  have ht := hB t Q.endpoints_support.2
  simp only [Implicit.closure,
    ite_eq_left (show s ∈ B ∧ t ∈ B ∧ s ≠ t from ⟨hs, ht, hst⟩)]
  have h := (induced (R.base G) B).dist_le_pathCost Q.expansion_endpoints
  rw [induced_path_cost _ _ Q.expansion (fun z hz => hB z (Q.expansion_support hz)),
    Q.expansion_cost] at h
  exact h

theorem weighted_prefix_edge (P : Path R G s u) (T : Path R G u t)
    (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : (P.append T).Inside S) (p : Fin n) (rho D : ℝ)
    (hD : ((P.append T).searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) t p rho) (hsu : s ≠ u) :
    closure (R.base G) (block (rounded A (R.restricted G S)) S p rho D) s u ≤
      (P.micro : Distance) := by
  apply weighted_closure_edge P _ _ hsu
  exact ((P.inside_append T).mp
    (prefix_support_in_block (P.append T) A hA S hS p rho D hD hp)).1

theorem weighted_suffix_edge (P : Path R G s u) (T : Path R G u t)
    (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : (P.append T).Inside S) (p : Fin n) (rho D : ℝ)
    (hD : ((P.append T).searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) p s rho) (hut : u ≠ t) :
    closure (R.base G) (block (rounded A (R.restricted G S)) S p rho D) u t ≤
      (T.micro : Distance) := by
  apply weighted_closure_edge T _ _ hut
  exact ((P.inside_append T).mp
    (suffix_support_in_block (P.append T) A hA S hS p rho D hD hp)).2

end

end StreamingSSSP.Late
