module

public import StreamingSSSP.Core.Doubling

@[expose] public section

namespace StreamingSSSP.Core

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def addSources (seed : V → Distance) (U : Finset V) (L : Distance) : V → Distance :=
  fun v => min (seed v) (if v ∈ U then L else ⊤)

theorem addSources_upper (G : Graph V) (seed : V → Distance) (U : Finset V)
    (L : Distance) (v : V) :
    multiDist G (addSources seed U L) v ≤ multiDist G seed v :=
  multiDist_mono (fun _ _ => le_rfl) (fun _ => min_le_left _ _) v

theorem addSources_lower (G : Graph V) (seed : V → Distance) (U : Finset V)
    (L : Distance) (v : V) :
    min (multiDist G seed v) L ≤ multiDist G (addSources seed U L) v := by
  apply Finset.le_inf
  intro u _
  by_cases hu : u ∈ U
  · simp only [addSources, hu, ↓reduceIte, min_add]
    apply le_min
    · exact (min_le_left _ _).trans (multiDist_le G seed u v)
    · exact (min_le_right _ _).trans (le_add_of_nonneg_right bot_le)
  · simp only [addSources, hu, ↓reduceIte, min_top_right]
    exact (min_le_left _ _).trans (multiDist_le G seed u v)

theorem addSources_preserves (G : Graph V) (seed : V → Distance) (U : Finset V)
    (L : Distance) (v : V) (hv : multiDist G seed v ≤ L) :
    multiDist G (addSources seed U L) v = multiDist G seed v := by
  apply le_antisymm (addSources_upper G seed U L v)
  simpa only [min_eq_left hv] using addSources_lower G seed U L v

theorem addSources_external (G : Graph V) (seed : V → Distance) (U : Finset V)
    (L : Distance) {v : V} (hv : v ∈ U) (hd : L ≤ multiDist G seed v) :
    multiDist G (addSources seed U L) v = L := by
  apply le_antisymm
  · exact (multiDist_le_seed G (addSources seed U L) v).trans
      (by simp only [addSources, hv, ↓reduceIte]; exact min_le_right _ _)
  · simpa only [min_eq_right hd] using addSources_lower G seed U L v

theorem addSources_redundant (G : Graph V) (seed : V → Distance) (U : Finset V)
    (L : Distance) (hU : ∀ u ∈ U, multiDist G seed u ≤ L) :
    multiDist G (addSources seed U L) = multiDist G seed := by
  funext v
  apply le_antisymm (addSources_upper G seed U L v)
  apply multiDist_potential (fun _ _ => le_rfl)
  intro u
  by_cases hu : u ∈ U
  · exact le_min (multiDist_le_seed G seed u) (by simpa [hu] using hU u hu)
  · simpa [addSources, hu] using multiDist_le_seed G seed u

theorem found_redundant_sources (G : Graph V) (seed : V → Distance)
    (B known : Finset V) (r : ℕ) :
    multiDist G (addSources seed (found B known (multiDist G seed) r) (r : Distance)) =
      multiDist G seed :=
  addSources_redundant G seed _ _ (fun _u hu => (Finset.mem_filter.mp hu).2.2)

omit [Fintype V] in
theorem nextDistance_le (B known : Finset V) (d : V → Distance) {v : V}
    (hv : v ∈ B) (hk : v ∉ known) : nextDistance B known d ≤ d v :=
  Finset.inf_le (Finset.mem_sdiff.mpr ⟨hv, hk⟩)

omit [Fintype V] in
theorem nextDistance_gt_round (B known : Finset V) (d : V → Distance) (r : ℕ) :
    (r : Distance) < nextDistance B (known ∪ found B known d r) d := by
  apply lt_of_not_ge
  intro hnext
  have hnonempty : (B \ (known ∪ found B known d r)).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [nextDistance, he, Finset.inf_empty] at hnext
    exact WithTop.natCast_ne_top r (top_le_iff.mp hnext)
  obtain ⟨v, hv, he⟩ := Finset.exists_mem_eq_inf
    (B \ (known ∪ found B known d r)) hnonempty d
  have hvr : d v ≤ (r : Distance) := he ▸ hnext
  obtain ⟨hvB, hvnot⟩ := Finset.mem_sdiff.mp hv
  have hvK : v ∉ known := fun h => hvnot (Finset.mem_union_left _ h)
  exact hvnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvB, hvK, hvr⟩))

omit [Fintype V] in
theorem next_round_bounds (A : ℕ) (hA : 0 < A) (B known : Finset V)
    (d : V → Distance) (r : ℕ) :
    (r + 1 : ℕ) ≤ roundDistance A
        (nextDistance B (known ∪ found B known d (A * r)) d) ∧
      ∀ v ∈ B, v ∉ known ∪ found B known d (A * r) →
        roundDistance A (nextDistance B (known ∪ found B known d (A * r)) d) ≤
          roundDistance A (d v) := by
  constructor
  · have hgt := nextDistance_gt_round B known d (A * r)
    have hnot : ¬ roundDistance A (nextDistance B (known ∪ found B known d (A * r)) d)
        ≤ (r : Distance) := by
      rw [roundDistance_le_iff hA]
      exact not_le_of_gt hgt
    have hlt := lt_of_not_ge hnot
    generalize roundDistance A (nextDistance B (known ∪ found B known d (A * r)) d) = z at hlt ⊢
    induction z using WithTop.recTopCoe with
    | top => exact le_top
    | coe k =>
        change ((r + 1 : ℕ) : WithTop ℕ) ≤ (k : WithTop ℕ)
        exact WithTop.coe_le_coe.mpr (by exact Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hlt))
  · intro v hv hk
    exact roundDistance_mono hA (nextDistance_le B _ d hv hk)

omit [Fintype V] in
theorem scheduled_nonempty (A : ℕ) (hA : 0 < A) (B known : Finset V)
    (d : V → Distance) (r : ℕ)
    (hnext : roundDistance A (nextDistance B known d) = (r : Distance)) :
    (found B known d (A * r)).Nonempty := by
  have hn : (B \ known).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have he' : nextDistance B known d = ⊤ := by simp [nextDistance, he]
    rw [he', roundDistance_top] at hnext
    exact WithTop.natCast_ne_top r hnext.symm
  obtain ⟨v, hv, he⟩ := Finset.exists_mem_eq_inf (B \ known) hn d
  obtain ⟨hvB, hvK⟩ := Finset.mem_sdiff.mp hv
  refine ⟨v, Finset.mem_filter.mpr ⟨hvB, hvK, ?_⟩⟩
  apply (roundDistance_le_iff hA (d v)).mp
  rw [← he]
  exact hnext.le

namespace ScheduleCharge

structure State where
  insertions : ℕ
  searches : ℕ
  dirty : Bool

def valid (s : State) : Prop := s.searches + s.dirty.toNat ≤ s.insertions

def externalInsert (s : State) (count : ℕ) : State :=
  ⟨s.insertions + count, s.searches, true⟩

def searched (s : State) (foundCount : ℕ) : State :=
  ⟨s.insertions + foundCount, s.searches + 1, false⟩

theorem external_valid (s : State) (h : valid s) (k : ℕ) (hk : 0 < k) :
    valid (externalInsert s k) := by
  unfold valid externalInsert at *
  simp only [Bool.toNat_true]
  omega

theorem searched_valid (s : State) (h : valid s) (k : ℕ)
    (hprogress : s.dirty = true ∨ 0 < k) : valid (searched s k) := by
  unfold valid searched at *
  simp only [Bool.toNat_false, Nat.add_zero]
  rcases hprogress with hd | hk
  · simp only [hd, Bool.toNat_true] at h
    omega
  · omega

theorem searches_le (s : State) (h : valid s) : s.searches ≤ s.insertions := by
  unfold valid at h
  omega

end ScheduleCharge

end StreamingSSSP.Core
