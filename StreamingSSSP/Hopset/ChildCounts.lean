module

public import StreamingSSSP.Hopset.BadBudget
public import StreamingSSSP.Hopset.StoppedTrace

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

theorem grouped_volume_eq (S : Finset (Fin n)) (keep : Fin n → Bool) (key : Fin n → List ℕ) :
    volume (grouped S keep key) = (S.filter fun v => keep v = true).card := by
  let K := groupKeys S keep key
  let count := fun label => (S.filter fun v => keep v = true ∧ key v = label).card
  have he : volume (grouped S keep key) = ∑ label ∈ K.toFinset, count label := by
    simp only [volume, grouped, List.map_map]
    exact (List.sum_toFinset count (groupKeys_nodup S keep key)).symm
  rw [he]
  simp only [count, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hk : keep v = true
  · have hkey : key v ∈ K := (groupKeys_mem S keep key _).mpr ⟨v, hv, hk, rfl⟩
    simp [hk, hkey]
  · simp [hk]

theorem length_le_volume (blocks : List (Finset (Fin n)))
    (h : ∀ B ∈ blocks, B.Nonempty) : blocks.length ≤ volume blocks := by
  induction blocks with
  | nil => simp [volume]
  | cons B blocks ih =>
      have hB := Finset.card_pos.mpr (h B (by simp))
      have ht := ih (fun C hC => h C (by simp [hC]))
      simp only [List.length_cons, volume, List.map_cons, List.sum_cons] at *
      omega

namespace Geometry

theorem core_length_le (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ)
    (hpos : ∀ p ∈ P, 0 ≤ rho p) : (core G S P rho).length ≤ (S \ P).card := by
  apply (length_le_volume _ (grouped_nonempty S _ _)).trans
  change volume (grouped S (fun v => decide (Early.remaining G P rho v)) (labels G P rho)) ≤ _
  rw [grouped_volume_eq]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hvS, hr⟩ := Finset.mem_filter.mp hv
  apply Finset.mem_sdiff.mpr
  refine ⟨hvS, ?_⟩
  intro hvP
  have hself := Early.within_self G v (hpos v hvP)
  exact (of_decide_eq_true hr) v hvP ⟨hself, hself⟩

end Geometry

namespace Reference

theorem balls_good_empty (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) : BallsGood cfg stored input r ∅ := by
  intro v hv
  simp at hv

theorem children_length_early (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) (he : r < cfg.earlyLevel)
    (hP : choice.pivots ⊆ S) : (children cfg stored input r S choice).length ≤ S.card := by
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let rho := radii cfg r G choice.owners
  have hc := Geometry.core_length_le G S choice.pivots rho
    (fun p _ => radii_nonneg cfg hnum r G choice.owners p)
  have hcard := Finset.card_sdiff_add_card_eq_card hP
  have hm : (members choice.pivots).length = choice.pivots.card := by
    simpa only [members_toFinset] using
      (List.toFinset_card_of_nodup (members_nodup choice.pivots)).symm
  simp only [children, he, ↓reduceIte, List.length_append, Geometry.fringes, List.length_map]
  change (members choice.pivots).length + (Geometry.core G S choice.pivots rho).length ≤ S.card
  rw [hm]
  omega

def badChildren (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) : ℕ :=
  ((children cfg stored input r S choice).filter fun T =>
    decide (¬ BallsGood cfg stored input (r + 1) T)).length

theorem badChildren_le_weight (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) (hP : choice.pivots ⊆ S) :
    badChildren cfg stored input r S choice ≤
      if BadBirth cfg stored input r S choice then S.card else 0 := by
  by_cases hb : BadBirth cfg stored input r S choice
  · simp only [hb, ↓reduceIte]
    apply (List.length_filter_le _ _).trans
    by_cases he : r < cfg.earlyLevel
    · exact children_length_early cfg stored input hnum r S choice he hP
    · have hlen : (children cfg stored input r S choice).length ≤ 1 := by
        simp only [children, he, ↓reduceIte]
        split_ifs <;> simp
      have hS : 0 < S.card := by
        by_contra h
        have hzero : S = ∅ := Finset.card_eq_zero.mp (by omega)
        obtain ⟨T, hT, hbad⟩ := hb
        have hTzero : T = ∅ := Finset.subset_empty.mp
          (by simpa only [hzero] using children_subset cfg stored input r S choice T hT)
        subst T
        exact hbad (balls_good_empty cfg stored input (r + 1))
      exact hlen.trans hS
  · simp only [hb, ↓reduceIte, badChildren]
    have he :
        ((children cfg stored input r S choice).filter fun T =>
          decide (¬ BallsGood cfg stored input (r + 1) T)) =
          (children cfg stored input r S choice).filter (fun _ => false) := by
      apply List.filter_congr
      intro T hT
      have hg : BallsGood cfg stored input (r + 1) T := by
        by_contra h
        exact hb ⟨T, hT, h⟩
      simp [hg]
    rw [he]
    simp

theorem badMetric_sum (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ)
    (choice : Choice n cfg) :
    (∑ v : Fin n, badMetric cfg stored input v r S ranks choice) =
      if BadBirth cfg stored input r S choice then S.card else 0 := by
  by_cases hb : BadBirth cfg stored input r S choice
  · simp only [badMetric, hb, and_true, ↓reduceIte]
    rw [Finset.sum_boole]
    have hS : (Finset.univ.filter fun v => v ∈ S) = S := by ext v; simp
    simp [hS]
  · simp only [badMetric, hb, and_false, ↓reduceIte, Finset.sum_const_zero]

end Reference

end

end StreamingSSSP.Hopset
