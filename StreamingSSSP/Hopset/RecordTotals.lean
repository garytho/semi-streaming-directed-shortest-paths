module

public import StreamingSSSP.Hopset.RecordMoments
public import StreamingSSSP.Hopset.TargetTotals

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

theorem vertexHits_sum (G : Graph (Fin n)) (S P : Finset (Fin n)) (hP : P ⊆ S)
    (v : Fin n) (radius : ℕ) :
    vertexHits G S v P radius =
      ∑ p ∈ P, ((if G.dist p v ≤ (radius : Distance) then 1 else 0) +
        if G.dist v p ≤ (radius : Distance) then 1 else 0) := by
  have hin : P ∩ incomingCentres G S v radius =
      P.filter fun p => G.dist p v ≤ (radius : Distance) := by
    ext p
    simp only [incomingCentres, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨hp, _, hd⟩
      exact ⟨hp, hd⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hP hp, hd⟩
  have hout : P ∩ outgoingCentres G S v radius =
      P.filter fun p => G.dist v p ≤ (radius : Distance) := by
    ext p
    simp only [outgoingCentres, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨hp, _, hd⟩
      exact ⟨hp, hd⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, hP hp, hd⟩
  simp only [vertexHits, hin, hout, Finset.card_filter, Finset.sum_add_distrib]

theorem searchRecords_sum (stored : Implicit.Representation n) (G : Graph (Fin n))
    (S P : Finset (Fin n)) (hP : P ⊆ S) (radius : ℕ) :
    (∑ p ∈ P, searchRecords stored G S p radius) =
      ∑ v ∈ S, vertexWeight stored v * vertexHits G S v P radius := by
  unfold searchRecords
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [vertexHits_sum G S P hP v radius, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hin : G.dist p v ≤ (radius : Distance) <;>
    by_cases hout : G.dist v p ≤ (radius : Distance) <;> simp [hin, hout, mul_two]

theorem recordMetric_sum (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ)
    (choice : Choice n cfg) (hP : choice.pivots ⊆ S) :
    (∑ v : Fin n, recordMetric cfg stored input v r S ranks choice) =
      nodeRecords cfg stored input ranks r S choice := by
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let A := advancePivots cfg r S ranks
  have he :
      (∑ v : Fin n, recordMetric cfg stored input v r S ranks choice) =
        ∑ v ∈ S, vertexWeight stored v * (vertexHits G S v choice.pivots (cfg.searchRadius r) +
          if r < cfg.earlyLevel then vertexHits G S v A (cfg.searchRadius r) else 0) := by
    simp only [recordMetric]
    rw [← Finset.sum_filter]
    have hS : (Finset.univ.filter fun v => v ∈ S) = S := by ext v; simp
    rw [hS]
  rw [he]
  calc
    _ = (∑ v ∈ S, vertexWeight stored v * vertexHits G S v choice.pivots (cfg.searchRadius r)) +
        if r < cfg.earlyLevel then
          ∑ v ∈ S, vertexWeight stored v * vertexHits G S v A (cfg.searchRadius r) else 0 := by
      by_cases hr : r < cfg.earlyLevel <;>
        simp only [hr, ↓reduceIte, mul_add, Finset.sum_add_distrib, mul_zero, add_zero]
    _ = (∑ p ∈ choice.pivots, searchRecords stored G S p (cfg.searchRadius r)) +
        if r < cfg.earlyLevel then ∑ p ∈ A, searchRecords stored G S p (cfg.searchRadius r) else 0 := by
      rw [searchRecords_sum stored G S choice.pivots hP (cfg.searchRadius r),
        searchRecords_sum stored G S A (Finset.filter_subset _ _) (cfg.searchRadius r)]
    _ = _ := rfl

theorem recordCharge_eq (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (r : ℕ) (S : Finset (Fin n))
    (step : Branching.Step (Finset (Fin n)) (Choice n cfg)) (hP : step.value.pivots ⊆ S) :
    (∑ v : Fin n, metricCharge cfg stored input (recordMetric cfg stored input v) ranks r S step) =
      if BallsGood cfg stored input r S then nodeRecords cfg stored input ranks r S step.value else 0 := by
  by_cases hg : BallsGood cfg stored input r S
  · simp only [metricCharge, hg, ↓reduceIte]
    exact recordMetric_sum cfg stored input r S ranks step.value hP
  · simp only [metricCharge, hg, ↓reduceIte, Finset.sum_const_zero]

end

end StreamingSSSP.Hopset.Reference
