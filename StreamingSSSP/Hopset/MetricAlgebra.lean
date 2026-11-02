module

public import StreamingSSSP.Hopset.MetricBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def sumMetric (cfg : Config) (metrics : Fin n → Metric n cfg) : Metric n cfg :=
  fun r S ranks choice => ∑ v : Fin n, metrics v r S ranks choice

theorem metricPotential_sum (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (metrics : Fin n → Metric n cfg)
    (fuel r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ) :
    metricPotential cfg hn stored input (sumMetric cfg metrics) fuel r S ranks =
      ∑ v : Fin n, metricPotential cfg hn stored input (metrics v) fuel r S ranks := by
  have he : metricCharge cfg stored input (sumMetric cfg metrics) ranks =
      fun r S step => ∑ v : Fin n, metricCharge cfg stored input (metrics v) ranks r S step := by
    funext r S step
    by_cases hg : BallsGood cfg stored input r S <;>
      simp only [metricCharge, sumMetric, hg, ↓reduceIte, Finset.sum_const_zero]
  unfold metricPotential
  rw [he]
  exact Branching.potential_sum _ Finset.univ
    (fun v => metricCharge cfg stored input (metrics v) ranks) fuel r S

def copyVisit (cfg : Config) (v : Fin n) : Metric n cfg :=
  fun _ S _ _ => if v ∈ S then 1 else 0

theorem sum_copyVisit (cfg : Config) (r : ℕ) (S : Finset (Fin n)) (ranks : Fin n → ℕ)
    (choice : Choice n cfg) : sumMetric cfg (copyVisit cfg) r S ranks choice = S.card := by
  simp only [sumMetric, copyVisit]
  rw [Finset.sum_boole]
  have hS : (Finset.univ.filter fun v => v ∈ S) = S := by ext v; simp
  simp [hS]

theorem copyVisit_potential (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (v : Fin n) (fuel r : ℕ)
    (S : Finset (Fin n)) (ranks : Fin n → ℕ) :
    metricPotential cfg hn stored input (copyVisit cfg v) fuel r S ranks =
      copyPotential cfg hn stored input v fuel r S ranks := by
  have he : metricCharge cfg stored input (copyVisit cfg v) ranks = copyCharge cfg stored input v := by
    funext r S step
    by_cases hg : BallsGood cfg stored input r S <;> by_cases hv : v ∈ S <;>
      simp only [metricCharge, copyVisit, copyCharge, hg, hv, true_and, false_and, ↓reduceIte]
  unfold metricPotential copyPotential
  rw [he]

end

end StreamingSSSP.Hopset.Reference
