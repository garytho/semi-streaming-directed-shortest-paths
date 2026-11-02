module

public import StreamingSSSP.Hopset.ChildCounts
public import StreamingSSSP.Hopset.MetricAlgebra

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def copyReward : Reward n := fun _ queue _ => volume queue
def recordReward : Reward n := fun _ _ step => step.records
def blockReward : Reward n := fun _ _ step => volume step.output.blocks

def badReward (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) : Reward n :=
  fun r _ step => (step.children.filter fun T =>
    decide (¬ Reference.BallsGood cfg stored input (r + 1) T)).length

theorem filter_count_cast {A : Type*} (L : List A) (P : A → Prop) [DecidablePred P] :
    ((L.filter fun a => decide (P a)).length : ℝ) =
      (L.map fun a => if P a then (1 : ℝ) else 0).sum := by
  induction L with
  | nil => simp
  | cons a L ih => by_cases ha : P a <;> simp [ha, ih, Nat.cast_add, add_comm]

theorem copyReward_mean (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ) (queue : List (Finset (Fin n))) :
    (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
        (fun step => (copyReward r queue step : ℝ)) =
      ∑ i : Fin queue.toArray.size,
        (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
          (fun step => (Reference.sumMetric cfg (Reference.copyVisit cfg)
            r (queue.toArray.toVector.get i) (fun v => rank.get v) step.value : ℝ)) := by
  simp only [copyReward]
  simp_rw [Reference.sum_copyVisit, Law.expect_const]
  simpa only [volume, Nat.cast_list_sum, List.map_map, Function.comp_def] using
    queue_sum queue (fun S => (S.card : ℝ))

theorem recordReward_mean (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ) (queue : List (Finset (Fin n)))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
        (fun step => (recordReward r queue step : ℝ)) =
      ∑ i : Fin queue.toArray.size,
        (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
          (fun step => (Reference.sumMetric cfg (Reference.recordMetric cfg stored input)
            r (queue.toArray.toVector.get i) (fun v => rank.get v) step.value : ℝ)) := by
  rw [show (fun step : Step n => (recordReward r queue step : ℝ)) =
    fun step => (step.records : ℝ) from rfl, level_records cfg hn stored input rank r _ hs hp hsize]
  apply Finset.sum_congr rfl
  intro i _
  exact (Reference.kernel_recordMetric_sum cfg hn stored input (fun v => rank.get v)
    r (queue.toArray.toVector.get i)).symm

theorem blockReward_mean (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ) (queue : List (Finset (Fin n)))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator) :
    (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
        (fun step => (blockReward r queue step : ℝ)) =
      ∑ i : Fin queue.toArray.size,
        (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
          (fun step => (Reference.sumMetric cfg (Reference.blockMetric cfg stored input)
            r (queue.toArray.toVector.get i) (fun v => rank.get v) step.value : ℝ)) := by
  have h := level_blocks cfg hn stored input rank r queue.toArray.toVector hs hp hsize hnum
    (fun B => (B.card : ℝ))
  have hsum (S : Finset (Fin n)) (choice : Reference.Choice n cfg) :
      Reference.sumMetric cfg (Reference.blockMetric cfg stored input)
          r S (fun v => rank.get v) choice = volume (Reference.blocks cfg stored input r S choice) := by
    unfold Reference.sumMetric Reference.blockMetric
    exact Reference.blockCounts_sum _
  simp_rw [hsum]
  simpa only [blockReward, volume, Nat.cast_list_sum, List.map_map, Function.comp_def] using h

theorem badReward_mean_le (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ) (queue : List (Finset (Fin n)))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator) :
    (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
        (fun step => (badReward cfg stored input r queue step : ℝ)) ≤
      ∑ i : Fin queue.toArray.size,
        (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
          (fun step => (Reference.sumMetric cfg (Reference.badMetric cfg stored input)
            r (queue.toArray.toVector.get i) (fun v => rank.get v) step.value : ℝ)) := by
  let bad := fun T => ¬ Reference.BallsGood cfg stored input (r + 1) T
  have he (step : Step n) :
      (badReward cfg stored input r queue step : ℝ) =
        (step.children.map fun T => if bad T then (1 : ℝ) else 0).sum :=
    filter_count_cast step.children bad
  simp_rw [he]
  rw [level_children cfg hn stored input rank r _ hs hp hsize hnum]
  apply Finset.sum_le_sum
  intro i _
  simp only [Reference.kernel, Law.expect_map]
  apply Early.Sampling.expect_mono_on
  refine Early.Sampling.holds_mono
    (Reference.choices_subset cfg hn r (queue.toArray.toVector.get i) (fun v => rank.get v)) ?_
  intro choice hP
  rw [← filter_count_cast]
  have hnat :
      Reference.badChildren cfg stored input r (queue.toArray.toVector.get i) choice ≤
        Reference.sumMetric cfg (Reference.badMetric cfg stored input)
          r (queue.toArray.toVector.get i) (fun v => rank.get v) choice :=
    (Reference.badChildren_le_weight cfg stored input hnum r _ choice hP).trans_eq
      (Reference.badMetric_sum cfg stored input r _ (fun v => rank.get v) choice).symm
  exact_mod_cast hnat

theorem root_traceCost_le_sum (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ps : List Rate)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) (hnum : 0 < cfg.initialNumerator)
    (reward : Reward n) (metrics : Fin n → Reference.Metric n cfg)
    (hlocal : ∀ rank r queue, AllGood cfg stored input r queue →
      (levelLaw cfg hn stored input rank r queue.toArray.toVector).expect
          (fun step => (reward r queue step : ℝ)) ≤
        ∑ i : Fin queue.toArray.size,
          (Reference.kernel cfg hn stored input (fun v => rank.get v) r (queue.toArray.toVector.get i)).expect
            (fun step => (Reference.sumMetric cfg metrics r (queue.toArray.toVector.get i)
              (fun v => rank.get v) step.value : ℝ)))
    (fuel : ℕ) :
    ((Law.family n (fun _ => Ranks.firstHit ps)).bind fun ranks =>
        traceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 [Finset.univ]).expect
        (fun trace => (traceCost reward trace : ℝ)) ≤
      ∑ v : Fin n, (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
        Reference.metricPotential cfg hn stored input (metrics v) fuel 0 Finset.univ ranks) := by
  rw [Law.expect_bind]
  calc
    _ ≤ (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
        Reference.metricPotential cfg hn stored input (Reference.sumMetric cfg metrics)
          fuel 0 Finset.univ ranks) := by
      apply Law.expect_mono
      intro ranks
      have h := expected_traceCost_le cfg hn stored input (Vector.ofFn ranks) hs hp hsize hnum
        reward (Reference.sumMetric cfg metrics) (hlocal (Vector.ofFn ranks)) fuel 0 [Finset.univ]
      simpa only [List.map_singleton, List.sum_singleton, Vector.get_ofFn] using h
    _ = _ := by
      simp_rw [Reference.metricPotential_sum]
      rw [Law.expect_finset_sum]

end

end StreamingSSSP.Hopset.Batched
