module

public import StreamingReachability.Hopset.PathMeans
public import StreamingReachability.Hopset.BadBudget

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

def rootState (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    {s t : Fin n} (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) :
    State cfg stored input 0 :=
  { known := fun _ => none
    queue := [Finset.univ]
    paths := [{
      node := ⟨0, by simp⟩
      source := s
      target := t
      path := Q
      inside := by
        intro v hv
        simpa [Vector.get_eq_getElem] using Finset.mem_univ v }]
    layers := [] }

theorem rootState_good (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    {s t : Fin n} (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) :
    Batched.AllGood cfg stored input 0 (rootState cfg stored input Q).queue := by
  intro S hS
  have he : S = Finset.univ := List.mem_singleton.mp hS
  subst S
  exact Reference.root_balls_good cfg stored input Finset.univ

theorem primeRelated_count {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {r : ℕ}
    (hnum : 0 < cfg.initialNumerator) (st : State cfg stored input r)
    (hb : 1 ≤ Parameters.ballSize n r) :
    st.primeRelated hnum ≤ 2 * Parameters.ballSize n r * st.primeCount hnum := by
  by_cases hg : Batched.AllGood cfg stored input r st.queue
  · simp only [State.primeRelated, State.primeCount, hg, ↓reduceIte]
    let paths := splitAll cfg r hnum st.paths
    let metric := fun P : TrackedPath stored input st.queue.toArray.toVector =>
      (relatedVertices (Backend.roundedRestricted stored input (st.queue.toArray.toVector.get P.node) cfg.inputScale)
        P.path.vertices (RankPrefix.eligible r st.known (st.queue.toArray.toVector.get P.node))
        (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card
    have hpoint : ∀ P ∈ paths, metric P ≤ 2 * Parameters.ballSize n r := by
      intro P hP
      have hshort := splitAll_short cfg r hnum st.paths P hP
      have hD := Reference.distanceScale_pos cfg hnum r
      have hbudget : (P.path.searchWeight cfg.inputScale : ℝ) +
          Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r) ≤
            Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r) := by
        unfold Early.nearRadius Early.searchRadius
        linarith
      have hm := relatedVertices_card_le P.path cfg.inputScale cfg.inputScale_pos (st.queue.toArray.toVector.get P.node)
        P.inside (RankPrefix.eligible r st.known (st.queue.toArray.toVector.get P.node))
        (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
        (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r)) (Parameters.ballSize n r) hbudget
        (st.ambient_balls hg hb P.node P.target).1 (st.ambient_balls hg hb P.node P.source).2
      have hround : Late.rounded cfg.inputScale
          (stored.restricted (StoredEdges.graphOfEdges input) (st.queue.toArray.toVector.get P.node)) =
            Backend.roundedRestricted stored input (st.queue.toArray.toVector.get P.node) cfg.inputScale := rfl
      have hmetric := congrArg (fun H =>
        (relatedVertices H P.path.vertices (RankPrefix.eligible r st.known (st.queue.toArray.toVector.get P.node))
          (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card) hround
      rw [hmetric] at hm
      exact hm
    have hsum : (paths.map metric).sum ≤ (paths.map fun _ => 2 * Parameters.ballSize n r).sum :=
      List.sum_le_sum hpoint
    simpa only [related, List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm] using hsum
  · simp only [State.primeRelated, State.primeCount, hg, ↓reduceIte, Nat.mul_zero, le_refl]

theorem root_meanRawZ (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) :
    meanRawZ cfg ps hnum stored input (rootState cfg stored input Q) 0 = 1 := by
  simp only [meanRawZ, pathStateLaw, Law.expect_pure, liftCount]
  rw [State.rawCount, if_pos (rootState_good cfg stored input Q)]
  have hlength : (rootState cfg stored input Q).paths.length = 1 := rfl
  rw [hlength, Nat.cast_one]

theorem root_meanZ_le (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) (W : ℕ)
    (hW : Q.searchWeight cfg.inputScale ≤ W) :
    meanZ cfg ps hnum stored input (rootState cfg stored input Q) 0 ≤
      1 + (W : ℝ) / Reference.distanceScale cfg 0 := by
  have hroot : weight cfg.inputScale (rootState cfg stored input Q).paths ≤ W := hW
  have h := meanZ_split cfg ps hnum stored input (rootState cfg stored input Q) W 0 hroot
  rwa [root_meanRawZ cfg ps hnum stored input Q] at h

theorem root_meanY_le (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (hn : 0 < n) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) :
    meanY cfg ps hnum stored input (rootState cfg stored input Q) 0 ≤
      2 * Parameters.ballSize n 0 * meanZ cfg ps hnum stored input (rootState cfg stored input Q) 0 := by
  simp only [meanY, meanZ, pathStateLaw, Law.expect_pure, liftCount]
  exact_mod_cast primeRelated_count hnum (rootState cfg stored input Q)
    (Parameters.ballSize_pos n hn 0 (Nat.zero_le _))

theorem root_meanZ_one (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (hn : 0 < n) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t) (W : ℕ)
    (hW : Q.searchWeight cfg.inputScale ≤ W) (hnumeric : EarlyNumerics n cfg ps 0) :
    meanZ cfg ps hnum stored input (rootState cfg stored input Q) 1 ≤
      (2 + 800 * cfg.k * cfg.logarithm) * meanZ cfg ps hnum stored input (rootState cfg stored input Q) 0 +
        (W : ℝ) / Reference.distanceScale cfg 1 := by
  have hroot : weight cfg.inputScale (rootState cfg stored input Q).paths ≤ W := hW
  have hz := meanZ_split cfg ps hnum stored input (rootState cfg stored input Q) W 1 hroot
  have hstep := meanRawZ_step cfg ps hnum stored input (rootState cfg stored input Q) 0 hnumeric
  have hy := root_meanY_le cfg ps hnum stored input hn Q
  have hz₀ := meanZ_nonneg cfg ps hnum stored input (rootState cfg stored input Q) 0
  have hyp := mul_le_mul_of_nonneg_left hy
    (show 0 ≤ 2 * (Ranks.rate ps 0).value from mul_nonneg (by norm_num) hnumeric.positive.le)
  have hbalance := mul_le_mul_of_nonneg_right hnumeric.balance
    (show 0 ≤ 4 * meanZ cfg ps hnum stored input (rootState cfg stored input Q) 0 by positivity)
  push_cast at hy hyp hz hstep hbalance ⊢
  linarith

end

end StreamingReachability.Hopset.Following
