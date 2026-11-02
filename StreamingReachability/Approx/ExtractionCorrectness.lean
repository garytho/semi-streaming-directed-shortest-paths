module

public import StreamingReachability.Approx.Extraction
public import StreamingReachability.Exact.Main

@[expose] public section

namespace StreamingReachability.Approx

open scoped Classical
open Hopset

noncomputable section

variable {n : ℕ}

def Accurate (input : List (StoredEdges.Edge n)) (source : Fin n) (accuracy : ℕ) (answer : Labels n) : Prop :=
  (∀ v, (StoredEdges.graphOfEdges input).dist source v ≤ answer.get v) ∧
    ∀ v (d : ℕ), (StoredEdges.graphOfEdges input).dist source v = (d : Distance) →
      ∃ q : ℕ, answer.get v = (q : Distance) ∧ d ≤ q ∧ accuracy * q ≤ (accuracy + 1) * d

theorem extractResult_lower (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hsound : stored.Sound (StoredEdges.graphOfEdges (input.filterMap (microView (Parameters.queryUnit n accuracy x)))))
    (deltas : List {delta : ℕ // 0 < delta}) (answer : Labels n)
    (hanswer : ∀ v, (StoredEdges.graphOfEdges input).dist source v ≤ answer.get v) :
    ∀ v, (StoredEdges.graphOfEdges input).dist source v ≤
      (extractResult input accuracy x source stored deltas answer).get v := by
  induction deltas generalizing answer with
  | nil => exact hanswer
  | cons delta deltas ih =>
      apply ih
      intro v
      simp only [Vector.get_ofFn]
      exact le_min (hanswer v)
        (decoded_lower hn (Parameters.queryUnit n accuracy x) delta.val x (8 * Parameters.queryUnit n accuracy x)
          (Parameters.queryUnit_pos n accuracy x ha) delta.property input stored source v hp hs hsize hsound)

theorem guesses_have_member (n wmin wmax : ℕ) (hwmin : 0 < wmin) :
    ∃ delta, delta ∈ guesses n wmin wmax hwmin := by
  refine ⟨⟨wmin, hwmin⟩, ?_⟩
  apply List.mem_map.mpr
  exact ⟨0, List.mem_range.mpr (Nat.zero_lt_succ _), by apply Subtype.ext; simp only [pow_zero, Nat.mul_one]⟩

theorem extractResult_correct (hn : 0 < n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hmin : ∀ e ∈ input, wmin ≤ e.weight) (hmax : ∀ e ∈ input, e.weight ≤ wmax)
    (hhopset : IsImplicitHopset (input.filterMap (microView (Parameters.queryUnit n accuracy x))) stored
      (Parameters.hopBound n accuracy x) (1 + 1 / (5 * (accuracy : ℝ)))) :
    Accurate input source accuracy
      (extractResult input accuracy x source stored (guesses n wmin wmax hwmin) (Vector.replicate n ⊤)) := by
  let answer := extractResult input accuracy x source stored (guesses n wmin wmax hwmin) (Vector.replicate n ⊤)
  have hlower : ∀ v, (StoredEdges.graphOfEdges input).dist source v ≤ answer.get v :=
    extractResult_lower hn accuracy x ha input stored source hp hs hsize hhopset.1 _ _
      (by intro v; simp only [Vector.get_replicate]; exact le_top)
  refine ⟨hlower, ?_⟩
  intro v d hd
  by_cases hv : v = source
  · subst v
    have hd0 : d = 0 := by
      have h : (0 : Distance) = (d : Distance) := by simpa only [Graph.dist_self] using hd
      exact_mod_cast h.symm
    subst d
    obtain ⟨delta, hdelta⟩ := guesses_have_member n wmin wmax hwmin
    have h := extractResult_hit input accuracy x source stored _ delta hdelta (Vector.replicate n ⊤) source
    rw [candidate_source hn accuracy x delta.val ha delta.property input stored source hp hs hsize] at h
    exact ⟨0, le_antisymm h bot_le, Nat.zero_le _, by simp⟩
  · have hG : ∀ u v, u ≠ v → (wmin : Distance) ≤ StoredEdges.graphOfEdges input u v := by
      intro u v _
      exact (StoredEdges.le_graphOfEdges_iff input u v _).mpr
        (fun e he _ _ => WithTop.coe_le_coe.mpr (hmin e he))
    have hlo : wmin ≤ d := by
      have h := (StoredEdges.graphOfEdges input).dist_lower_bound wmin hG (Ne.symm hv)
      rw [hd] at h
      exact WithTop.coe_le_coe.mp h
    have hbound := Exact.dist_bound _ wmax (Exact.edge_list_weightsBounded input wmax hmax) hd
    have hupper : d ≤ 2 * n * wmax := by
      have hm := Nat.mul_le_mul_left wmax (Nat.sub_le n 1)
      simp only [Fintype.card_fin] at hbound
      nlinarith
    obtain ⟨delta, hdelta, hdlo, hdhi⟩ := guesses_cover_scaled n wmin wmax 1 d hwmin (by decide)
      (by simpa only [Nat.mul_one] using hlo) (by simpa only [Nat.mul_one] using hupper)
    simp only [Nat.mul_one] at hdlo hdhi
    obtain ⟨candidateValue, hc, hclow, hcaccuracy⟩ := decoded_upper hn accuracy x delta.val ha delta.property
      input stored source v hp hs hsize hhopset d hd hdlo hdhi
    have hhit := extractResult_hit input accuracy x source stored _ delta hdelta (Vector.replicate n ⊤) v
    change answer.get v ≤ candidate input accuracy x stored source delta.val v at hhit
    rw [show candidate input accuracy x stored source delta.val v = (candidateValue : Distance) from hc] at hhit
    obtain ⟨q, hq, hqBound⟩ := Exact.finite_of_le hhit
    have hlow : d ≤ q := by
      have h := hlower v
      rw [hd, hq] at h
      exact WithTop.coe_le_coe.mp h
    exact ⟨q, hq, hlow, (Nat.mul_le_mul_left accuracy hqBound).trans hcaccuracy⟩

theorem extraction_correct (hn : 0 < n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hmin : ∀ e ∈ input, wmin ≤ e.weight) (hmax : ∀ e ∈ input, e.weight ≤ wmax)
    (hhopset : IsImplicitHopset (input.filterMap (microView (Parameters.queryUnit n accuracy x))) stored
      (Parameters.hopBound n accuracy x) (1 + 1 / (5 * (accuracy : ℝ)))) :
    Early.Sampling.Holds
      (Program.evaluate input (extractGuesses accuracy x source stored (guesses n wmin wmax hwmin) (Vector.replicate n ⊤)))
      (Accurate input source accuracy) := by
  refine Early.Sampling.holds_mono (extract_evaluate hn accuracy x ha input stored source hp hs hsize _ _) ?_
  intro result heq
  rw [heq]
  exact extractResult_correct hn accuracy x wmin wmax ha hwmin input stored source hp hs hsize hmin hmax hhopset

end

end StreamingReachability.Approx
