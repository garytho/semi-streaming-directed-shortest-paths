module

public import StreamingSSSP.Hopset.FrozenAmplification
public import StreamingSSSP.Hopset.BackedPaths

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def StagePair (frozen committed : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hops low high : ℕ) (stretch : ℝ) (s t : Fin n) : Prop :=
  ∀ d : ℕ, (frozen.graph (StoredEdges.graphOfEdges input)).hopDist (2 * hops) s t = (d : Distance) →
    low ≤ d → d ≤ high → ShortRoute (committed.graph (StoredEdges.graphOfEdges input)) s t hops (stretch * d)

def StageQuality (frozen committed : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hops low high : ℕ) (stretch : ℝ) : Prop :=
  ∀ pair : Fin n × Fin n, StagePair frozen committed input hops low high stretch pair.1 pair.2

theorem stage_pair_failure (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (frozen : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ frozen.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ frozen.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (count : ℕ) (committed : Implicit.Representation n) (hc : committed.Extends frozen) (s t : Fin n) :
    (Builder.evaluate (Backend.guardedHandler input)
      (repeatTrials hn accuracy x ha (guesses n wmin wmax hwmin) frozen count committed)).prob (fun out =>
        ¬ StagePair frozen out input (Parameters.hopBound n accuracy x)
          (wmin * Parameters.queryUnit n accuracy x) (2 * n * wmax * Parameters.queryUnit n accuracy x)
          (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) s t) ≤ (1 / 2 : ℝ) ^ count := by
  let mu := Builder.evaluate (Backend.guardedHandler input)
    (repeatTrials hn accuracy x ha (guesses n wmin wmax hwmin) frozen count committed)
  let h := Parameters.hopBound n accuracy x
  let U := Parameters.queryUnit n accuracy x
  let stretch : ℝ := 1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)
  by_cases hex : ∃ d : ℕ, (frozen.graph (StoredEdges.graphOfEdges input)).hopDist (2 * h) s t = (d : Distance) ∧
      wmin * U ≤ d ∧ d ≤ 2 * n * wmax * U
  · obtain ⟨d, hd, hlo, hhi⟩ := hex
    have hf : (frozen.graph (StoredEdges.graphOfEdges input)).hopDist (2 * h) s t ≠ ⊤ := by
      rw [hd]
      exact WithTop.natCast_ne_top _
    obtain ⟨Q, hsimple, hlength, hcost⟩ := Late.exists_backed_hopPath (2 * h) s t hf
    have hm : Q.micro = d := by exact_mod_cast hcost.trans hd
    have hfailure := repeatTrials_shortens_failure hn hn₂ accuracy x wmin wmax ha hwmin frozen input Q hlength
      (by rw [hm]; exact hlo) (by rw [hm]; exact hhi) hs hp hsize hpoly count committed hc
    have hquality (out : Implicit.Representation n)
        (hq : ShortRoute (out.graph (StoredEdges.graphOfEdges input)) s t h (stretch * Q.micro)) :
        StagePair frozen out input h (wmin * U) (2 * n * wmax * U) stretch s t := by
      intro d' hd' _ _
      have heq : d' = Q.micro := by exact_mod_cast hd'.symm.trans hcost.symm
      simpa only [heq] using hq
    have hmono : mu.prob (fun out => ¬ StagePair frozen out input h (wmin * U) (2 * n * wmax * U) stretch s t) ≤
        mu.prob (fun out => ¬ ShortRoute (out.graph (StoredEdges.graphOfEdges input)) s t h (stretch * Q.micro)) :=
      mu.prob_mono (fun out hnot hq => hnot (hquality out hq))
    exact hmono.trans hfailure
  · have hquality (out : Implicit.Representation n) :
        StagePair frozen out input h (wmin * U) (2 * n * wmax * U) stretch s t := by
      intro d hd hlo hhi
      exact False.elim (hex ⟨d, hd, hlo, hhi⟩)
    have heq : (fun out : Implicit.Representation n =>
        ¬ StagePair frozen out input h (wmin * U) (2 * n * wmax * U) stretch s t) = fun _ => False := by
      funext out
      exact propext ⟨fun hn => hn (hquality out), False.elim⟩
    change mu.prob _ ≤ _
    rw [heq, Law.prob_false]
    positivity

theorem stage_quality_failure (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (frozen : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ frozen.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ frozen.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x)
    (count : ℕ) (committed : Implicit.Representation n) (hc : committed.Extends frozen) :
    (Builder.evaluate (Backend.guardedHandler input)
      (repeatTrials hn accuracy x ha (guesses n wmin wmax hwmin) frozen count committed)).prob (fun out =>
        ¬ StageQuality frozen out input (Parameters.hopBound n accuracy x)
          (wmin * Parameters.queryUnit n accuracy x) (2 * n * wmax * Parameters.queryUnit n accuracy x)
          (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ))) ≤ (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ count := by
  let mu := Builder.evaluate (Backend.guardedHandler input)
    (repeatTrials hn accuracy x ha (guesses n wmin wmax hwmin) frozen count committed)
  let bad := fun pair : Fin n × Fin n => fun out : Implicit.Representation n =>
    ¬ StagePair frozen out input (Parameters.hopBound n accuracy x)
      (wmin * Parameters.queryUnit n accuracy x) (2 * n * wmax * Parameters.queryUnit n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)) pair.1 pair.2
  have heq : mu.prob (fun out => ¬ StageQuality frozen out input (Parameters.hopBound n accuracy x)
      (wmin * Parameters.queryUnit n accuracy x) (2 * n * wmax * Parameters.queryUnit n accuracy x)
      (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ))) =
      mu.prob (fun out => ∃ pair ∈ (Finset.univ : Finset (Fin n × Fin n)), bad pair out) := by
    apply mu.prob_congr
    intro out
    simp only [StageQuality, bad, not_forall, Finset.mem_univ, true_and]
  change mu.prob _ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ pair ∈ (Finset.univ : Finset (Fin n × Fin n)), mu.prob (bad pair) := mu.finite_union _ _
    _ ≤ ∑ _pair ∈ (Finset.univ : Finset (Fin n × Fin n)), (1 / 2 : ℝ) ^ count := by
      apply Finset.sum_le_sum
      intro pair _
      exact stage_pair_failure hn hn₂ accuracy x wmin wmax ha hwmin frozen input hs hp hsize hpoly count committed hc pair.1 pair.2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

end

end StreamingSSSP.Hopset
