module

public import StreamingReachability.Hopset.GuessCoverage
public import StreamingReachability.Hopset.Extension

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical
open Batched

noncomputable section

variable {n : ℕ}

def ShortRoute (F : Graph (Fin n)) (s t : Fin n) (hops : ℕ) (budget : ℝ) : Prop :=
  ∃ cost : ℕ, (cost : ℝ) ≤ budget ∧ ∃ P : Late.Route F s t cost, P.hops ≤ hops

theorem ShortRoute.mono_graph {F H : Graph (Fin n)} {s t : Fin n} {hops : ℕ} {budget : ℝ}
    (h : ShortRoute F s t hops budget) (hF : ∀ u v, H u v ≤ F u v) : ShortRoute H s t hops budget := by
  obtain ⟨cost, hc, P, hh⟩ := h
  exact ⟨cost, hc, P.mono hF, by simpa only [Late.Route.hops_mono] using hh⟩

theorem ShortRoute.mono_budget {F : Graph (Fin n)} {s t : Fin n} {hops : ℕ} {a b : ℝ}
    (h : ShortRoute F s t hops a) (hab : a ≤ b) : ShortRoute F s t hops b := by
  obtain ⟨cost, hc, P, hh⟩ := h
  exact ⟨cost, hc.trans hab, P, hh⟩

def RelativeShortcut (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    {s t : Fin n} (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hops : ℕ) (stretch : ℝ) (out : Output n) : Prop :=
  ShortRoute ((commit stored out).graph (StoredEdges.graphOfEdges input)) s t hops (stretch * Q.micro)

theorem fixedGuess_relative (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hlength : Q.length ≤ 2 * Parameters.hopBound n accuracy x)
    (hlower : delta * Parameters.queryUnit n accuracy x ≤ Q.micro)
    (hupper : Q.micro < 2 * delta * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (1 / 2 : ℝ) ≤
      (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob
        (OutputSatisfies (RelativeShortcut stored input Q (Parameters.hopBound n accuracy x)
          (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ)))) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let mu := Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)
  let P := PathShortcut stored input Q delta (Parameters.hopBound n accuracy x)
    ((Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy)
  let R := RelativeShortcut stored input Q (Parameters.hopBound n accuracy x)
    (1 + 2 / (Parameters.accuracyDenominator n accuracy : ℝ))
  have hweight := Q.searchWeight_le_three_unit delta (Parameters.hopBound n accuracy x)
    (Parameters.queryUnit n accuracy x) hd hlength (Parameters.two_hops_le_unit n accuracy x ha) hupper.le
  have hraw : 1 - 17 / 256 ≤ mu.prob (OutputSatisfies P) :=
    fixedGuess_shortens hn hn₂ accuracy x delta ha hd stored input Q hweight hs hp hsize hpoly
  have hm : mu.prob (OutputSatisfies P) ≤ mu.prob (OutputSatisfies R) := by
    apply mu.prob_mono
    intro result h
    cases result with
    | none => exact False.elim h
    | some out =>
        obtain ⟨debt, hdebt, path, hh⟩ := h
        exact ⟨delta * (Q.searchWeight delta + debt),
          relative_search_budget accuracy x delta ha hd Q hlength hlower debt hdebt, path, hh⟩
  change (1 / 2 : ℝ) ≤ mu.prob (OutputSatisfies R)
  exact (by norm_num : (1 / 2 : ℝ) ≤ 1 - 17 / 256).trans (hraw.trans hm)

end

end StreamingReachability.Hopset
