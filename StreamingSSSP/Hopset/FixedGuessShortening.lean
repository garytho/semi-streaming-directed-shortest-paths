module

public import StreamingSSSP.Hopset.RootShortening
public import StreamingSSSP.Hopset.FullCodeTransfer

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical
open Batched Following

noncomputable section

variable {n : ℕ}

def PathShortcut (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    {s t : Fin n} (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (scale hops : ℕ) (debtBudget : ℝ) (out : Output n) : Prop :=
  ∃ debt : ℕ, (debt : ℝ) ≤ debtBudget ∧
    ∃ T : Late.Route ((commit stored out).graph (StoredEdges.graphOfEdges input))
        s t (scale * (Q.searchWeight scale + debt)), T.hops ≤ hops

theorem fixedGuess_shortens (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges input) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 17 / 256 ≤
      (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob
        (OutputSatisfies (PathShortcut stored input Q delta (Parameters.hopBound n accuracy x)
          ((Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy))) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let hnum : 0 < cfg.initialNumerator := Parameters.initialNumerator_pos n accuracy x ha
  let root := rootState cfg stored input Q
  let mu := fullAuditLaw cfg hn stored input
  let P := PathShortcut stored input Q delta (Parameters.hopBound n accuracy x)
    ((Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy)
  have hx : 0 < x := by
    have hk : 0 < Parameters.k n := by have h := Parameters.k_large n; omega
    have he := Parameters.ell_pos n
    exact lt_of_lt_of_le (by positivity : 0 < 4 * 100 * Parameters.k n * Parameters.ell n) hpoly
  have hevent : 1 - 17 / 256 ≤ mu.prob (PathEvent cfg hn hnum accuracy stored input root) :=
    full_path_event hn hn₂ accuracy x delta ha hd stored input Q hweight hs hp hsize
  have hgood : mu.prob (PathEvent cfg hn hnum accuracy stored input root) ≤
      mu.prob (fun sample => FullResourceFit cfg stored input sample ∧
        P (geometricOutput cfg stored input sample.1 sample.2)) := by
    apply prob_mono_supported
    refine Early.Sampling.holds_mono (fullAudit_valid cfg hn hnum stored input hs hp hsize) ?_
    intro sample hvalid he
    obtain ⟨run, hentries⟩ := hvalid.execution
    let F := (commit stored (geometricOutput cfg stored input sample.1 sample.2)).graph (StoredEdges.graphOfEdges input)
    have hroute := calibrated_root_route hn accuracy x delta (volume stored.blocks) ha hd hx stored input Q hweight
      hs hp hsize sample.1 sample.2 run hentries he F
      (geometricOutput_old cfg stored input sample.1 sample.2)
      (fun entry he e hee => geometricOutput_frame_edge cfg stored input sample.1 sample.2 entry he e hee)
      (fun B hB => geometricOutput_frame_block cfg stored input sample.1 sample.2 B hB)
      (fun e he => geometricOutput_global_edge cfg stored input sample.1 sample.2 e he)
    exact ⟨he.1, hroute⟩
  change 1 - 17 / 256 ≤ (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob (OutputSatisfies P)
  exact hevent.trans (hgood.trans (full_success_le_code hn accuracy x delta ha hd stored input hs hp hsize hpoly P))

theorem fixedGuess_viewed_shortens {E : Type*} (view : E → Option (StoredEdges.Edge n))
    (input : List E) (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n) {s t : Fin n}
    (Q : Late.Path stored (StoredEdges.graphOfEdges (input.filterMap view)) s t)
    (hweight : Q.searchWeight delta ≤ 3 * Parameters.queryUnit n accuracy x)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input.filterMap view, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    1 - 17 / 256 ≤
      (Code.evaluate (Backend.guardedViewedHandler view input) (fixedGuess cfg hn stored)).prob
        (OutputSatisfies (PathShortcut stored (input.filterMap view) Q delta (Parameters.hopBound n accuracy x)
          ((Parameters.queryUnit n accuracy x : ℝ) / Parameters.accuracyDenominator n accuracy))) := by
  dsimp only
  rw [Backend.guardedViewedHandler_eq]
  exact fixedGuess_shortens hn hn₂ accuracy x delta ha hd stored _ Q hweight hs hp hsize hpoly

end

end StreamingSSSP.Hopset
