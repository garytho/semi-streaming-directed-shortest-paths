module

public import StreamingSSSP.Hopset.ReplayOutput
public import StreamingSSSP.Hopset.AuditEvents

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem full_success_le_code (hn : 0 < n) (accuracy x delta : ℕ)
    (ha : 0 < accuracy) (hd : 0 < delta) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) (P : Output n → Prop) :
    let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
    (fullAuditLaw cfg hn stored input).prob (fun sample =>
      FullResourceFit cfg stored input sample ∧ P (geometricOutput cfg stored input sample.1 sample.2)) ≤
      (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob (OutputSatisfies P) := by
  let cfg := Parameters.configuration n accuracy x delta (volume stored.blocks) ha hd
  let mu := fullAuditLaw cfg hn stored input
  let good := fun sample : (Fin n → ℕ) × List (GeometricEntry n cfg) =>
    ResourceFit cfg stored input (Vector.ofFn sample.1, sample.2.map GeometricEntry.erase) ∧
      P (geometricOutput cfg stored input sample.1 sample.2)
  let erasedGood := fun sample : Vector ℕ n × List (Entry n) =>
    ResourceFit cfg stored input sample ∧
      P (replay (globalState cfg stored input sample.1) sample.2).output
  have hstop : mu.prob (fun sample =>
      FullResourceFit cfg stored input sample ∧ P (geometricOutput cfg stored input sample.1 sample.2)) ≤
      mu.prob (fun sample => good (sample.1, stopTrace cfg stored input sample.2)) := by
    apply mu.prob_mono
    intro sample h
    have he := (stopTrace_eq_iff cfg stored input sample.2).mpr h.1.1
    exact ⟨by simpa only [he] using h.1.2, by simpa only [he] using h.2⟩
  have heq : mu.prob (fun sample => good (sample.1, stopTrace cfg stored input sample.2)) =
      (auditLaw cfg hn stored input).prob erasedGood := by
    calc
      _ = (geometricAuditLaw cfg hn stored input).prob good :=
        fullAudit_stopped_probability cfg hn stored input good
      _ = _ := geometricAudit_erase_probability cfg hn stored input erasedGood
  have haccept : (auditLaw cfg hn stored input).prob erasedGood ≤
      (auditLaw cfg hn stored input).prob (fun sample =>
        sample.2.length = cfg.maximumLevel + 1 ∧ AcceptedTrace cfg (globalState cfg stored input sample.1) sample.2 ∧
          P (replay (globalState cfg stored input sample.1) sample.2).output) := by
    apply prob_mono_supported
    refine Early.Sampling.holds_mono (audit_valid cfg hn stored input) ?_
    intro sample hvalid h
    exact ⟨h.1.1, resourceFit_accepted n hn accuracy x delta ha hd stored input hs hp hsize hpoly sample hvalid h.1, h.2⟩
  change mu.prob _ ≤ _
  exact hstop.trans (heq.le.trans (haccept.trans
    (audit_success_le_code cfg hn stored input
      (Parameters.initial_copies_fit n accuracy x delta (volume stored.blocks) ha hd) hs hp hsize P)))

end

end StreamingSSSP.Hopset.Batched
