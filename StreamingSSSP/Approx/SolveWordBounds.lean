module

public import StreamingSSSP.Approx.OutputWordBounds

@[expose] public section

namespace StreamingSSSP.Approx.Measured

open scoped Classical
open Hopset
open Hopset.Measured

variable {n : ℕ} {E : Type*}

theorem solve_words (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy x confidence : ℕ)
    (ha : 0 < accuracy) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight) :
    Early.Sampling.Holds (evaluate view input auxiliary (solve hn accuracy x confidence ha source))
      (fun out => LabelsWords
        (8 * guessScale n (scanAuxiliary view input auxiliary).minWeight (scanAuxiliary view input auxiliary).maximum)
        out.result) := by
  let bounds := scanAuxiliary view input auxiliary
  let count := executionCount n confidence bounds.minWeight bounds.maximum
  let scale := guessScale n bounds.minWeight bounds.maximum
  let weight := physicalWeight n accuracy x bounds.minWeight bounds.maximum
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count)
      (storeCatalogLimit n accuracy count) scale weight
  let U := Parameters.queryUnit n accuracy x
  let micro := input.filterMap (microViewed U view) ++ auxiliary.map (microMap U)
  have hb : bounds.Valid (input.filterMap view ++ auxiliary) := by
    change (scanAuxiliary view input auxiliary).Valid _
    rw [scanAuxiliary_eq]
    exact scan_valid _ hp
  have hmin := hb.minWeight_pos
  have hscanMin : 0 < (scanAuxiliary view input auxiliary).minWeight := hmin
  have hU := Parameters.queryUnit_pos n accuracy x ha
  have hmicro : ∀ e ∈ micro, 0 < e.weight := by
    have he : micro = (input.filterMap view ++ auxiliary).filterMap (microView U) := by
      simp only [micro, microViewed_filterMap, List.filterMap_append, microView_list]
    rw [he]
    exact microView_positive U hU _ hp
  let build := construct hn accuracy x confidence bounds.minWeight bounds.maximum ha hmin (emptyRepresentation n)
  have hc : BuilderCertificate micro Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n)
      build count (StoreBounds (StoredEdges.graphOfEdges micro) accuracy x count weight count) :=
    construct_certificate hn accuracy x confidence bounds.minWeight bounds.maximum ha hmin micro hmicro
  have hbuild := builder_certificate_holds (microViewed U view) input (auxiliary.map (microMap U))
    Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n) build count _ hc
  change Early.Sampling.Holds _ (fun out : Report n (Labels n) => LabelsWords (8 * scale) out.result)
  simp only [solve, evaluate, hscanMin, ↓reduceDIte]
  refine Early.Sampling.holds_map ?_ metadata _ (fun out ho => ho)
  refine Reference.holds_bind_on _ _ _ _ hbuild ?_
  intro first hf
  have hextract := extract_words view input auxiliary hn accuracy x count weight scale count ha source first.result
    hf.post hmicro (guesses n bounds.minWeight bounds.maximum hmin)
    (guesses_scale n bounds.minWeight bounds.maximum hmin) (Vector.replicate n ⊤)
    (by intro v; exact Or.inl (by simp))
  exact Early.Sampling.holds_map hextract first.then _ (fun out ho => ho)

end StreamingSSSP.Approx.Measured
