module

public import StreamingReachability.Approx.ExtractionResources

@[expose] public section

namespace StreamingReachability.Approx.Measured

open scoped Classical
open Hopset
open Hopset.Measured

variable {n : ℕ} {E : Type*}

structure SolveFits (Q : Core.BatchAPI.Request n → ℕ → Prop) (limit calls draws word : ℕ)
    (out : Report n (Labels n)) : Prop where
  passes_le : out.passes ≤ 1 + calls * limit
  calls_le : out.calls.length ≤ calls
  draws_le : out.draws.length ≤ draws
  calls_valid : ∀ call ∈ out.calls, Q call.request call.allowance
  draws_valid : ∀ draw ∈ out.draws, draw.bound ≤ word

def solveCallLimit (n confidence wmin wmax : ℕ) : ℕ :=
  executionCount n confidence wmin wmax * callLimit n + (guessExponent n wmin wmax + 1)

theorem solve_resources (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy x confidence : ℕ)
    (ha : 0 < accuracy) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight) :
    let bounds := scanAuxiliary view input auxiliary
    let count := executionCount n confidence bounds.minWeight bounds.maximum
    let scale := guessScale n bounds.minWeight bounds.maximum
    let weight := physicalWeight n accuracy x bounds.minWeight bounds.maximum
    Early.Sampling.Holds (evaluate view input auxiliary (solve hn accuracy x confidence ha source))
      (SolveFits (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count)
        (storeCatalogLimit n accuracy count) scale weight)
        (passLimit n x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count))
        (solveCallLimit n confidence bounds.minWeight bounds.maximum)
        (count * drawLimit n accuracy x) (randomLimit n accuracy x)) := by
  let bounds := scanAuxiliary view input auxiliary
  let count := executionCount n confidence bounds.minWeight bounds.maximum
  let scale := guessScale n bounds.minWeight bounds.maximum
  let weight := physicalWeight n accuracy x bounds.minWeight bounds.maximum
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count)
      (storeCatalogLimit n accuracy count) scale weight
  let limit := passLimit n x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy count)
  let calls := solveCallLimit n confidence bounds.minWeight bounds.maximum
  let U := Parameters.queryUnit n accuracy x
  let micro := input.filterMap (microViewed U view) ++ auxiliary.map (microMap U)
  have hb : bounds.Valid (input.filterMap view ++ auxiliary) := by
    change (scanAuxiliary view input auxiliary).Valid (input.filterMap view ++ auxiliary)
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
  have hactual := builder_actual (microViewed U view) input (auxiliary.map (microMap U)) build
  have hboth : Early.Sampling.Holds
      (Hopset.Measured.builder (Hopset.Measured.auxiliaryHandler (microViewed U view) input (auxiliary.map (microMap U))) build)
      (fun first => BuilderFits Q (randomLimit n accuracy x) (drawLimit n accuracy x) (callLimit n) count
        (StoreBounds (StoredEdges.graphOfEdges micro) accuracy x count weight count) first ∧
          Actual (microViewed U view) input (auxiliary.map (microMap U)) first) :=
    fun z hz => ⟨hbuild z hz, hactual z hz⟩
  change Early.Sampling.Holds _ (SolveFits Q limit calls (count * drawLimit n accuracy x) (randomLimit n accuracy x))
  simp only [solve, evaluate, hscanMin, ↓reduceDIte]
  refine Early.Sampling.holds_map ?_ metadata _ (fun out ho => ho)
  refine Reference.holds_bind_on _ _ _ _ hboth ?_
  intro first hf
  have hpass : first.passes ≤ (count * callLimit n) * limit := hf.1.passes (microViewed U view) input
    (auxiliary.map (microMap U)) hn hf.2 hmicro
  let deltas := guesses n bounds.minWeight bounds.maximum hmin
  have hextract := extract_resources view input auxiliary hn accuracy x count weight scale count source first.result
    hf.1.post (le_refl count) hmicro deltas (guesses_scale n bounds.minWeight bounds.maximum hmin) (Vector.replicate n ⊤)
  refine Early.Sampling.holds_map hextract first.then _ ?_
  intro last hl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change first.passes + last.passes + 1 ≤ 1 + calls * limit
    have ht := hl.passes_le
    have he : deltas.length = guessExponent n bounds.minWeight bounds.maximum + 1 := guesses_length _ _ _ _
    dsimp only [calls, solveCallLimit]
    rw [← he]
    nlinarith
  · change (first.calls ++ last.calls).length ≤ calls
    rw [List.length_append]
    have hfirst := hf.1.calls_le
    have hlast := hl.calls_le
    have he : count * callLimit n + deltas.length = calls := by
      dsimp only [calls, solveCallLimit, deltas, count]
      rw [guesses_length]
    exact (Nat.add_le_add hfirst hlast).trans_eq he
  · change (first.draws ++ last.draws).length ≤ count * drawLimit n accuracy x
    rw [List.length_append, hl.draws_empty]
    exact hf.1.draws_le
  · intro call hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.1.calls_valid call hm
    · exact hl.calls_valid call hm
  · intro draw hm
    have he : last.draws = [] := hl.draws_empty
    have hfresh : draw ∈ first.draws := by simpa only [metadata, Report.then, he, List.append_nil] using hm
    exact hf.1.draws_valid draw hfresh

end StreamingReachability.Approx.Measured
