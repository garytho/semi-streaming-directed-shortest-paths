module

public import StreamingReachability.Approx.MeasuredProgram

@[expose] public section

namespace StreamingReachability.Approx.Measured

open scoped Classical
open Hopset
open Hopset.Measured

variable {n : ℕ} {E : Type*}

theorem extraction_catalog (stored : Implicit.Representation n) (scale radius : ℕ) (source : Fin n) :
    Core.Live.catalogCells (queryCatalog stored scale radius source) stored.explicit =
      4 * (stored.blocks.length + 3) + 3 * stored.explicit.length + 2 * volume stored.blocks + 2 * n := by
  unfold Core.Live.catalogCells
  rw [vector_volume (queryCatalog stored scale radius source).blocks,
    vector_volume (queryCatalog stored scale radius source).sets]
  simp only [queryCatalog, setVolume, Array.toVector, Vector.toList_mk, List.toList_toArray,
    Vector.toList_replicate, volume, List.map_replicate, List.sum_replicate, Finset.card_univ, Fintype.card_fin]
  ring

theorem extraction_bounds {G : Graph (Fin n)} (hn : 0 < n)
    (accuracy x total weight scale count delta : ℕ) (hd : 0 < delta) (source : Fin n)
    (stored : Implicit.Representation n) (h : StoreBounds G accuracy x total weight count stored)
    (hc : count ≤ total) (hdelta : delta ≤ scale) :
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
      (storeCatalogLimit n accuracy total) scale weight
      (queryRequest stored x delta (8 * Parameters.queryUnit n accuracy x) source) (n + volume stored.blocks) := by
  have hcopy : n ≤ copyLimit n := by
    have he : 1 ≤ Parameters.ell n ^ 4 := by
      change 0 < Parameters.ell n ^ 4
      have hp := Parameters.ell_pos n
      positivity
    unfold copyLimit
    nlinarith
  have hv := h.volume_le.trans (Nat.mul_le_mul_right _ hc)
  have hh := h.headers_le.trans (Nat.mul_le_mul_right _ hc)
  have hs := h.stars_le.trans (Nat.mul_le_mul_right _ hc)
  have hfactor : 1 ≤ recordFactor n accuracy := by
    change 0 < recordFactor n accuracy
    unfold recordFactor
    have hk : 0 < Parameters.k n := by have hh := Parameters.k_large n; omega
    have he := Parameters.ell_pos n
    positivity
  refine ⟨rfl, ?_, ?_, ?_, hd, hdelta, h.valid.positive, h.weights,
    queryCatalog_small stored x delta _ source h.valid.blocks⟩
  · simp [Core.BatchAPI.Request.radius, Core.BatchAPI.Request.ofCatalog, queryRequest, queryCatalog]
  · unfold recordLimit
    exact (Nat.add_le_add_left hv n).trans (Nat.le_mul_of_pos_left _ hfactor)
  · change Core.Live.catalogCells (queryCatalog stored delta _ source) stored.explicit ≤ _
    rw [extraction_catalog]
    unfold storeCatalogLimit
    omega

structure ExtractionFits (Q : Core.BatchAPI.Request n → ℕ → Prop) (limit count : ℕ)
    (out : Report n (Labels n)) : Prop where
  passes_le : out.passes ≤ count * limit
  calls_le : out.calls.length ≤ count
  draws_empty : out.draws = []
  calls_valid : ∀ call ∈ out.calls, Q call.request call.allowance

theorem extract_resources {G : Graph (Fin n)} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy x total weight scale count : ℕ)
    (source : Fin n) (stored : Implicit.Representation n)
    (h : StoreBounds G accuracy x total weight count stored) (hc : count ≤ total)
    (hp : ∀ e ∈ (input.filterMap (microViewed (Parameters.queryUnit n accuracy x) view) ++
      auxiliary.map (microMap (Parameters.queryUnit n accuracy x))), 0 < e.weight)
    (deltas : List {delta : ℕ // 0 < delta}) (hd : ∀ delta ∈ deltas, delta.val ≤ scale) (answer : Labels n) :
    Early.Sampling.Holds (evaluate view input auxiliary (extractGuesses accuracy x source stored deltas answer))
      (ExtractionFits
        (QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
          (storeCatalogLimit n accuracy total) scale weight)
        (passLimit n x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)) deltas.length) := by
  let Q : Core.BatchAPI.Request n → ℕ → Prop :=
    QueryBounds x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
      (storeCatalogLimit n accuracy total) scale weight
  let limit := passLimit n x (8 * Parameters.queryUnit n accuracy x) (recordLimit n accuracy total)
  let U := Parameters.queryUnit n accuracy x
  induction deltas generalizing answer with
  | nil =>
      exact Early.Sampling.holds_pure _ _ ⟨by simp, by simp, rfl, by simp⟩
  | cons delta deltas ih =>
      let request := queryRequest stored x delta.val (8 * U) source
      let first := Hopset.Measured.auxiliaryHandler (microViewed U view) input (auxiliary.map (microMap U))
        request (n + volume stored.blocks)
      let nextAnswer := match first.result with
        | none => answer
        | some reply => Vector.ofFn (fun v => min (answer.get v) (decoded U delta.val reply v))
      have hq : Q request (n + volume stored.blocks) :=
        extraction_bounds hn accuracy x total weight scale count delta.val delta.property source stored h hc
          (hd delta (by simp))
      have hpass : first.passes ≤ limit := hq.passes hn (microViewed U view) input (auxiliary.map (microMap U)) hp
      have htail := ih (fun d hm => hd d (List.mem_cons_of_mem delta hm)) nextAnswer
      change Early.Sampling.Holds
        ((evaluate view input auxiliary (extractGuesses accuracy x source stored deltas nextAnswer)).map first.then) _
      refine Early.Sampling.holds_map htail first.then _ ?_
      intro out ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · change first.passes + out.passes ≤ (delta :: deltas).length * limit
        have ht := ho.passes_le
        simp only [List.length_cons]
        nlinarith
      · change (first.calls ++ out.calls).length ≤ (delta :: deltas).length
        have hf : first.calls.length = 1 := rfl
        have ht := ho.calls_le
        rw [List.length_append, hf, List.length_cons]
        omega
      · change first.draws ++ out.draws = []
        rw [ho.draws_empty]
        rfl
      · intro call hm
        rcases List.mem_append.mp hm with hm | hm
        · have he : call = ⟨request, n + volume stored.blocks, first.passes⟩ := List.mem_singleton.mp hm
          simpa only [he] using hq
        · exact ho.calls_valid call hm

end StreamingReachability.Approx.Measured
