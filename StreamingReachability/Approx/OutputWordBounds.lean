module

public import StreamingReachability.Approx.SolveResources

@[expose] public section

namespace StreamingReachability.Approx.Measured

open scoped Classical
open Hopset
open Hopset.Measured

variable {n : ℕ} {E : Type*}

theorem lookup_words (reply : Core.BatchAPI.SparseReply n) (R : ℕ)
    (h : ∀ record ∈ reply, record.distance ≤ R) (query : ℕ) (v : Fin n) :
    Core.WordBounds.Bounded R (Core.BatchAPI.lookup reply query v) := by
  induction reply with
  | nil => exact Or.inl rfl
  | cons record reply ih =>
      by_cases hm : record.queryId = query ∧ record.vertex = v
      · right
        simp only [Core.BatchAPI.lookup, hm, ↓reduceIte]
        exact (min_le_left _ _).trans (WithTop.coe_le_coe.mpr (h record (by simp)))
      · simp only [Core.BatchAPI.lookup, hm, ↓reduceIte]
        exact ih (fun r hr => h r (List.mem_cons_of_mem record hr))

theorem decoded_words (unit scale : ℕ) (hunit : 0 < unit) (reply : Core.BatchAPI.SparseReply n)
    (h : ∀ record ∈ reply, record.distance ≤ 8 * unit) (v : Fin n) :
    Core.WordBounds.Bounded (8 * scale) (decoded unit scale reply v) := by
  have hb := lookup_words reply (8 * unit) h 0 v
  rcases hb with ht | hb
  · exact Or.inl (by simp [decoded, ht])
  · obtain ⟨d, hd, hdb⟩ := Exact.finite_of_le hb
    right
    simp only [decoded, hd]
    apply WithTop.coe_le_coe.mpr
    apply Nat.div_le_of_le_mul
    have hm := Nat.mul_le_mul_left scale hdb
    nlinarith only [hm]

def LabelsWords (bound : ℕ) (answer : Labels n) : Prop :=
  ∀ v, Core.WordBounds.Bounded bound (answer.get v)

theorem min_words (bound : ℕ) (answer : Labels n) (unit scale : ℕ) (hunit : 0 < unit)
    (reply : Core.BatchAPI.SparseReply n) (hreply : ∀ record ∈ reply, record.distance ≤ 8 * unit)
    (hanswer : LabelsWords bound answer) (hscale : 8 * scale ≤ bound) :
    LabelsWords bound (Vector.ofFn (fun v => min (answer.get v) (decoded unit scale reply v))) := by
  intro v
  simp only [Vector.get_ofFn]
  exact Core.WordBounds.min_bounded (hanswer v)
    (Core.WordBounds.bounded_mono hscale (decoded_words unit scale hunit reply hreply v))

theorem extract_words {G : Graph (Fin n)} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy x total weight scale count : ℕ)
    (ha : 0 < accuracy) (source : Fin n) (stored : Implicit.Representation n)
    (h : StoreBounds G accuracy x total weight count stored)
    (hp : ∀ e ∈ input.filterMap (microViewed (Parameters.queryUnit n accuracy x) view) ++
      auxiliary.map (microMap (Parameters.queryUnit n accuracy x)), 0 < e.weight)
    (deltas : List {delta : ℕ // 0 < delta}) (hd : ∀ delta ∈ deltas, delta.val ≤ scale)
    (answer : Labels n) (hanswer : LabelsWords (8 * scale) answer) :
    Early.Sampling.Holds (evaluate view input auxiliary (extractGuesses accuracy x source stored deltas answer))
      (fun out => LabelsWords (8 * scale) out.result) := by
  let U := Parameters.queryUnit n accuracy x
  let micro := input.filterMap (microViewed U view) ++ auxiliary.map (microMap U)
  have hU := Parameters.queryUnit_pos n accuracy x ha
  induction deltas generalizing answer with
  | nil => exact Early.Sampling.holds_pure _ _ hanswer
  | cons delta deltas ih =>
      let request := queryRequest stored x delta.val (8 * U) source
      let first := auxiliaryHandler (microViewed U view) input (auxiliary.map (microMap U)) request (n + volume stored.blocks)
      have hresult : first.result = some (Core.BatchAPI.run request micro).records := by
        change (match (Core.BatchAPI.runGuardedMeasuredAuxiliary request (n + volume stored.blocks)
          (microViewed U view) input (auxiliary.map (microMap U))).result with
          | .error _ => none | .ok result => some result.records) = _
        rw [Core.BatchAPI.runGuardedMeasuredAuxiliary_eq, Core.BatchAPI.runGuardedMeasured_erases,
          query_noAbort hn stored micro x delta.val (8 * U) source h.valid.positive hp delta.property h.valid.blocks]
      have hrec : ∀ record ∈ (Core.BatchAPI.run request micro).records, record.distance ≤ 8 * U := by
        intro record hm
        have hr := raw_record_radius hn request micro record hm
        have he : request.radius = 8 * U := by
          simp [request, queryRequest, queryCatalog, Core.BatchAPI.Request.radius, Core.BatchAPI.Request.ofCatalog]
        exact hr.trans_eq he
      let next := Vector.ofFn (fun v => min (answer.get v) (decoded U delta.val (Core.BatchAPI.run request micro).records v))
      have hnext : LabelsWords (8 * scale) next :=
        min_words _ answer U delta.val hU _ hrec hanswer (Nat.mul_le_mul_left 8 (hd delta (by simp)))
      have ht := ih (fun d hm => hd d (List.mem_cons_of_mem delta hm)) next hnext
      change Early.Sampling.Holds
        ((evaluate view input auxiliary
          (extractGuesses accuracy x source stored deltas
            (match first.result with
            | none => answer
            | some reply => Vector.ofFn (fun v => min (answer.get v) (decoded U delta.val reply v))))).map first.then) _
      rw [hresult]
      exact Early.Sampling.holds_map ht first.then _ (fun out ho => ho)

theorem label_payload (bound : ℕ) (answer : Labels n) (h : LabelsWords bound answer) (v : Fin n) :
    (answer.get v).untopD 0 ≤ bound := by
  rcases h v with ht | hb
  · simp [ht]
  · have hf : answer.get v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hb
    exact WithTop.coe_le_coe.mp ((Core.distance_coe_untop hf).le.trans hb)

end StreamingReachability.Approx.Measured
