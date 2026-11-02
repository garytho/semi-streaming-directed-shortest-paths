module

public import StreamingSSSP.Approx.DecodedUpper

@[expose] public section

namespace StreamingSSSP.Approx

open scoped Classical
open Hopset

variable {n : ℕ}

def candidate (input : List (StoredEdges.Edge n)) (accuracy x : ℕ) (stored : Implicit.Representation n)
    (source : Fin n) (scale : ℕ) (v : Fin n) : Distance :=
  let unit := Parameters.queryUnit n accuracy x
  decoded unit scale
    (Core.BatchAPI.run (queryRequest stored x scale (8 * unit) source) (input.filterMap (microView unit))).records v

def extractResult (input : List (StoredEdges.Edge n)) (accuracy x : ℕ) (source : Fin n)
    (stored : Implicit.Representation n) : List {delta : ℕ // 0 < delta} → Labels n → Labels n
  | [], answer => answer
  | delta :: rest, answer =>
      extractResult input accuracy x source stored rest
        (Vector.ofFn (fun v => min (answer.get v) (candidate input accuracy x stored source delta.val v)))

theorem extractResult_decreases (input : List (StoredEdges.Edge n)) (accuracy x : ℕ) (source : Fin n)
    (stored : Implicit.Representation n) (deltas : List {delta : ℕ // 0 < delta}) (answer : Labels n) (v : Fin n) :
    (extractResult input accuracy x source stored deltas answer).get v ≤ answer.get v := by
  induction deltas generalizing answer with
  | nil => exact le_rfl
  | cons delta deltas ih =>
      have hm := min_le_left (answer.get v) (candidate input accuracy x stored source delta.val v)
      exact (ih _).trans (by simpa only [Vector.get_ofFn] using hm)

theorem extractResult_hit (input : List (StoredEdges.Edge n)) (accuracy x : ℕ) (source : Fin n)
    (stored : Implicit.Representation n) (deltas : List {delta : ℕ // 0 < delta})
    (delta : {delta : ℕ // 0 < delta}) (hdelta : delta ∈ deltas) (answer : Labels n) (v : Fin n) :
    (extractResult input accuracy x source stored deltas answer).get v ≤ candidate input accuracy x stored source delta.val v := by
  induction deltas generalizing answer with
  | nil => simp only [List.not_mem_nil] at hdelta
  | cons first deltas ih =>
      rcases List.mem_cons.mp hdelta with hfirst | hrest
      · subst first
        have hm := min_le_right (answer.get v) (candidate input accuracy x stored source delta.val v)
        exact (extractResult_decreases input accuracy x source stored deltas _ v).trans
          (by simpa only [Vector.get_ofFn] using hm)
      · exact ih hrest (Vector.ofFn (fun w => min (answer.get w) (candidate input accuracy x stored source first.val w)))

noncomputable section

theorem candidate_source (hn : 0 < n) (accuracy x scale : ℕ) (ha : 0 < accuracy) (hscale : 0 < scale)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) :
    candidate input accuracy x stored source scale source = 0 := by
  let unit := Parameters.queryUnit n accuracy x
  have h := query_lookup hn stored (input.filterMap (microView unit)) x scale (8 * unit) source source hs
    (microView_positive unit (Parameters.queryUnit_pos n accuracy x ha) input hp) hscale hsize
  simp only [Graph.dist_self, zero_le, ↓reduceIte] at h
  change decoded unit scale (Core.BatchAPI.run (queryRequest stored x scale (8 * unit) source)
    (input.filterMap (microView unit))).records source = 0
  unfold decoded
  rw [h]
  simp

theorem extract_evaluate (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x) (deltas : List {delta : ℕ // 0 < delta}) (answer : Labels n) :
    Early.Sampling.Holds (Program.evaluate input (extractGuesses accuracy x source stored deltas answer))
      (fun result => result = extractResult input accuracy x source stored deltas answer) := by
  induction deltas generalizing answer with
  | nil => exact Early.Sampling.holds_pure answer _ rfl
  | cons delta deltas ih =>
      let unit := Parameters.queryUnit n accuracy x
      let request := queryRequest stored x delta.val (8 * unit) source
      let raw := (Core.BatchAPI.run request (input.filterMap (microView unit))).records
      have hhandler : Backend.guardedViewedHandler (microViewed unit some) input request (n + volume stored.blocks) =
          Law.pure (some raw) := by
        rw [Backend.guardedViewedHandler_eq]
        exact query_handler hn stored (input.filterMap (microView unit)) x delta.val (8 * unit) source hs
          (microView_positive unit (Parameters.queryUnit_pos n accuracy x ha) input hp) delta.property hsize
      simp only [extractGuesses, Program.evaluate, Program.evaluateViewed]
      rw [hhandler]
      refine Reference.holds_bind_on _ _ (fun result => result = some raw) _
        (Early.Sampling.holds_pure _ _ rfl) ?_
      intro reply heq
      subst reply
      exact ih _

end

end StreamingSSSP.Approx
