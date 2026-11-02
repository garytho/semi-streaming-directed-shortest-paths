module

public import StreamingSSSP.Approx.SolveWordBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

theorem guess_scale_upper (n wmin wmax : ℕ) :
    guessScale n wmin wmax ≤ wmin + 4 * n * wmax := by
  let J := guessExponent n wmin wmax
  by_cases hz : J = 0
  · simp only [guessScale, show guessExponent n wmin wmax = 0 from hz, pow_zero, mul_one]
    omega
  · have hprev := Parameters.firstCross_small wmin 2 (2 * n * wmax) (2 * n * wmax)
      (J - 1) (show J - 1 < guessExponent n wmin wmax by change J - 1 < J; omega)
    have he : wmin * 2 ^ J = 2 * (wmin * 2 ^ (J - 1)) := by
      have hj : J = (J - 1) + 1 := by omega
      conv_lhs => rw [hj, pow_succ]
      ring
    change wmin * 2 ^ J ≤ _
    rw [he]
    nlinarith

end StreamingSSSP.Hopset.Measured

namespace StreamingSSSP.Approx.Measured

open scoped Classical
open Hopset
open Hopset.Measured

variable {n : ℕ} {E : Type*}

theorem fold_maximum (input : List (StoredEdges.Edge n)) (bounds : Bounds) (weight : ℕ)
    (hb : bounds.maximum ≤ weight) (hw : ∀ e ∈ input, e.weight ≤ weight) :
    (input.foldl Bounds.push bounds).maximum ≤ weight := by
  induction input generalizing bounds with
  | nil => exact hb
  | cons e input ih =>
      apply ih
      · exact max_le hb (hw e (by simp))
      · exact fun f hf => hw f (List.mem_cons_of_mem e hf)

theorem scan_maximum (input : List (StoredEdges.Edge n)) (weight : ℕ)
    (hw : ∀ e ∈ input, e.weight ≤ weight) : (scan input).maximum ≤ weight :=
  fold_maximum input initialBounds weight (Nat.zero_le _) hw

theorem scan_minimum_upper (input : List (StoredEdges.Edge n)) (hp : ∀ e ∈ input, 0 < e.weight) :
    (scan input).minWeight ≤ (scan input).maximum + 1 := by
  cases input with
  | nil => simp [scan, Bounds.minWeight, initialBounds]
  | cons e input =>
      have hv := scan_valid (e :: input) hp
      exact (hv.minWeight_le e (by simp)).trans ((hv.upper e (by simp)).trans (Nat.le_add_right _ _))

theorem scan_guess_scale (hn : 0 < n) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (weight : ℕ) (hw : ∀ e ∈ input, e.weight ≤ weight) :
    guessScale n (scan input).minWeight (scan input).maximum ≤ 5 * n * (weight + 1) := by
  have hm := scan_minimum_upper input hp
  have hwmax := scan_maximum input weight hw
  have hg := guess_scale_upper n (scan input).minWeight (scan input).maximum
  have hprod := Nat.mul_le_mul_left (4 * n) hwmax
  nlinarith

theorem solve_payloads (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (hn : 0 < n) (accuracy x confidence weight : ℕ)
    (ha : 0 < accuracy) (source : Fin n)
    (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight)
    (hw : ∀ e ∈ input.filterMap view ++ auxiliary, e.weight ≤ weight) :
    Early.Sampling.Holds (evaluate view input auxiliary (solve hn accuracy x confidence ha source))
      (fun out => ∀ v, (out.result.get v).untopD 0 ≤ 40 * n * (weight + 1)) := by
  have hs := solve_words view input auxiliary hn accuracy x confidence ha source hp
  have hb : guessScale n (scanAuxiliary view input auxiliary).minWeight (scanAuxiliary view input auxiliary).maximum ≤
      5 * n * (weight + 1) := by
    rw [scanAuxiliary_eq]
    exact scan_guess_scale hn _ hp weight hw
  refine Early.Sampling.holds_mono hs ?_
  intro out ho v
  exact (label_payload _ out.result ho v).trans (by nlinarith)

end StreamingSSSP.Approx.Measured
