module

public import StreamingReachability.Approx.ProgramSemantics

@[expose] public section

namespace StreamingReachability.Approx

open scoped Classical
open Hopset

noncomputable section

variable {n : ℕ}

theorem scaled_decode_lower (unit scale : ℕ) (hunit : 0 < unit) (original rounded : Distance)
    (h : WithTop.map (fun d => unit * d) original ≤ WithTop.map (fun d => scale * d) rounded) :
    original ≤ WithTop.map (fun d => scale * d / unit) rounded := by
  induction original using WithTop.recTopCoe with
  | top =>
      induction rounded using WithTop.recTopCoe with
      | top => exact le_rfl
      | coe d =>
          have hh : (⊤ : Distance) ≤ ((scale * d : ℕ) : Distance) := h
          exact False.elim (WithTop.natCast_ne_top _ (top_le_iff.mp hh))
  | coe d =>
      induction rounded using WithTop.recTopCoe with
      | top => exact le_top
      | coe q =>
          have hn : unit * d ≤ scale * q := WithTop.coe_le_coe.mp h
          exact WithTop.coe_le_coe.mpr ((Nat.le_div_iff_mul_le hunit).mpr (by nlinarith only [hn]))

theorem decoded_lower (hn : 0 < n) (unit scale x radius : ℕ) (hunit : 0 < unit) (hscale : 0 < scale)
    (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n) (source v : Fin n)
    (hp : ∀ e ∈ input, 0 < e.weight) (hs : ∀ e ∈ stored.explicit, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ x)
    (hsound : stored.Sound (StoredEdges.graphOfEdges (input.filterMap (microView unit)))) :
    (StoredEdges.graphOfEdges input).dist source v ≤
      decoded unit scale
        (Core.BatchAPI.run (queryRequest stored x scale radius source) (input.filterMap (microView unit))).records v := by
  let physical := input.filterMap (microView unit)
  let G := StoredEdges.graphOfEdges physical
  let F := Late.rounded scale (stored.graph G)
  have hpos := microView_positive unit hunit input hp
  have hquery := query_lookup hn stored physical x scale radius source v hs hpos hscale hsize
  unfold decoded
  rw [hquery]
  change (StoredEdges.graphOfEdges input).dist source v ≤ WithTop.map (fun d => scale * d / unit)
    (if F.dist source v ≤ (radius : Distance) then F.dist source v else ⊤)
  by_cases hr : F.dist source v ≤ (radius : Distance)
  · rw [ite_eq_left hr]
    apply scaled_decode_lower unit scale hunit _ (F.dist source v)
    have h := noncontracting_rounded_dist G (stored.graph G) scale hscale (stored.sound_graph G hsound) source v
    have hd : G.dist source v =
        WithTop.map (fun d => unit * d) ((StoredEdges.graphOfEdges input).dist source v) := by
      change (StoredEdges.graphOfEdges (input.filterMap (microView unit))).dist source v = _
      rw [microView_graph, Graph.scaled_dist]
    rw [hd] at h
    exact h
  · rw [ite_eq_right hr]
    exact le_top

end

end StreamingReachability.Approx
