module

public import StreamingReachability.Hopset.InputScaling
public import StreamingReachability.Hopset.CubeCalibration

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem sound_hopset_of_card (input : List (StoredEdges.Edge n)) (stored : Implicit.Representation n)
    (hops : ℕ) (stretch : ℝ) (hcard : n ≤ hops + 1) (hstretch : 1 ≤ stretch)
    (hs : stored.Sound (StoredEdges.graphOfEdges input)) : IsImplicitHopset input stored hops stretch := by
  refine ⟨hs, ?_⟩
  intro s t d hd
  have he := (stored.graph (StoredEdges.graphOfEdges input)).hopDist_eq_dist_of_card_le hops s t
    (by simpa only [Fintype.card_fin] using hcard)
  rw [stored.sound_distance _ hs, hd] at he
  have hu : (d : ℝ) ≤ stretch * d := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hstretch (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  exact ⟨d, he, le_rfl, hu⟩

theorem scaled_construct_small (hn : 0 < n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hmin : ∀ e ∈ input, wmin ≤ e.weight)
    (hcard : n ≤ Parameters.hopBound n accuracy x + 1) :
    let unit := Parameters.queryUnit n accuracy x
    (Builder.evaluate (Backend.guardedViewedHandler (microView unit) input)
      (construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n))).prob (fun out =>
        StoredValid (StoredEdges.graphOfEdges (input.filterMap (microView unit))) x out ∧
          IsImplicitHopset (input.filterMap (microView unit)) out (Parameters.hopBound n accuracy x)
            (1 + 1 / (5 * (accuracy : ℝ)))) = 1 := by
  let unit := Parameters.queryUnit n accuracy x
  let physical := input.filterMap (microView unit)
  let G := StoredEdges.graphOfEdges physical
  let plan := construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n)
  have hunit := Parameters.queryUnit_pos n accuracy x ha
  have hphysical := microView_positive unit hunit input hp
  have hpos : 0 < wmin * unit := Nat.mul_pos hwmin hunit
  have hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v :=
    fun u v _ => (WithTop.coe_le_coe.mpr hpos).trans (microView_lower unit wmin input hmin u v)
  have hinput : Implicit.Noncontracting G G := fun u v => Graph.dist_le_edge G u v
  have hv : Early.Sampling.Holds (Builder.evaluate (Backend.guardedHandler physical) plan) (StoredValid G x) :=
    Builder.checked_evaluate physical _ _ (stages_valid G hn accuracy x ha physical hphysical hinput hG _ _ _
      (emptyRepresentation n) (emptyRepresentation_valid G x))
  have hstretch : (1 : ℝ) ≤ 1 + 1 / (5 * (accuracy : ℝ)) :=
    le_add_of_nonneg_right (by positivity)
  have hall := Early.Sampling.holds_mono hv (fun out ho =>
    And.intro ho (sound_hopset_of_card physical out _ _ hcard hstretch ho.sound))
  change (Builder.evaluate (Backend.guardedViewedHandler (microView unit) input) plan).prob _ = 1
  rw [Backend.guardedViewedHandler_eq]
  exact Following.probability_of_holds _ _ hall

theorem scaled_construct_admissible (hn : 0 < n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hmin : ∀ e ∈ input, wmin ≤ e.weight) (hmax : ∀ e ∈ input, e.weight ≤ wmax)
    (hblock : Parameters.blockAdmissible n accuracy x) :
    let unit := Parameters.queryUnit n accuracy x
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Builder.evaluate (Backend.guardedViewedHandler (microView unit) input)
        (construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n))).prob (fun out =>
          StoredValid (StoredEdges.graphOfEdges (input.filterMap (microView unit))) x out ∧
            IsImplicitHopset (input.filterMap (microView unit)) out (Parameters.hopBound n accuracy x)
              (1 + 1 / (5 * (accuracy : ℝ)))) := by
  rcases hblock with ⟨hn₂, hpoly⟩ | hcard
  · exact scaled_construct_implicit_hopset hn hn₂ accuracy x confidence wmin wmax ha hwmin input hp hmin hmax hpoly
  · have he := scaled_construct_small hn accuracy x confidence wmin wmax ha hwmin input hp hmin hcard
    have hnonneg : (0 : ℝ) ≤ 1 / (n : ℝ) ^ confidence := by positivity
    exact (by linarith : 1 - 1 / (n : ℝ) ^ confidence ≤ 1).trans_eq he.symm

end

end StreamingReachability.Hopset
