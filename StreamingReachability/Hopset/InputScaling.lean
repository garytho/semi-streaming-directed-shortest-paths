module

public import StreamingReachability.Hopset.ConstructionCorrectness
public import StreamingReachability.Exact.Descriptors

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

variable {n : ℕ}

def microMap (U : ℕ) (edge : StoredEdges.Edge n) : StoredEdges.Edge n :=
  { edge with weight := U * edge.weight }

def microView (U : ℕ) (edge : StoredEdges.Edge n) : Option (StoredEdges.Edge n) :=
  some (microMap U edge)

theorem microView_list (U : ℕ) (input : List (StoredEdges.Edge n)) :
    input.filterMap (microView U) = input.map (microMap U) := by
  induction input with
  | nil => rfl
  | cons e input ih => simp only [List.filterMap_cons, microView, List.map_cons, ih]

theorem microView_graph (U : ℕ) (input : List (StoredEdges.Edge n)) :
    StoredEdges.graphOfEdges (input.filterMap (microView U)) =
      Graph.scaled (StoredEdges.graphOfEdges input) U := by
  rw [microView_list]
  change StoredEdges.graphOfEdges (input.map (Exact.EdgeTransducer.mapEdge (fun _ _ w => U * w))) = _
  funext u v
  rw [Exact.EdgeTransducer.map_graph (fun _ _ w => U * w)
    (fun _ _ _ _ h => Nat.mul_le_mul_left U h), Graph.scaled_apply]

theorem microView_positive (U : ℕ) (hU : 0 < U) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) :
    ∀ e ∈ input.filterMap (microView U), 0 < e.weight := by
  intro e he
  rw [microView_list] at he
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
  exact Nat.mul_pos hU (hp original ho)

theorem microView_lower (U wmin : ℕ) (input : List (StoredEdges.Edge n))
    (hmin : ∀ e ∈ input, wmin ≤ e.weight) (u v : Fin n) :
    ((wmin * U : ℕ) : Distance) ≤ StoredEdges.graphOfEdges (input.filterMap (microView U)) u v := by
  apply (StoredEdges.le_graphOfEdges_iff _ u v _).mpr
  intro e he _ _
  rw [microView_list] at he
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
  have h := Nat.mul_le_mul_left U (hmin original ho)
  change ((wmin * U : ℕ) : Distance) ≤ ((U * original.weight : ℕ) : Distance)
  exact WithTop.coe_le_coe.mpr (by nlinarith only [h])

theorem microView_upper (U wmax : ℕ) (input : List (StoredEdges.Edge n))
    (hmax : ∀ e ∈ input, e.weight ≤ wmax) :
    Exact.WeightsBounded (StoredEdges.graphOfEdges (input.filterMap (microView U))) (wmax * U) := by
  intro u v w hw
  obtain ⟨e, he, _, _, hew⟩ := StoredEdges.exists_edge_eq (input.filterMap (microView U)) (u := u) (v := v) (by simp [hw])
  rw [microView_list] at he
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp he
  have heq : U * original.weight = w := by exact_mod_cast hew.trans hw
  have h := Nat.mul_le_mul_left U (hmax original ho)
  nlinarith only [h, heq]

def emptyRepresentation (n : ℕ) : Implicit.Representation n := ⟨[], []⟩

theorem emptyRepresentation_valid (G : Graph (Fin n)) (x : ℕ) :
    StoredValid G x (emptyRepresentation n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    cases he
  · intro e he
    cases he
  · intro B hB
    cases hB

noncomputable section

theorem scaled_construct_implicit_hopset (hn : 0 < n) (hn₂ : 2 ≤ n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hmin : ∀ e ∈ input, wmin ≤ e.weight) (hmax : ∀ e ∈ input, e.weight ≤ wmax)
    (hpoly : 4 * 100 * Parameters.k n * Parameters.ell n ≤ x) :
    let U := Parameters.queryUnit n accuracy x
    1 - 1 / (n : ℝ) ^ confidence ≤
      (Builder.evaluate (Backend.guardedViewedHandler (microView U) input)
        (construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n))).prob (fun out =>
          StoredValid (StoredEdges.graphOfEdges (input.filterMap (microView U))) x out ∧
            IsImplicitHopset (input.filterMap (microView U)) out (Parameters.hopBound n accuracy x)
              (1 + 1 / (5 * (accuracy : ℝ)))) := by
  let U := Parameters.queryUnit n accuracy x
  change 1 - 1 / (n : ℝ) ^ confidence ≤
    (Builder.evaluate (Backend.guardedViewedHandler (microView U) input)
      (construct hn accuracy x confidence wmin wmax ha hwmin (emptyRepresentation n))).prob _
  rw [Backend.guardedViewedHandler_eq]
  exact construct_implicit_hopset hn hn₂ accuracy x confidence wmin wmax ha hwmin
    (input.filterMap (microView U)) (microView_positive U (Parameters.queryUnit_pos n accuracy x ha) input hp)
    (fun u v _ => microView_lower U wmin input hmin u v) (microView_upper U wmax input hmax) hpoly
    (emptyRepresentation n) (emptyRepresentation_valid _ x)

end

end StreamingReachability.Hopset
