module

public import StreamingSSSP.Exact.GuardCorrectness

@[expose] public section

namespace StreamingSSSP.Exact

open StoredEdges

variable {V : Type*}

/-- The complete persistent data of a base-query edge transducer. -/
structure BaseDescriptor (V : Type*) where
  potential : V → ℕ
  inflation : ℕ
  positiveScale : ℕ

def BaseDescriptor.weight (d : BaseDescriptor V) (u v : V) (w : ℕ) : ℕ :=
  d.positiveScale * (d.inflation * (w + d.potential u - d.potential v) + 1) + 1

def BaseDescriptor.graph (d : BaseDescriptor V) (G : Graph V) : Graph V :=
  affineGraph (affineGraph (reweight G d.potential) d.inflation 1) d.positiveScale 1

theorem BaseDescriptor.local (d : BaseDescriptor V) (G : Graph V) (u v : V) :
    d.graph G u v = WithTop.map (d.weight u v) (G u v) := by
  by_cases hn : G u v = ⊤
  · simp [graph, affineGraph, reweight, mapWeights, hn]
  · lift G u v to ℕ using hn with w hw
    change d.graph G u v = ((d.weight u v w : ℕ) : Distance)
    have hR := reweight_coe G d.potential hw.symm
    have hB := mapWeights_coe (reweight G d.potential) (fun z => d.inflation * z + 1) hR
    exact mapWeights_coe (affineGraph (reweight G d.potential) d.inflation 1)
      (fun z => d.positiveScale * z + 1) hB

/-- A level-query transducer stores two endpoint vectors and five scalars.
There is deliberately no field containing a precomputed oracle graph. -/
structure LevelDescriptor (V : Type*) where
  potential : V → ℕ
  labels : V → ℕ
  inflation : ℕ
  slope : ℕ
  width : ℕ
  shift : ℕ
  positiveScale : ℕ

def LevelDescriptor.keep (d : LevelDescriptor V) (u v : V) : Bool :=
  decide (binIndex d.width d.shift (d.labels u) = binIndex d.width d.shift (d.labels v))

def LevelDescriptor.weight (d : LevelDescriptor V) (u v : V) (w : ℕ) : ℕ :=
  d.positiveScale * (d.slope * (d.inflation * (w + d.potential u - d.potential v) + 1)) + 1

def LevelDescriptor.sourceWeight (d : LevelDescriptor V) (v : V) : ℕ :=
  d.positiveScale * residue d.width d.shift (d.labels v) + 1

def LevelDescriptor.graph (d : LevelDescriptor V) (G : Graph V) :
    Graph (Option V) :=
  affineGraph
    (levelGraph (affineGraph (reweight G d.potential) d.inflation 1)
      d.labels d.slope d.width d.shift) d.positiveScale 1

theorem LevelDescriptor.local (d : LevelDescriptor V) (G : Graph V) (u v : V) :
    d.graph G (some u) (some v) =
      if d.keep u v then WithTop.map (d.weight u v) (G u v) else ⊤ := by
  unfold graph
  by_cases hb : binIndex d.width d.shift (d.labels u) =
      binIndex d.width d.shift (d.labels v)
  · have hk : d.keep u v = true := by simp [keep, hb]
    rw [hk]
    simp only [Bool.true_eq, ite_true]
    by_cases hn : G u v = ⊤
    · simp [affineGraph, mapWeights, levelGraph, hb, reweight, hn]
    · lift G u v to ℕ using hn with w hw
      change affineGraph
        (levelGraph (affineGraph (reweight G d.potential) d.inflation 1)
          d.labels d.slope d.width d.shift) d.positiveScale 1 (some u) (some v) =
        ((d.weight u v w : ℕ) : Distance)
      have hR := reweight_coe G d.potential hw.symm
      have hB := mapWeights_coe (reweight G d.potential) (fun z => d.inflation * z + 1) hR
      have hL : levelGraph (affineGraph (reweight G d.potential) d.inflation 1)
          d.labels d.slope d.width d.shift (some u) (some v) =
          ((d.slope * (d.inflation * (w + d.potential u - d.potential v) + 1) : ℕ) : Distance) := by
        simp only [levelGraph, if_pos hb]
        exact mapWeights_coe _ (d.slope * ·) hB
      exact mapWeights_coe _ (fun z => d.positiveScale * z + 1) hL
  · have hk : d.keep u v = false := by simp [keep, hb]
    simp [hk, affineGraph, mapWeights, levelGraph, hb]

theorem LevelDescriptor.source_local (d : LevelDescriptor V) (G : Graph V) (v : V) :
    d.graph G none (some v) = (d.sourceWeight v : Distance) := by
  unfold graph sourceWeight
  exact mapWeights_coe _ _ rfl

theorem LevelDescriptor.no_incoming_source (d : LevelDescriptor V) (G : Graph V) (v : Option V) :
    d.graph G v none = ⊤ := by
  simp [graph, affineGraph, mapWeights, levelGraph]

theorem withTop_map_monotone (f : ℕ → ℕ) (hf : Monotone f) :
    Monotone (WithTop.map f : Distance → Distance) := by
  intro x y hxy
  by_cases hx : x = ⊤
  · have hy : y = ⊤ := top_le_iff.mp (hx ▸ hxy)
    simp [hx, hy]
  by_cases hy : y = ⊤
  · simp [hy]
  lift x to ℕ using hx with a ha
  lift y to ℕ using hy with b hb
  exact WithTop.coe_le_coe.mpr (hf (WithTop.coe_le_coe.mp hxy))

theorem withTop_map_min (f : ℕ → ℕ) (hf : Monotone f) (x y : Distance) :
    WithTop.map f (min x y) = min (WithTop.map f x) (WithTop.map f y) := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, min_eq_left (withTop_map_monotone f hf hxy)]
  · have hyx := le_of_not_ge hxy
    rw [min_eq_right hyx, min_eq_right (withTop_map_monotone f hf hyx)]

namespace EdgeTransducer

variable {n : ℕ}

def mapEdge (f : Fin n → Fin n → ℕ → ℕ) (e : Edge n) : Edge n :=
  { e with weight := f e.source e.target e.weight }

/-- Pointwise graph semantics of an actual edge-by-edge map, including duplicate
edges. Monotonicity justifies mapping the duplicate minimum. -/
theorem map_graph (f : Fin n → Fin n → ℕ → ℕ)
    (hf : ∀ u v, Monotone (f u v)) (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges (edges.map (mapEdge f)) u v = WithTop.map (f u v) (graphOfEdges edges u v) := by
  induction edges with
  | nil => simp [graphOfEdges_nil]
  | cons e edges ih =>
      simp only [List.map_cons, graphOfEdges_cons, ih]
      rw [withTop_map_min _ (hf u v)]
      congr 1
      by_cases he : e.source = u ∧ e.target = v
      · rcases he with ⟨hu, hv⟩
        simp [edgeCost, mapEdge, hu, hv]
      · simp [edgeCost, mapEdge, he]

theorem base_weight_monotone (d : BaseDescriptor (Fin n)) (u v : Fin n) :
    Monotone (d.weight u v) := by
  intro a b hab
  unfold BaseDescriptor.weight
  gcongr

theorem base_graph (d : BaseDescriptor (Fin n)) (edges : List (Edge n)) :
    graphOfEdges (edges.map (mapEdge d.weight)) = d.graph (graphOfEdges edges) := by
  funext u v
  rw [map_graph d.weight (base_weight_monotone d), d.local]

def retained (d : LevelDescriptor (Fin n)) (edges : List (Edge n)) : List (Edge n) :=
  edges.filter (fun e => d.keep e.source e.target)

def levelEdges (d : LevelDescriptor (Fin n)) (edges : List (Edge n)) : List (Edge n) :=
  (retained d edges).map (mapEdge d.weight)

theorem level_weight_monotone (d : LevelDescriptor (Fin n)) (u v : Fin n) :
    Monotone (d.weight u v) := by
  intro a b hab
  unfold LevelDescriptor.weight
  gcongr

theorem retained_graph (d : LevelDescriptor (Fin n)) (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges (retained d edges) u v =
      if d.keep u v then graphOfEdges edges u v else ⊤ := by
  induction edges with
  | nil => simp [retained]
  | cons e edges ih =>
      unfold retained at *
      simp only [List.filter_cons]
      by_cases hk : d.keep e.source e.target
      · rw [if_pos hk, graphOfEdges_cons, ih]
        by_cases he : e.source = u ∧ e.target = v
        · rcases he with ⟨hu, hv⟩
          have hkuv : d.keep u v = true := by simpa [hu, hv] using hk
          simp [hkuv]
        · simp [edgeCost, he]
      · rw [if_neg hk, ih]
        by_cases he : e.source = u ∧ e.target = v
        · rcases he with ⟨hu, hv⟩
          simp [hu, hv] at hk ⊢
          simp [hk]
        · simp [graphOfEdges_cons, edgeCost, he]

theorem level_graph (d : LevelDescriptor (Fin n)) (edges : List (Edge n)) (u v : Fin n) :
    graphOfEdges (levelEdges d edges) u v = d.graph (graphOfEdges edges) (some u) (some v) := by
  unfold levelEdges
  rw [map_graph d.weight (level_weight_monotone d), retained_graph, d.local]
  split_ifs <;> simp

theorem base_length (d : BaseDescriptor (Fin n)) (edges : List (Edge n)) :
    (edges.map (mapEdge d.weight)).length = edges.length := by simp

theorem level_length (d : LevelDescriptor (Fin n)) (edges : List (Edge n)) :
    (levelEdges d edges).length ≤ edges.length := by
  unfold levelEdges retained
  simpa using List.length_filter_le (fun e => d.keep e.source e.target) edges

def sentinelEdges (source : Fin n) (threshold : ℕ) : List (Edge n) :=
  ((List.finRange n).filter (· ≠ source)).map (fun v => ⟨source, v, threshold⟩)

theorem sentinelEdges_mem (source : Fin n) (threshold : ℕ) (e : Edge n) :
    e ∈ sentinelEdges source threshold ↔
      e.source = source ∧ e.target ≠ source ∧ e.weight = threshold := by
  cases e with
  | mk u v w =>
      simp [sentinelEdges]
      grind

theorem sentinelEdges_graph (source : Fin n) (threshold : ℕ) :
    graphOfEdges (sentinelEdges source threshold) = sentinelGraph source threshold := by
  funext u v
  by_cases h : u = source ∧ v ≠ source
  · obtain ⟨hu, hv⟩ := h
    subst u
    have hemem : (⟨source, v, threshold⟩ : Edge n) ∈ sentinelEdges source threshold := by
      simp [sentinelEdges_mem, hv]
    apply le_antisymm
    · simpa [sentinelGraph, hv] using graphOfEdges_le_edge _ hemem
    · rw [show sentinelGraph source threshold source v = (threshold : Distance) by
        simp [sentinelGraph, hv]]
      apply (le_graphOfEdges_iff _ _ _ _).mpr
      intro e he _ _
      have hw := (sentinelEdges_mem source threshold e).mp he
      simp [hw.2.2]
  · have hn : graphOfEdges (sentinelEdges source threshold) u v = ⊤ := by
      by_contra hn
      obtain ⟨e, he, heu, hev⟩ := (graphOfEdges_ne_top_iff _ _ _).mp hn
      have hh := (sentinelEdges_mem source threshold e).mp he
      exact h ⟨heu ▸ hh.1, hev ▸ hh.2.1⟩
    simp [sentinelGraph, h, hn]

def preprocessingEdges (edges : List (Edge n)) (source : Fin n) (W : ℕ) : List (Edge n) :=
  edges.map (mapEdge (fun _ _ w => n * w + 1)) ++ sentinelEdges source (sentinel n W)

theorem preprocessing_graph (edges : List (Edge n)) (source : Fin n) (W : ℕ) :
    graphOfEdges (preprocessingEdges edges source W) =
      preprocess (graphOfEdges edges) source W := by
  unfold preprocessingEdges preprocess
  simp only [Fintype.card_fin]
  rw [graphOfEdges_append, sentinelEdges_graph]
  congr 1
  funext u v
  simpa [affineGraph, mapWeights] using
    map_graph (fun _ _ w => n * w + 1) (by
      intro u v a b hab
      change n * a + 1 ≤ n * b + 1
      exact Nat.add_le_add_right (Nat.mul_le_mul_left n hab) 1) edges u v

theorem preprocessing_length (edges : List (Edge n)) (source : Fin n) (W : ℕ) :
    (preprocessingEdges edges source W).length ≤ edges.length + n := by
  simp only [preprocessingEdges, List.length_append, List.length_map, sentinelEdges]
  have hl := List.length_filter_le (fun v : Fin n => v ≠ source) (List.finRange n)
  simpa using Nat.add_le_add_left hl edges.length

/-- `m+2n` edges suffice for every level query: at most one emitted edge per
preprocessed input edge, and exactly one virtual-source edge per vertex. -/
theorem oracle_edge_count (d : LevelDescriptor (Fin n)) (edges : List (Edge n))
    (source : Fin n) (W : ℕ) :
    (levelEdges d (preprocessingEdges edges source W)).length + n ≤ edges.length + 2 * n := by
  have h₁ := level_length d (preprocessingEdges edges source W)
  have h₂ := preprocessing_length edges source W
  omega

end EdgeTransducer

end StreamingSSSP.Exact
