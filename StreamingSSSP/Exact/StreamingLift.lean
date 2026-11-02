module

public import StreamingSSSP.Exact.StreamingEncoding

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open StoredEdges

variable {n : ℕ}

theorem lifted_ne_last (v : Fin n) : v.castSucc ≠ Fin.last n := by
  intro h
  have hv := congrArg Fin.val h
  have hi := v.isLt
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

theorem last_ne_lifted (v : Fin n) : Fin.last n ≠ v.castSucc := (lifted_ne_last v).symm

theorem lifted_eq_lifted (u v : Fin n) : u.castSucc = v.castSucc ↔ u = v :=
  ⟨fun h => Fin.ext (congrArg (fun w : Fin (n + 1) => w.val) h), congrArg Fin.castSucc⟩

def liftEdge (edge : Edge n) : Edge (n + 1) :=
  ⟨edge.source.castSucc, edge.target.castSucc, edge.weight⟩

def onlyOriginal (G : Graph (Fin n)) : Graph (Option (Fin n))
  | some u, some v => G u v
  | _, _ => ⊤

theorem lift_graph_apply (input : List (Edge n)) (u v : Option (Fin n)) :
    graphOfEdges (input.map liftEdge) (encodeVertex u) (encodeVertex v) = onlyOriginal (graphOfEdges input) u v := by
  induction input with
  | nil => cases u <;> cases v <;> rfl
  | cons edge input ih =>
      cases u <;> cases v
      all_goals
        simp only [encodeVertex, onlyOriginal] at ih
        simp only [List.map_cons, graphOfEdges_cons, edgeCost, liftEdge, encodeVertex, lifted_ne_last, last_ne_lifted,
          lifted_eq_lifted, false_and, and_false, ↓reduceIte, onlyOriginal, ih, min_top_right, min_top_left]

theorem lift_graph (input : List (Edge n)) :
    graphOfEdges (input.map liftEdge) = (onlyOriginal (graphOfEdges input)).comap (vertexEquiv n) := by
  funext u v
  have h := lift_graph_apply input (decodeVertex u) (decodeVertex v)
  simp only [encode_decode] at h
  exact h

def virtualEdges (weight : Fin n → ℕ) : List (Edge (n + 1)) :=
  (List.finRange n).map (fun v => ⟨Fin.last n, v.castSucc, weight v⟩)

def virtualGraph (weight : Fin n → ℕ) : Graph (Option (Fin n))
  | none, some v => (weight v : Distance)
  | _, _ => ⊤

theorem virtual_graph_apply (weight : Fin n → ℕ) (u v : Option (Fin n)) :
    graphOfEdges (virtualEdges weight) (encodeVertex u) (encodeVertex v) = virtualGraph weight u v := by
  cases v with
  | none =>
      have htarget : graphOfEdges (virtualEdges weight) (encodeVertex u) (Fin.last n) = ⊤ := by
        by_contra hne
        obtain ⟨edge, he, hs, ht⟩ := (graphOfEdges_ne_top_iff _ _ _).mp hne
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
        exact lifted_ne_last w ht
      cases u <;> exact htarget
  | some v =>
      cases u with
      | none =>
          change graphOfEdges (virtualEdges weight) (Fin.last n) v.castSucc = (weight v : Distance)
          apply le_antisymm
          · have hm : (⟨Fin.last n, v.castSucc, weight v⟩ : Edge (n + 1)) ∈ virtualEdges weight :=
              List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩
            exact graphOfEdges_le_edge _ hm
          · apply (le_graphOfEdges_iff _ _ _ _).mpr
            intro edge he _ ht
            obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
            have heq : w = v := (lifted_eq_lifted w v).mp ht
            subst w
            exact le_rfl
      | some u =>
          change graphOfEdges (virtualEdges weight) u.castSucc v.castSucc = ⊤
          by_contra hne
          obtain ⟨edge, he, hs, ht⟩ := (graphOfEdges_ne_top_iff _ _ _).mp hne
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp he
          exact last_ne_lifted u hs

theorem virtual_graph (weight : Fin n → ℕ) :
    graphOfEdges (virtualEdges weight) = (virtualGraph weight).comap (vertexEquiv n) := by
  funext u v
  have h := virtual_graph_apply weight (decodeVertex u) (decodeVertex v)
  simp only [encode_decode] at h
  exact h

theorem virtual_length (weight : Fin n → ℕ) : (virtualEdges weight).length = n := by
  simp only [virtualEdges, List.length_map, List.length_finRange]

end StreamingSSSP.Exact.Implementation
