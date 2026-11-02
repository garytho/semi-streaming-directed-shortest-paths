module

public import StreamingReachability.Hopset.PathNeighborhoods
public import StreamingReachability.Hopset.EarlyPlanRoutes

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}
    {Q : Late.Path R G s t} {A : ℕ} {S : Finset (Fin n)} {D : ℝ}

theorem type2_piece_count (B : Late.Partition R G S A D Q) (hS : Q.Inside S) :
    B.pieces.length = B.type2 + 1 := by
  have hb := B.boundary_count
  rw [Q.badEdges_zero hS, Nat.add_zero] at hb
  rw [B.piece_count, hb]

theorem type2_credit (B : Late.Partition R G S A D Q) (hgreedy : B.Greedy) (hD : 0 ≤ D) :
    (B.type2 : ℝ) * D ≤ Q.searchWeight A := by
  have h := B.type2_credit hgreedy hD
  have hfirst : (0 : ℝ) ≤ B.firstWeight := Nat.cast_nonneg _
  linarith

theorem type2_related_le (B : Late.Partition R G S A D Q) (hS : Q.Inside S)
    (hA : 0 < A) (hD : 0 ≤ D) (E : Finset (Fin n)) (k M b : ℕ)
    (hin : ∀ v, (Early.searchIn (Late.rounded A (R.restricted G S)) v
      (Early.searchRadius k M D)).card ≤ b)
    (hout : ∀ v, (Early.searchOut (Late.rounded A (R.restricted G S)) v
      (Early.searchRadius k M D)).card ≤ b) :
    (B.pieces.map fun C =>
      (relatedVertices (Late.rounded A (R.restricted G S)) C.path.vertices E (Early.nearRadius k M D)).card).sum ≤
      (relatedVertices (Late.rounded A (R.restricted G S)) Q.vertices E (Early.nearRadius k M D)).card +
        2 * b * B.type2 := by
  have hc : ∀ C ∈ B.pieces,
      (relatedVertices (Late.rounded A (R.restricted G S)) C.path.vertices E (Early.nearRadius k M D)).card ≤
        2 * b := by
    intro C hC
    apply relatedVertices_card_le C.path A hA S C.inside E
      (Early.nearRadius k M D) (Early.searchRadius k M D) b _ (hin C.target) (hout C.source)
    have hshort := C.short
    unfold Early.nearRadius Early.searchRadius
    linarith
  have hs := partition_related_total_le B _ E (Early.nearRadius k M D) (2 * b) hc
  have hb := B.boundary_count
  rw [Q.badEdges_zero hS, Nat.add_zero] at hb
  rwa [hb] at hs

end

end StreamingReachability.Hopset
