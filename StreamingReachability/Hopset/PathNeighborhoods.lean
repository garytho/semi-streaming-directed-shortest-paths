module

public import StreamingReachability.Hopset.PartitionFacts
public import StreamingReachability.Late.Boundary

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

def relatedVertices (H : Graph V) (xs : List V) (E : Finset V) (radius : ℝ) : Finset V :=
  E.filter fun w => (∃ v ∈ xs, Early.Within H w v radius) ∨ ∃ v ∈ xs, Early.Within H v w radius

theorem mem_relatedVertices (H : Graph V) (xs : List V) (E : Finset V) (radius : ℝ) (w : V) :
    w ∈ relatedVertices H xs E radius ↔
      w ∈ E ∧ ((∃ v ∈ xs, Early.Within H w v radius) ∨ ∃ v ∈ xs, Early.Within H v w radius) :=
  Finset.mem_filter

theorem mem_nearPivots {H : Graph V} {D : ℝ} (Q : Early.ShortPath H D)
    (E : Finset V) (radius : ℝ) (w : V) :
    w ∈ Early.nearPivots Q E radius ↔ w ∈ E ∧ Early.Near Q w radius := by
  unfold Early.nearPivots
  exact Finset.mem_filter

theorem relatedVertices_shortPath {H : Graph V} {D : ℝ}
    (Q : Early.ShortPath H D) (E : Finset V) (radius : ℝ) :
    relatedVertices H Q.vertices E radius = Early.nearPivots Q E radius := by
  ext w
  simp only [mem_relatedVertices, mem_nearPivots, Early.Near,
    List.exists_mem_iff_get, Early.ShortPath.vertex, Early.ShortPath.size]

theorem relatedVertices_mono (H F : Graph V) (xs ys : List V) (E E' : Finset V) (r r' : ℝ)
    (hgraph : ∀ u v, H.dist u v ≤ F.dist u v) (hvertices : ∀ v ∈ xs, v ∈ ys)
    (hE : E ⊆ E') (hr : r ≤ r') :
    relatedVertices F xs E r ⊆ relatedVertices H ys E' r' := by
  intro w hw
  obtain ⟨hwE, hw⟩ := (mem_relatedVertices F xs E r w).mp hw
  apply (mem_relatedVertices H ys E' r' w).mpr
  refine ⟨hE hwE, ?_⟩
  rcases hw with ⟨v, hv, hdist⟩ | ⟨v, hv, hdist⟩
  · exact Or.inl ⟨v, hvertices v hv, Early.within_mono
      (Early.bounded_mono_distance (hgraph w v) hdist) hr⟩
  · exact Or.inr ⟨v, hvertices v hv, Early.within_mono
      (Early.bounded_mono_distance (hgraph v w) hdist) hr⟩

theorem list_sum_le_base_add {T : Type*} (xs : List T) (f : T → ℕ) (base c : ℕ)
    (hbase : ∀ x ∈ xs, f x ≤ base) (hc : ∀ x ∈ xs, f x ≤ c) :
    (xs.map f).sum ≤ base + c * (xs.length - 1) := by
  cases xs with
  | nil => simp
  | cons a xs =>
      have ha := hbase a (by simp)
      have ht : (xs.map f).sum ≤ xs.length * c := by
        calc
          _ ≤ (xs.map fun _ => c).sum := List.sum_le_sum (fun x hx => hc x (List.mem_cons_of_mem _ hx))
          _ = _ := by simp
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_sub_cancel]
      rw [Nat.mul_comm]
      omega

variable {n : ℕ} {R : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem relatedVertices_card_le (Q : Late.Path R G s t) (A : ℕ) (hA : 0 < A)
    (S : Finset (Fin n)) (hS : Q.Inside S) (E : Finset (Fin n)) (radius cap : ℝ) (b : ℕ)
    (hbudget : (Q.searchWeight A : ℝ) + radius ≤ cap)
    (hin : (Early.searchIn (Late.rounded A (R.restricted G S)) t cap).card ≤ b)
    (hout : (Early.searchOut (Late.rounded A (R.restricted G S)) s cap).card ≤ b) :
    (relatedVertices (Late.rounded A (R.restricted G S)) Q.vertices E radius).card ≤ 2 * b := by
  let H := Late.rounded A (R.restricted G S)
  have hsub : relatedVertices H Q.vertices E radius ⊆ Late.endpointNear H s t cap := by
    intro w hw
    have hsupp (v : Fin n) (hv : v ∈ Q.vertices) : v ∈ Q.support := by
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
      rw [← hi, Q.get_vertices]
      exact Q.vertex_support i.val
    rcases (mem_relatedVertices H Q.vertices E radius w).mp hw |>.2 with
      ⟨v, hv, hd⟩ | ⟨v, hv, hd⟩
    · have htail := Q.support_to_end A hA hS (hsupp v hv)
      have h := Early.within_mono (Early.within_trans hd htail) (by linarith : radius + Q.searchWeight A ≤ cap)
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · have hpre := Q.start_to_support A hA hS (hsupp v hv)
      have h := Early.within_mono (Early.within_trans hpre hd) hbudget
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  exact (Finset.card_le_card hsub).trans (Late.endpointNear_card H s t cap b hin hout)

theorem partition_related_total_le {X : Finset (Fin n)} {A : ℕ} {d : ℝ} {Q : Late.Path R G s t}
    (B : Late.Partition R G X A d Q) (H : Graph (Fin n)) (E : Finset (Fin n)) (radius : ℝ) (c : ℕ)
    (hc : ∀ C ∈ B.pieces, (relatedVertices H C.path.vertices E radius).card ≤ c) :
    (B.pieces.map fun C => (relatedVertices H C.path.vertices E radius).card).sum ≤
      (relatedVertices H Q.vertices E radius).card + c * B.boundaries := by
  have hbase : ∀ C ∈ B.pieces,
      (relatedVertices H C.path.vertices E radius).card ≤ (relatedVertices H Q.vertices E radius).card := by
    intro C hC
    apply Finset.card_le_card
    apply relatedVertices_mono H H _ _ E E radius radius (fun _ _ => le_rfl) _ (fun _ h => h) le_rfl
    intro v hv
    exact ((B.piece_vertices_infix C hC).sublist.subset hv)
  have hs := list_sum_le_base_add B.pieces _ _ c hbase hc
  simpa only [B.piece_count, Nat.add_sub_cancel] using hs

end

end StreamingReachability.Hopset
