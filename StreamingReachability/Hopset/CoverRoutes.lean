module

public import StreamingReachability.Hopset.IntervalPaths

@[expose] public section

namespace StreamingReachability.Hopset.VertexCover

open scoped Classical BigOperators

noncomputable section

open Late

variable {n : ℕ} {R : Implicit.Representation n} {G F : Graph (Fin n)}
    {s t : Fin n} {L : Type*}

theorem route (Q : Path R G s t) (C : VertexCover Q.vertices.length L)
    (hF : ∀ u v, F u v ≤ R.graph G u v) (walks : L → List (Fin n))
    (hwalks : ∀ a ∈ C.labels,
      Graph.Endpoints (walks a) (Q.vertex (C.interval a).1) (Q.vertex ((C.interval a).2 - 1)) ∧
        F.pathCost (walks a) ≤ (Q.intervalMicro (C.interval a) : Distance)) :
    ∃ T : Route F s t Q.micro,
      T.hops ≤ C.labels.card + ∑ a ∈ C.labels, ((walks a).length - 1) := by
  have hmain : ∀ fuel k (A : Finset L), A.card ≤ fuel → A ⊆ C.labels →
      k < Q.vertices.length → (∀ a ∈ A, k ≤ (C.interval a).1) →
      (∀ i : Fin Q.vertices.length, k ≤ i.val → ∃ a ∈ A, Early.Cells.Contains (C.interval a) i.val) →
      ∃ T : Route F (Q.vertex k) t (Q.suffix k).micro,
        T.hops ≤ A.card + ∑ a ∈ A, ((walks a).length - 1) := by
    intro fuel
    induction fuel with
    | zero =>
        intro k A hcard hsub hk hlo hcover
        obtain ⟨a, ha, hi⟩ := hcover ⟨k, hk⟩ le_rfl
        have hpos := Finset.card_pos.mpr ⟨a, ha⟩
        omega
    | succ fuel ih =>
        intro k A hcard hsub hk hlo hcover
        obtain ⟨a, ha, hia⟩ := hcover ⟨k, hk⟩ le_rfl
        change Early.Cells.Contains (C.interval a) k at hia
        have haC := hsub ha
        have haB := C.bounds a haC
        have haLo : (C.interval a).1 = k := by have h := hlo a ha; have h' := hia.1; omega
        let last := (C.interval a).2
        let head : Route F (Q.vertex k) (Q.vertex (last - 1)) (Q.intervalMicro (C.interval a)) :=
          ⟨walks a, by simpa only [haLo] using (hwalks a haC).1, (hwalks a haC).2⟩
        by_cases hfinal : last = Q.vertices.length
        · have hb := Q.intervalMicro_final (C.interval a) haB.1 hfinal
          rw [haLo] at hb
          have hlast : last - 1 = Q.length := by have hlen := Q.length_vertices; omega
          have ht : Q.vertex (last - 1) = t := by rw [hlast, Q.vertex_length]
          let T : Route F (Q.vertex k) t (Q.suffix k).micro :=
            ⟨walks a, ⟨head.endpoints.1, head.endpoints.2.trans (congrArg some ht)⟩,
              head.cost_le.trans_eq (congrArg (fun q : ℕ => (q : Distance)) hb)⟩
          refine ⟨T, ?_⟩
          have hs : (walks a).length - 1 ≤ ∑ b ∈ A, ((walks b).length - 1) :=
            Finset.single_le_sum (f := fun b => (walks b).length - 1) (fun _ _ => Nat.zero_le _) ha
          change (walks a).length - 1 ≤ _
          omega
        · have hlast : last < Q.vertices.length := by have hbound := haB.2; dsimp only [last] at *; omega
          have hcard' : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one ha
          have hlo' : ∀ b ∈ A.erase a, last ≤ (C.interval b).1 := by
            intro b hb
            obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
            rcases C.separated a haC b (hsub hb) (Ne.symm hne) with h | h
            · exact h
            · have hB := C.bounds b (hsub hb)
              have hlow := hlo b hb
              omega
          have hcover' : ∀ i : Fin Q.vertices.length, last ≤ i.val →
              ∃ b ∈ A.erase a, Early.Cells.Contains (C.interval b) i.val := by
            intro i hi
            obtain ⟨b, hb, hbi⟩ := hcover i (by have hpos := haB.1; omega)
            have hne : b ≠ a := by
              intro he
              subst b
              have hh := hbi.2
              omega
            exact ⟨b, Finset.mem_erase.mpr ⟨hne, hb⟩, hbi⟩
          obtain ⟨tail, htail⟩ := ih last (A.erase a) (by omega)
            ((Finset.erase_subset _ _).trans hsub) hlast hlo' hcover'
          have hlen : 0 < (Q.suffix (last - 1)).length := by
            have hs := Q.length_suffix (last - 1)
            have hv := Q.length_vertices
            omega
          obtain ⟨v, e, Rest, he⟩ := (Q.suffix (last - 1)).exists_cons_of_length_pos hlen
          have harg : last - 1 + 1 = last := by have hp := haB.1; omega
          have hv : v = Q.vertex last := by
            have h := Q.vertex_suffix (last - 1) 1
            simpa only [he, Path.vertex, Path.vertex_zero, harg] using h
          have hew : R.graph G (Q.vertex (last - 1)) (Q.vertex last) = (e.micro : Distance) :=
            (congrArg (fun z => R.graph G (Q.vertex (last - 1)) z) hv).symm.trans e.weight
          let boundary := Route.edge (F := F) (Q.vertex (last - 1)) (Q.vertex last) e.micro
            ((hF _ _).trans_eq hew)
          have hrest : Rest.micro = (Q.suffix last).micro := by
            have h := Q.micro_suffix_suffix (last - 1) 1
            rw [he, harg] at h
            change (Rest.suffix 0).micro = (Q.suffix last).micro at h
            exact Rest.micro_suffix_zero.symm.trans h
          have hboundary : (Q.suffix (last - 1)).micro = e.micro + Rest.micro := by rw [he]; rfl
          have hsplit := Q.intervalMicro_split (C.interval a) haB.1
          rw [haLo] at hsplit
          change Q.intervalMicro (C.interval a) + (Q.suffix (last - 1)).micro =
            (Q.suffix k).micro at hsplit
          have hbudget : Q.intervalMicro (C.interval a) + (e.micro + (Q.suffix last).micro) ≤
              (Q.suffix k).micro := by omega
          let T := (head.append (boundary.append tail)).weaken hbudget
          refine ⟨T, ?_⟩
          have hh := head.hops_append (boundary.append tail)
          have ht := boundary.hops_append tail
          have hb : boundary.hops = 1 := Route.hops_edge _ _ _ _
          have haH : head.hops = (walks a).length - 1 := rfl
          have hsum : (∑ b ∈ A.erase a, ((walks b).length - 1)) + ((walks a).length - 1) =
              ∑ b ∈ A, ((walks b).length - 1) :=
            Finset.sum_erase_add _ _ ha
          change (head.append (boundary.append tail)).hops ≤ _
          omega
  have hsize : 0 < Q.vertices.length := by rw [Q.length_vertices]; omega
  obtain ⟨T, hT⟩ := hmain C.labels.card 0 C.labels le_rfl (Finset.Subset.refl _)
    hsize (by intro a ha; exact Nat.zero_le _) (fun i hi => C.covers i)
  let final : Route F s t Q.micro :=
    ⟨T.vertices, by simpa only [Q.vertex_zero] using T.endpoints,
      T.cost_le.trans_eq (congrArg (fun q : ℕ => (q : Distance)) Q.micro_suffix_zero)⟩
  exact ⟨final, hT⟩

theorem route_subtype (Q : Path R G s t) (C : VertexCover Q.vertices.length L)
    (hF : ∀ u v, F u v ≤ R.graph G u v)
    (walks : {a : L // a ∈ C.labels} → List (Fin n))
    (hwalks : ∀ a : {a : L // a ∈ C.labels},
      Graph.Endpoints (walks a) (Q.vertex (C.interval a.val).1) (Q.vertex ((C.interval a.val).2 - 1)) ∧
        F.pathCost (walks a) ≤ (Q.intervalMicro (C.interval a.val) : Distance)) :
    ∃ T : Route F s t Q.micro,
      T.hops ≤ C.labels.card + ∑ a : {a : L // a ∈ C.labels}, ((walks a).length - 1) := by
  let extend : L → List (Fin n) := fun a => if ha : a ∈ C.labels then walks ⟨a, ha⟩ else []
  have hw (a : L) (ha : a ∈ C.labels) :
      Graph.Endpoints (extend a) (Q.vertex (C.interval a).1) (Q.vertex ((C.interval a).2 - 1)) ∧
        F.pathCost (extend a) ≤ (Q.intervalMicro (C.interval a) : Distance) := by
    simpa only [extend, ha, ↓reduceDIte] using hwalks ⟨a, ha⟩
  obtain ⟨T, hT⟩ := route Q C hF extend hw
  have hs : (∑ a ∈ C.labels, ((extend a).length - 1)) =
      ∑ a : {a : L // a ∈ C.labels}, ((walks a).length - 1) := by
    rw [← Finset.sum_coe_sort C.labels (fun a => (extend a).length - 1)]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [extend, a.property, ↓reduceDIte]
  exact ⟨T, by simpa only [hs] using hT⟩

end

end StreamingReachability.Hopset.VertexCover
