module

public import StreamingSSSP.Hopset.SearchPathAlgebra

@[expose] public section

namespace StreamingSSSP.Hopset.VertexCover

open scoped Classical BigOperators
open Late

noncomputable section

variable {n : ℕ} {R : Implicit.Representation n} {G F : Graph (Fin n)}
    {s t : Fin n} {L : Type*}

theorem search_route (Q : Path R G s t) (C : VertexCover Q.vertices.length L)
    (scale : ℕ) (hscale : 0 < scale) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (debt : L → ℕ) (walks : L → List (Fin n))
    (hwalks : ∀ a ∈ C.labels,
      Graph.Endpoints (walks a) (Q.vertex (C.interval a).1) (Q.vertex ((C.interval a).2 - 1)) ∧
        F.pathCost (walks a) ≤ ((scale * (Q.intervalSearch scale (C.interval a) + debt a) : ℕ) : Distance)) :
    ∃ T : Route F s t (scale * (Q.searchWeight scale + ∑ a ∈ C.labels, debt a)),
      T.hops ≤ C.labels.card + ∑ a ∈ C.labels, ((walks a).length - 1) := by
  have hmain : ∀ fuel k (A : Finset L), A.card ≤ fuel → A ⊆ C.labels →
      k < Q.vertices.length → (∀ a ∈ A, k ≤ (C.interval a).1) →
      (∀ i : Fin Q.vertices.length, k ≤ i.val → ∃ a ∈ A, Early.Cells.Contains (C.interval a) i.val) →
      ∃ T : Route F (Q.vertex k) t (scale * ((Q.suffix k).searchWeight scale + ∑ a ∈ A, debt a)),
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
        let head : Route F (Q.vertex k) (Q.vertex (last - 1))
            (scale * (Q.intervalSearch scale (C.interval a) + debt a)) :=
          ⟨walks a, by simpa only [haLo] using (hwalks a haC).1, (hwalks a haC).2⟩
        by_cases hfinal : last = Q.vertices.length
        · have hb := Q.intervalSearch_final scale (C.interval a) haB.1 hfinal
          rw [haLo] at hb
          have hlast : last - 1 = Q.length := by have hlen := Q.length_vertices; omega
          have ht : Q.vertex (last - 1) = t := by rw [hlast, Q.vertex_length]
          have hdebt : debt a ≤ ∑ b ∈ A, debt b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
          have hcost : scale * (Q.intervalSearch scale (C.interval a) + debt a) ≤
              scale * ((Q.suffix k).searchWeight scale + ∑ b ∈ A, debt b) := by
            rw [hb]
            exact Nat.mul_le_mul_left scale (Nat.add_le_add_left hdebt _)
          let T : Route F (Q.vertex k) t (scale * ((Q.suffix k).searchWeight scale + ∑ b ∈ A, debt b)) :=
            ⟨walks a, ⟨head.endpoints.1, head.endpoints.2.trans (congrArg some ht)⟩,
              head.cost_le.trans (WithTop.coe_le_coe.mpr hcost)⟩
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
          have hround : e.micro ≤ scale * e.searchWeight scale := (Core.ceilNat_le_iff hscale).mp le_rfl
          let boundary := Route.edge (F := F) (Q.vertex (last - 1)) (Q.vertex last) (scale * e.searchWeight scale)
            (((hF _ _).trans_eq hew).trans (WithTop.coe_le_coe.mpr hround))
          have hrest : Rest.searchWeight scale = (Q.suffix last).searchWeight scale := by
            have h := Q.searchWeight_suffix_suffix scale (last - 1) 1
            rw [he, harg] at h
            change (Rest.suffix 0).searchWeight scale = (Q.suffix last).searchWeight scale at h
            exact (Rest.searchWeight_suffix_zero scale).symm.trans h
          have hboundary : (Q.suffix (last - 1)).searchWeight scale = e.searchWeight scale + Rest.searchWeight scale := by
            rw [he]
            rfl
          have hsplit := Q.intervalSearch_split scale (C.interval a) haB.1
          rw [haLo] at hsplit
          change Q.intervalSearch scale (C.interval a) + (Q.suffix (last - 1)).searchWeight scale =
            (Q.suffix k).searchWeight scale at hsplit
          have hweight : Q.intervalSearch scale (C.interval a) + e.searchWeight scale +
              (Q.suffix last).searchWeight scale = (Q.suffix k).searchWeight scale := by omega
          have hdebt : (∑ b ∈ A.erase a, debt b) + debt a = ∑ b ∈ A, debt b :=
            Finset.sum_erase_add _ _ ha
          have hbudget :
              scale * (Q.intervalSearch scale (C.interval a) + debt a) +
                (scale * e.searchWeight scale +
                  scale * ((Q.suffix last).searchWeight scale + ∑ b ∈ A.erase a, debt b)) ≤
              scale * ((Q.suffix k).searchWeight scale + ∑ b ∈ A, debt b) := by
            apply le_of_eq
            calc
              _ = scale * ((Q.intervalSearch scale (C.interval a) + e.searchWeight scale +
                  (Q.suffix last).searchWeight scale) + ((∑ b ∈ A.erase a, debt b) + debt a)) := by ring
              _ = _ := by rw [hweight, hdebt]
          let T := (head.append (boundary.append tail)).weaken hbudget
          refine ⟨T, ?_⟩
          have hh := head.hops_append (boundary.append tail)
          have ht := boundary.hops_append tail
          have hb : boundary.hops = 1 := Route.hops_edge _ _ _ _
          have haH : head.hops = (walks a).length - 1 := rfl
          have hsum : (∑ b ∈ A.erase a, ((walks b).length - 1)) + ((walks a).length - 1) =
              ∑ b ∈ A, ((walks b).length - 1) := Finset.sum_erase_add _ _ ha
          change (head.append (boundary.append tail)).hops ≤ _
          omega
  have hsize : 0 < Q.vertices.length := by rw [Q.length_vertices]; omega
  obtain ⟨T, hT⟩ := hmain C.labels.card 0 C.labels le_rfl (Finset.Subset.refl _)
    hsize (by intro a ha; exact Nat.zero_le _) (fun i hi => C.covers i)
  let final : Route F s t (scale * (Q.searchWeight scale + ∑ a ∈ C.labels, debt a)) :=
    ⟨T.vertices, by simpa only [Q.vertex_zero] using T.endpoints,
      T.cost_le.trans_eq (congrArg (fun w : ℕ => ((scale * (w + ∑ a ∈ C.labels, debt a) : ℕ) : Distance))
        (Q.searchWeight_suffix_zero scale))⟩
  exact ⟨final, hT⟩

theorem search_route_subtype (Q : Path R G s t) (C : VertexCover Q.vertices.length L)
    (scale : ℕ) (hscale : 0 < scale) (hF : ∀ u v, F u v ≤ R.graph G u v)
    (debt : {a : L // a ∈ C.labels} → ℕ) (walks : {a : L // a ∈ C.labels} → List (Fin n))
    (hwalks : ∀ a : {a : L // a ∈ C.labels},
      Graph.Endpoints (walks a) (Q.vertex (C.interval a.val).1) (Q.vertex ((C.interval a.val).2 - 1)) ∧
        F.pathCost (walks a) ≤ ((scale * (Q.intervalSearch scale (C.interval a.val) + debt a) : ℕ) : Distance)) :
    ∃ T : Route F s t (scale * (Q.searchWeight scale + ∑ a : {a : L // a ∈ C.labels}, debt a)),
      T.hops ≤ C.labels.card + ∑ a : {a : L // a ∈ C.labels}, ((walks a).length - 1) := by
  let extendDebt : L → ℕ := fun a => if ha : a ∈ C.labels then debt ⟨a, ha⟩ else 0
  let extendWalk : L → List (Fin n) := fun a => if ha : a ∈ C.labels then walks ⟨a, ha⟩ else []
  have hw (a : L) (ha : a ∈ C.labels) :
      Graph.Endpoints (extendWalk a) (Q.vertex (C.interval a).1) (Q.vertex ((C.interval a).2 - 1)) ∧
        F.pathCost (extendWalk a) ≤ ((scale * (Q.intervalSearch scale (C.interval a) + extendDebt a) : ℕ) : Distance) := by
    simpa only [extendDebt, extendWalk, ha, ↓reduceDIte] using hwalks ⟨a, ha⟩
  have hd : (∑ a ∈ C.labels, extendDebt a) = ∑ a : {a : L // a ∈ C.labels}, debt a := by
    rw [← Finset.sum_coe_sort C.labels extendDebt]
    apply Finset.sum_congr rfl
    intro a _
    simp only [extendDebt, a.property, ↓reduceDIte]
  obtain ⟨T, hT⟩ := search_route Q C scale hscale hF extendDebt extendWalk hw
  have hh : (∑ a ∈ C.labels, ((extendWalk a).length - 1)) =
      ∑ a : {a : L // a ∈ C.labels}, ((walks a).length - 1) := by
    rw [← Finset.sum_coe_sort C.labels (fun a => (extendWalk a).length - 1)]
    apply Finset.sum_congr rfl
    intro a _
    simp only [extendWalk, a.property, ↓reduceDIte]
  let final : Route F s t (scale * (Q.searchWeight scale + ∑ a : {a : L // a ∈ C.labels}, debt a)) :=
    ⟨T.vertices, T.endpoints, by simpa only [hd] using T.cost_le⟩
  refine ⟨final, ?_⟩
  change T.hops ≤ _
  simpa only [hh] using hT

end

end StreamingSSSP.Hopset.VertexCover
