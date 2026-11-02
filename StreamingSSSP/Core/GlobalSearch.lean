module

public import StreamingSSSP.Core.GlobalFacts

@[expose] public section

namespace StreamingSSSP.Core.Global

open StoredEdges

variable {n b : ℕ}

structure SearchInvariant (p : Problem n b) (input : List (Edge n))
    (settled : Finset (Fin n)) (r : ℕ) (i : Fin b)
    (old : BlockState n) (result : BlockResult n) : Prop where
  found_eq : result.vertices = found (p.blocks.get i) (SparseLabels.support old.known)
    (blockDistance p input settled i) (p.scale * r)
  support_eq : SparseLabels.support result.state.known =
    SparseLabels.support old.known ∪ result.vertices
  known_exact : ∀ v ∈ SparseLabels.support result.state.known,
    SparseLabels.get result.state.known v = blockDistance p input settled i v
  known_bounded : ∀ v ∈ SparseLabels.support result.state.known,
    blockDistance p input settled i v ≤ ((p.scale * r : ℕ) : Distance)
  known_unique : (result.state.known.map Prod.fst).Nodup
  next_lower : ((r + 1 : ℕ) : Distance) ≤ result.state.next
  next_upper : ∀ v ∈ p.blocks.get i, v ∉ SparseLabels.support result.state.known →
    result.state.next ≤ roundDistance p.scale (blockDistance p input settled i v)
  next_exact : result.state.charge.dirty = false →
    result.state.next = roundDistance p.scale
      (nextDistance (p.blocks.get i) (SparseLabels.support result.state.known)
        (blockDistance p input settled i))
  charge_valid : ScheduleCharge.valid result.state.charge
  insertion_count : result.state.charge.insertions = (SparseLabels.support result.state.known).card
  reservation_bound : result.state.reservations ≤
    4 * (p.blocks.get i).card * (result.state.charge.insertions + result.state.charge.searches)

theorem searchOne_invariant (hn : 0 < n) (p : Problem n b) (input : List (Edge n))
    (hA : 0 < p.scale) {old : State n b} {r : ℕ}
    (hg : GlobalInvariant p input old r) (i : Fin b) (bs : BlockState n)
    (hb : BlockInvariant p input old.settled r i bs) :
    SearchInvariant p input old.settled r i bs (searchOne hn p input r i bs) := by
  let B := p.blocks.get i
  let K := SparseLabels.support bs.known
  let d := blockDistance p input old.settled i
  by_cases hs : bs.next = (r : Distance)
  · have hseed : ∀ u, u ∉ K → blockSeed p input old.settled i u = ⊤ := by
      intro u hu
      have hu' : u ∉ old.settled ∩ p.blocks.get i := by
        simpa only [K, hb.known_support] using hu
      unfold blockSeed scaledSeeds
      rw [ite_eq_right hu']
    have hinit : ∀ u, (SparseLabels.vector bs.known).get u =
        if u ∈ K then d u else ⊤ := by
      intro u
      rw [SparseLabels.vector_get]
      by_cases hu : u ∈ K
      · simpa only [hu, ↓reduceIte] using hb.known_exact u hu
      · simpa only [hu, ↓reduceIte] using SparseLabels.get_eq_top_of_not_mem bs.known hu
    obtain ⟨out, hout, hU, hrec, hnext, _, hres, _⟩ :=
      BlockSearch.search_correct_and_cost hn B K (p.scale * r)
        (SparseLabels.vector bs.known) input (blockSeed p input old.settled i) hseed hinit
    change out.vertices = found B K d (p.scale * r) at hU
    change out.nextNumerator = nextDistance B (K ∪ out.vertices) d at hnext
    have hr : out.records = SparseLabels.ofSet out.vertices d := hrec
    have hdis : Disjoint K out.vertices := by
      rw [hU]
      exact Finset.disjoint_left.mpr (fun _ hk hv => (Finset.mem_filter.mp hv).2.1 hk)
    have hsupport : SparseLabels.support (bs.known ++ out.records) = K ∪ out.vertices := by
      rw [SparseLabels.support_append, hr, SparseLabels.support_ofSet]
    have hlabels : ∀ v ∈ K ∪ out.vertices,
        SparseLabels.get (bs.known ++ out.records) v = d v := by
      intro v hv
      rw [SparseLabels.get_append, hr, SparseLabels.get_ofSet]
      by_cases hk : v ∈ K
      · have hvnot : v ∉ out.vertices := fun hv => Finset.disjoint_left.mp hdis hk hv
        rw [ite_eq_right hvnot, min_top_right]
        exact hb.known_exact v hk
      · have hvU : v ∈ out.vertices := (Finset.mem_union.mp hv).resolve_left hk
        rw [SparseLabels.get_eq_top_of_not_mem bs.known hk, ite_eq_left hvU, min_top_left]
    have hbounded : ∀ v ∈ K ∪ out.vertices, d v ≤ ((p.scale * r : ℕ) : Distance) := by
      intro v hv
      rcases Finset.mem_union.mp hv with hk | hvU
      · exact known_bound p input hg i bs hb hk
      · rw [hU] at hvU
        exact (Finset.mem_filter.mp hvU).2.2
    have hprogress : bs.charge.dirty = true ∨ 0 < out.vertices.card := by
      by_cases hd : bs.charge.dirty = true
      · exact Or.inl hd
      · have hf : bs.charge.dirty = false := by cases h : bs.charge.dirty <;> simp_all
        have he : roundDistance p.scale (nextDistance B K d) = (r : Distance) :=
          (hb.next_exact hf).symm.trans hs
        exact Or.inr (by rw [hU]; exact Finset.card_pos.mpr (scheduled_nonempty p.scale hA B K d r he))
    have hnex := next_round_bounds p.scale hA B K d r
    rw [searchOne, searchBlock, ite_eq_left hs, hout]
    dsimp only [Option.getD_some]
    refine ⟨hU, hsupport, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      exact hlabels v (hsupport ▸ hv)
    · intro v hv
      exact hbounded v (hsupport ▸ hv)
    · rw [hr]
      exact SparseLabels.nodup_append bs.known _ hb.known_unique
        (SparseLabels.nodup_ofSet _ _) (by simpa only [SparseLabels.support_ofSet] using hdis)
    · rw [hnext, hU]
      exact hnex.1
    · intro v hvB hvnot
      rw [hnext]
      rw [hsupport, hU] at hvnot
      rw [hU]
      exact hnex.2 v hvB hvnot
    · intro _
      rw [hnext, hsupport]
    · exact ScheduleCharge.searched_valid bs.charge hb.charge_valid out.vertices.card hprogress
    · dsimp only [ScheduleCharge.searched]
      rw [hsupport, Finset.card_union_of_disjoint hdis, hb.insertion_count]
    · have hbudget := hb.reservation_bound
      dsimp only [ScheduleCharge.searched]
      nlinarith only [hbudget, hres]
  · have hlt : (r : Distance) < bs.next := lt_of_le_of_ne hb.next_lower (Ne.symm hs)
    have hU : found B K d (p.scale * r) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨v, hv⟩
      obtain ⟨hvB, hvK, hd⟩ := Finset.mem_filter.mp hv
      have hvs : v ∉ old.settled := by
        intro hvS
        exact hvK (by
          change v ∈ SparseLabels.support bs.known
          rw [hb.known_support]
          exact Finset.mem_inter.mpr ⟨hvS, hvB⟩)
      have he := (hb.next_upper v hvB hvs).trans ((roundDistance_le_iff hA _).mpr hd)
      exact (not_le_of_gt hlt) he
    rw [searchOne, searchBlock, ite_eq_right hs]
    refine ⟨hU.symm, by simp only [Finset.union_empty], hb.known_exact, ?_,
      hb.known_unique, distance_succ_le hlt, ?_, hb.next_exact, hb.charge_valid,
      hb.insertion_count, hb.reservation_bound⟩
    · intro v hv
      exact known_bound p input hg i bs hb hv
    · intro v hvB hvnot
      apply hb.next_upper v hvB
      intro hvS
      exact hvnot (by rw [hb.known_support]; exact Finset.mem_inter.mpr ⟨hvS, hvB⟩)

end StreamingSSSP.Core.Global
