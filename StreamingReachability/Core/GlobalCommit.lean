module

public import StreamingReachability.Core.GlobalFrontier

@[expose] public section

namespace StreamingReachability.Core.Global

open StoredEdges

variable {n b : ℕ}

theorem insertExternal_invariant (p : Problem n b) (input : List (Edge n)) (hA : 0 < p.scale)
    {old : State n b} {r : ℕ} (hg : GlobalInvariant p input old r) (i : Fin b)
    (hb : BlockInvariant p input old.settled r i (old.blocks.get i))
    (result : BlockResult n)
    (hs : SearchInvariant p input old.settled r i (old.blocks.get i) result)
    (U : Finset (Fin n)) (hU : ∀ v, v ∈ U ↔ target p input v = (r : Distance)) :
    BlockInvariant p input (old.settled ∪ U) (r + 1) i
      (insertExternal p r U i result.state) := by
  let B := p.blocks.get i
  let K := SparseLabels.support result.state.known
  let E := (U ∩ B) \ K
  let L : Distance := ((p.scale * r : ℕ) : Distance)
  let d := blockDistance p input old.settled i
  let dnew := blockDistance p input (old.settled ∪ U) i
  have hF : result.vertices ⊆ U ∩ B := by
    intro v hv
    have hfound := hs.found_eq ▸ hv
    have hvB := (Finset.mem_filter.mp hfound).1
    rw [hb.known_support] at hfound
    exact Finset.mem_inter.mpr
      ⟨(hU v).mpr (found_exact_round p input hA hg i v hfound), hvB⟩
  have hK : K = (old.settled ∩ B) ∪ result.vertices := hs.support_eq.trans (congrArg (· ∪ result.vertices) hb.known_support)
  have hsupport : K ∪ E = (old.settled ∪ U) ∩ B := by
    ext v
    have hvF : v ∈ result.vertices → v ∈ U ∧ v ∈ B := fun h =>
      Finset.mem_inter.mp (hF h)
    simp only [E, hK, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdis : Disjoint K E :=
    Finset.disjoint_left.mpr (fun _ hk he => (Finset.mem_sdiff.mp he).2 hk)
  have hlabels_support : SparseLabels.support
      (result.state.known ++ SparseLabels.ofSet E (fun _ => L)) = K ∪ E := by
    rw [SparseLabels.support_append, SparseLabels.support_ofSet]
  have hadd := block_distance_union p input old.settled U r (fun v hv => (hU v).mp hv) i
  have hpres : ∀ v ∈ K, dnew v = d v := by
    intro v hv
    change blockDistance p input (old.settled ∪ U) i v = _
    rw [hadd]
    exact addSources_preserves _ _ _ _ v (hs.known_bounded v hv)
  have hexternal : ∀ v ∈ E, dnew v = L := by
    intro v hv
    obtain ⟨hvUB, hvK⟩ := Finset.mem_sdiff.mp hv
    have hvB := (Finset.mem_inter.mp hvUB).2
    have hOld : v ∉ SparseLabels.support (old.blocks.get i).known := by
      intro hk
      apply hvK
      change v ∈ SparseLabels.support result.state.known
      rw [hs.support_eq]
      exact Finset.mem_union_left _ hk
    have hlarge : L ≤ d v := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hd
      have hfv : v ∈ result.vertices := by
        rw [hs.found_eq]
        exact Finset.mem_filter.mpr ⟨hvB, hOld, hd⟩
      apply hvK
      change v ∈ SparseLabels.support result.state.known
      rw [hs.support_eq]
      exact Finset.mem_union_right _ hfv
    change blockDistance p input (old.settled ∪ U) i v = L
    rw [hadd]
    exact addSources_external _ _ _ L hvUB hlarge
  have hnew0 : E.card = 0 → dnew = d := by
    intro he
    have hempty := Finset.card_eq_zero.mp he
    change blockDistance p input (old.settled ∪ U) i = d
    rw [hadd]
    apply addSources_redundant
    intro v hv
    apply hs.known_bounded
    by_contra hnot
    have hmem : v ∈ E := Finset.mem_sdiff.mpr ⟨hv, hnot⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have hlabels : ∀ v ∈ K ∪ E,
      SparseLabels.get (result.state.known ++ SparseLabels.ofSet E (fun _ => L)) v = dnew v := by
    intro v hv
    rw [SparseLabels.get_append, SparseLabels.get_ofSet]
    by_cases hk : v ∈ K
    · have hnot : v ∉ E := fun he => Finset.disjoint_left.mp hdis hk he
      rw [ite_eq_right hnot, min_top_right, hs.known_exact v hk, hpres v hk]
    · have he : v ∈ E := (Finset.mem_union.mp hv).resolve_left hk
      rw [SparseLabels.get_eq_top_of_not_mem result.state.known hk, ite_eq_left he,
        min_top_left, hexternal v he]
  have hgnew := global_commit p input hg U hU old.blocks
  unfold insertExternal
  change BlockInvariant p input (old.settled ∪ U) (r + 1) i
    { known := result.state.known ++ SparseLabels.ofSet E (fun _ => L)
      next := if E.card = 0 then result.state.next else ((r + 1 : ℕ) : Distance)
      charge := if E.card = 0 then result.state.charge
        else ScheduleCharge.externalInsert result.state.charge E.card
      reservations := result.state.reservations }
  refine ⟨hlabels_support.trans hsupport, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hlabels v (hlabels_support ▸ hv)
  · exact SparseLabels.nodup_append result.state.known _ hs.known_unique
      (SparseLabels.nodup_ofSet _ _) (by simpa only [SparseLabels.support_ofSet] using hdis)
  · split_ifs
    · exact hs.next_lower
    · exact le_rfl
  · intro v hvB hvnot
    by_cases he : E.card = 0
    · rw [ite_eq_left he]
      have hdnew := congrFun (hnew0 he) v
      change result.state.next ≤ roundDistance p.scale (dnew v)
      rw [hdnew]
      apply hs.next_upper v hvB
      intro hk
      apply hvnot
      have hmem : v ∈ K ∪ E := Finset.mem_union_left _ hk
      exact (Finset.mem_inter.mp (hsupport ▸ hmem)).1
    · rw [ite_eq_right he]
      have hdist : ((r + 1 : ℕ) : Distance) ≤ target p input v :=
        le_of_not_gt (fun h => hvnot ((hgnew.settled_iff v).mpr h))
      exact hdist.trans (block_sound p input hA hgnew i hvB)
  · intro hd
    by_cases he : E.card = 0
    · simp only [he, ↓reduceIte] at hd ⊢
      have hde : blockDistance p input (old.settled ∪ U) i =
          blockDistance p input old.settled i := hnew0 he
      rw [hs.next_exact hd, hde]
      have hempty := Finset.card_eq_zero.mp he
      rw [hlabels_support, hempty, Finset.union_empty]
    · simp only [he, ↓reduceIte, ScheduleCharge.externalInsert] at hd
      cases hd
  · by_cases he : E.card = 0
    · simpa only [he, ↓reduceIte] using hs.charge_valid
    · simpa only [he, ↓reduceIte] using
        ScheduleCharge.external_valid result.state.charge hs.charge_valid E.card (by omega)
  · rw [hlabels_support, Finset.card_union_of_disjoint hdis]
    by_cases he : E.card = 0 <;>
      simp [he, ScheduleCharge.externalInsert, hs.insertion_count, K]
  · have hbudget := hs.reservation_bound
    by_cases he : E.card = 0
    · simpa only [he, ↓reduceIte] using hbudget
    · simp only [he, ↓reduceIte, ScheduleCharge.externalInsert]
      nlinarith only [hbudget]

end StreamingReachability.Core.Global
