module

public import StreamingReachability.Core.GlobalSearch

@[expose] public section

namespace StreamingReachability.Core.Global

open StoredEdges

variable {n b : ℕ}

theorem ordinary_mem (p : Problem n b) (input : List (Edge n)) (r : ℕ) (old : State n b)
    (v : Fin n) :
    v ∈ ordinary p input r old ↔ ∃ e ∈ input, e.target = v ∧
      e.source ∈ old.settled ∧ v ∉ old.settled ∧
      SparseLabels.get old.labels e.source + (ceilNat p.scale e.weight : Distance) ≤ (r : Distance) := by
  have h (xs : List (Edge n)) (C : Finset (Fin n)) :
      v ∈ xs.foldl (ordinaryStep p.scale r old) C ↔ v ∈ C ∨
        ∃ e ∈ xs, e.target = v ∧ e.source ∈ old.settled ∧ v ∉ old.settled ∧
          SparseLabels.get old.labels e.source + (ceilNat p.scale e.weight : Distance) ≤ (r : Distance) := by
    induction xs generalizing C with
    | nil => simp
    | cons e es ih =>
        rw [List.foldl_cons, ih]
        by_cases he : e.source ∈ old.settled ∧ e.target ∉ old.settled ∧
            SparseLabels.get old.labels e.source + (ceilNat p.scale e.weight : Distance) ≤ (r : Distance)
        · have ht : v = e.target ↔ e.target = v ∧ e.source ∈ old.settled ∧
              v ∉ old.settled ∧ SparseLabels.get old.labels e.source +
                (ceilNat p.scale e.weight : Distance) ≤ (r : Distance) := by
            constructor
            · intro h; subst v; exact ⟨rfl, he⟩
            · intro h; exact h.1.symm
          rw [show ordinaryStep p.scale r old C e = insert e.target C from ite_eq_left he]
          simp only [Finset.mem_insert, List.mem_cons, exists_eq_or_imp]
          rw [ht]
          tauto
        · rw [show ordinaryStep p.scale r old C e = C from ite_eq_right he]
          simp only [List.mem_cons, exists_eq_or_imp]
          have hno : ¬ (e.target = v ∧ e.source ∈ old.settled ∧ v ∉ old.settled ∧
              SparseLabels.get old.labels e.source + (ceilNat p.scale e.weight : Distance) ≤ (r : Distance)) := by
            rintro ⟨hv, hs, hnot, hw⟩
            exact he ⟨hs, by simpa only [hv] using hnot, hw⟩
          tauto
  simpa [ordinary] using h input ∅

theorem newVertices_exact (p : Problem n b) (input : List (Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < p.scale)
    {old : State n b} {r : ℕ} (hg : GlobalInvariant p input old r)
    (hb : ∀ i, BlockInvariant p input old.settled r i (old.blocks.get i))
    (results : Vector (BlockResult n) b)
    (hr : ∀ i, SearchInvariant p input old.settled r i (old.blocks.get i) (results.get i)) :
    ∀ v, v ∈ newVertices p input r old results ↔ target p input v = (r : Distance) := by
  intro v
  have hnot (hd : target p input v = (r : Distance)) : v ∉ old.settled := by
    intro hv
    have hlt := (hg.settled_iff v).mp hv
    rw [hd] at hlt
    exact lt_irrefl _ hlt
  constructor
  · intro hv
    obtain ⟨hv, hvnot⟩ := Finset.mem_sdiff.mp hv
    have hlo : (r : Distance) ≤ target p input v :=
      le_of_not_gt (fun h => hvnot ((hg.settled_iff v).mpr h))
    have hupp : target p input v ≤ (r : Distance) := by
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · by_cases hr0 : r = 0
          · have heq : v = p.source := by simpa only [hr0, ↓reduceIte, Finset.mem_singleton] using hv
            subst v
            simp [hr0]
          · simp [hr0] at hv
        · obtain ⟨e, he, htarget, hsource, _, hw⟩ := (ordinary_mem p input r old v).mp hv
          have hlabels := hg.label_exact e.source (by rw [hg.label_support]; exact Finset.mem_union_left _ hsource)
          have hqe : queryGraph input p.blocks.toList p.scale e.source v ≤ (ceilNat p.scale e.weight : Distance) := by
            apply (Query.le_ordinary input p.blocks.toList p.scale e.source v).trans
            have h := graphOfEdges_le_edge input he
            rw [htarget] at h
            exact roundDistance_mono hA h
          calc
            target p input v ≤ target p input e.source +
                queryGraph input p.blocks.toList p.scale e.source v := Graph.dist_le_dist_add_edge _ _ _ _
            _ ≤ target p input e.source + (ceilNat p.scale e.weight : Distance) := add_le_add le_rfl hqe
            _ ≤ (r : Distance) := by rwa [hlabels] at hw
      · obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hv
        have hf := (hr i).found_eq ▸ hvi
        rw [(hb i).known_support] at hf
        exact (found_exact_round p input hA hg i v hf).le
    exact le_antisymm hupp hlo
  · intro hd
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hnot hd⟩
    rcases Query.predecessor_split input hp p.blocks.toList p.scale hA p.source v r hd with
      ⟨hvs, hr0⟩ | ⟨u, hdu, hlast⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp [hr0, hvs]
    have hus : u ∈ old.settled := (hg.settled_iff u).mpr hdu
    rcases hlast with ⟨e, he, hsu, htv, hw⟩ | ⟨B, hB, huB, hvB, hw⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply (ordinary_mem p input r old v).mpr
      refine ⟨e, he, htv, hsu ▸ hus, hnot hd, ?_⟩
      have hlabels := hg.label_exact u (by rw [hg.label_support]; exact Finset.mem_union_left _ hus)
      simpa only [hsu, hlabels, target] using hw
    · obtain ⟨k, hk⟩ := List.mem_iff_get.mp hB
      let i : Fin b := ⟨k.val, by simpa using k.isLt⟩
      have hi : p.blocks.get i = B := by
        simpa only [List.get_eq_getElem, Vector.getElem_toList, Vector.get_eq_getElem] using hk
      have huk : u ∈ old.settled ∩ p.blocks.get i := Finset.mem_inter.mpr ⟨hus, hi ▸ huB⟩
      have hbnum : blockDistance p input old.settled i v ≤ ((p.scale * r : ℕ) : Distance) := by
        apply (roundDistance_le_iff hA _).mp
        calc
          roundDistance p.scale (blockDistance p input old.settled i v) =
              (old.settled ∩ p.blocks.get i).inf (fun a =>
                (targetNat p input a : Distance) +
                  roundDistance p.scale ((BlockSearch.blockGraph input (p.blocks.get i)).dist a v)) :=
            closure_rounding_once _ p.scale hA _ _ _
          _ ≤ (targetNat p input u : Distance) +
                roundDistance p.scale ((BlockSearch.blockGraph input (p.blocks.get i)).dist u v) :=
            Finset.inf_le huk
          _ ≤ (r : Distance) := by rw [settled_cast p input hg hus, hi]; exact hw
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      rw [(hr i).found_eq]
      apply Finset.mem_filter.mpr
      refine ⟨hi ▸ hvB, ?_, hbnum⟩
      intro hvk
      rw [(hb i).known_support] at hvk
      exact hnot hd (Finset.mem_inter.mp hvk).1

theorem global_commit (p : Problem n b) (input : List (Edge n)) {old : State n b} {r : ℕ}
    (hg : GlobalInvariant p input old r) (U : Finset (Fin n))
    (hU : ∀ v, v ∈ U ↔ target p input v = (r : Distance))
    (blocks : Vector (BlockState n) b) :
    GlobalInvariant p input
      ⟨SparseLabels.addNew old.labels U (r : Distance), old.settled ∪ U, blocks⟩ (r + 1) := by
  refine ⟨?_, ?_, ?_, SparseLabels.nodup_addNew old.labels U _ hg.label_unique⟩
  · intro v
    rw [Finset.mem_union, hg.settled_iff v, hU v, distance_lt_succ_iff]
    constructor
    · rintro (hlt | heq)
      · exact hlt.le
      · exact heq.le
    · exact lt_or_eq_of_le
  · rw [SparseLabels.support_addNew, hg.label_support]
    ext v
    simp only [Finset.mem_union]
    tauto
  · intro v hv
    rw [SparseLabels.support_addNew] at hv
    rw [SparseLabels.get_addNew]
    by_cases hold : v ∈ SparseLabels.support old.labels
    · simpa only [hold, ↓reduceIte] using hg.label_exact v hold
    · have hnew : v ∈ U := (Finset.mem_union.mp hv).resolve_left hold
      simp only [hold, hnew, ↓reduceIte]
      exact ((hU v).mp hnew).symm

end StreamingReachability.Core.Global
