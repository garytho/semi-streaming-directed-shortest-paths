module

public import StreamingSSSP.Core.GlobalDefs

@[expose] public section

namespace StreamingSSSP.Core.Global

open StoredEdges

variable {n b : ℕ}

@[simp] theorem target_source (p : Problem n b) (input : List (Edge n)) :
    target p input p.source = 0 := Graph.dist_self _ _

theorem settled_cast (p : Problem n b) (input : List (Edge n)) {old : State n b} {r : ℕ}
    (hg : GlobalInvariant p input old r) {v : Fin n} (hv : v ∈ old.settled) :
    ((targetNat p input v : ℕ) : Distance) = target p input v :=
  distance_coe_untop (ne_top_of_lt (hg.settled_iff v |>.mp hv))

theorem block_sound (p : Problem n b) (input : List (Edge n)) (hA : 0 < p.scale)
    {old : State n b} {r : ℕ} (hg : GlobalInvariant p input old r)
    (i : Fin b) {v : Fin n} (hv : v ∈ p.blocks.get i) :
    target p input v ≤ roundDistance p.scale (blockDistance p input old.settled i v) := by
  apply Query.block_sound input p.blocks.toList p.scale hA p.source
    (show p.blocks.get i ∈ p.blocks.toList from by
      have h := List.get_mem p.blocks.toList ⟨i.val, by simpa using i.isLt⟩
      simpa only [List.get_eq_getElem, Vector.getElem_toList, Vector.get_eq_getElem] using h)
    (old.settled ∩ p.blocks.get i) (targetNat p input)
    (Finset.inter_subset_right)
  · intro u hu
    exact (settled_cast p input hg (Finset.mem_inter.mp hu).1).symm
  · exact hv

theorem block_self_le (p : Problem n b) (input : List (Edge n))
    (settled : Finset (Fin n)) (i : Fin b) {v : Fin n} (hv : v ∈ settled ∩ p.blocks.get i) :
    blockDistance p input settled i v ≤ ((p.scale * targetNat p input v : ℕ) : Distance) := by
  simpa only [blockDistance, blockSeed, scaledSeeds, hv, ↓reduceIte] using
    multiDist_le_seed (BlockSearch.blockGraph input (p.blocks.get i)) (blockSeed p input settled i) v

theorem known_bound (p : Problem n b) (input : List (Edge n)) {old : State n b} {r : ℕ}
    (hg : GlobalInvariant p input old r) (i : Fin b) (bs : BlockState n)
    (hb : BlockInvariant p input old.settled r i bs) {v : Fin n}
    (hv : v ∈ SparseLabels.support bs.known) :
    blockDistance p input old.settled i v ≤ ((p.scale * r : ℕ) : Distance) := by
  have hK : v ∈ old.settled ∩ p.blocks.get i := hb.known_support ▸ hv
  have hd := (hg.settled_iff v).mp (Finset.mem_inter.mp hK).1
  have hc := settled_cast p input hg (Finset.mem_inter.mp hK).1
  have hnat : targetNat p input v ≤ r := by
    have h := hd.le
    rw [← hc] at h
    exact_mod_cast h
  exact (block_self_le p input old.settled i hK).trans
    (WithTop.coe_le_coe.mpr (Nat.mul_le_mul_left p.scale hnat))

theorem block_seed_union (p : Problem n b) (input : List (Edge n))
    (settled U : Finset (Fin n)) (r : ℕ)
    (hU : ∀ v ∈ U, target p input v = (r : Distance)) (i : Fin b) :
    blockSeed p input (settled ∪ U) i =
      addSources (blockSeed p input settled i) (U ∩ p.blocks.get i) ((p.scale * r : ℕ) : Distance) := by
  funext v
  have hr (hv : v ∈ U) : targetNat p input v = r := by
    simp only [targetNat, hU v hv]
    rfl
  by_cases hvU : v ∈ U
  · by_cases hvS : v ∈ settled <;> by_cases hvB : v ∈ p.blocks.get i <;>
      simp [blockSeed, scaledSeeds, addSources, hvU, hvS, hvB, hr hvU]
  · by_cases hvS : v ∈ settled <;> by_cases hvB : v ∈ p.blocks.get i <;>
      simp [blockSeed, scaledSeeds, addSources, hvU, hvS, hvB]

theorem block_distance_union (p : Problem n b) (input : List (Edge n))
    (settled U : Finset (Fin n)) (r : ℕ)
    (hU : ∀ v ∈ U, target p input v = (r : Distance)) (i : Fin b) :
    blockDistance p input (settled ∪ U) i =
      multiDist (BlockSearch.blockGraph input (p.blocks.get i))
        (addSources (blockSeed p input settled i) (U ∩ p.blocks.get i)
          ((p.scale * r : ℕ) : Distance)) := by
  unfold blockDistance
  rw [block_seed_union p input settled U r hU i]

theorem found_exact_round (p : Problem n b) (input : List (Edge n)) (hA : 0 < p.scale)
    {old : State n b} {r : ℕ} (hg : GlobalInvariant p input old r) (i : Fin b) :
    ∀ v ∈ found (p.blocks.get i) (old.settled ∩ p.blocks.get i)
        (blockDistance p input old.settled i) (p.scale * r),
      target p input v = (r : Distance) := by
  intro v hv
  obtain ⟨hvB, hvK, hd⟩ := Finset.mem_filter.mp hv
  have hvs : v ∉ old.settled := fun h => hvK (Finset.mem_inter.mpr ⟨h, hvB⟩)
  have hlow : (r : Distance) ≤ target p input v :=
    le_of_not_gt (fun h => hvs ((hg.settled_iff v).mpr h))
  have hupp : target p input v ≤ (r : Distance) :=
    (block_sound p input hA hg i hvB).trans ((roundDistance_le_iff hA _).mpr hd)
  exact le_antisymm hupp hlow

theorem block_empty (p : Problem n b) (input : List (Edge n)) (i : Fin b) (v : Fin n) :
    blockDistance p input ∅ i v = ⊤ := by
  simp [blockDistance, blockSeed, scaledSeeds, multiDist]

theorem initial_invariant (p : Problem n b) (input : List (Edge n)) :
    Invariant p input (initial p) 0 := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      simp [initial, not_lt_of_ge (show (0 : Distance) ≤ target p input v from bot_le)]
    · simp [initial, SparseLabels.support]
    · intro v hv
      have hv' : v = p.source := by simpa [initial, SparseLabels.support] using hv
      subst v
      simp [initial, SparseLabels.get, target_source]
    · simp [initial]
  · intro i
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [initial, emptyBlock, SparseLabels.support]
    · intro v hv
      simp [initial, emptyBlock, SparseLabels.support] at hv
    · simp [initial, emptyBlock]
    · simpa [initial, emptyBlock] using (le_top : (0 : Distance) ≤ ⊤)
    · intro v _ _
      simp [initial, emptyBlock, block_empty]
    · intro _
      have he : blockDistance p input ∅ i = (fun _ => ⊤) := funext (block_empty p input i)
      simp only [initial, Vector.get_replicate, emptyBlock]
      rw [he]
      simp [nextDistance, SparseLabels.support]
    · simp [initial, emptyBlock, ScheduleCharge.valid]
    · simp [initial, emptyBlock, SparseLabels.support]
    · simp [initial, emptyBlock]

end StreamingSSSP.Core.Global
