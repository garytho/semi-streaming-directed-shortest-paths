module

public import StreamingSSSP.Core.GuardedRoundSpace

@[expose] public section

namespace StreamingSSSP.Core.SparseDriver

variable {n b : ℕ}

def cacheCells (cache : RecordMap.Map (Fin b) (Global.BlockState n)) : ℕ :=
  8 * cache.length + 4 * (cache.map fun pair => pair.2.known.length).sum

theorem partialCache_active (p : Parameters n b) (r : ℕ) (U : Finset (Fin n))
    (indices : List (Fin b)) (cache : RecordMap.Map (Fin b) (Global.BlockState n)) (ha : Active cache) :
    Active (RecordMap.foldModify Global.emptyBlock (fun i => Global.externalBlock p.scale r (p.blockAt i) U)
      (fun i => decide (0 < (U ∩ p.blockAt i).card)) indices cache) := by
  induction indices generalizing cache with
  | nil => exact ha
  | cons i is ih =>
      unfold RecordMap.foldModify
      rw [List.foldl_cons]
      apply ih
      split_ifs with hg
      · exact all_set (fun pair : Fin b × Global.BlockState n => 0 < pair.2.known.length) cache ha i _
          (external_active _ _ _ _ _ (of_decide_eq_true hg))
      · exact ha

theorem partialCache_lengths (p : Parameters n b) (r : ℕ) (U : Finset (Fin n))
    (indices : List (Fin b)) (hu : indices.Nodup) (cache : RecordMap.Map (Fin b) (Global.BlockState n))
    (i : Fin b) :
    (RecordMap.get Global.emptyBlock
      (RecordMap.foldModify Global.emptyBlock (fun i => Global.externalBlock p.scale r (p.blockAt i) U)
        (fun i => decide (0 < (U ∩ p.blockAt i).card)) indices cache) i).known.length ≤
      (RecordMap.get Global.emptyBlock (commitCache p r U cache) i).known.length := by
  rw [RecordMap.get_foldModify _ _ _ _ hu, get_commitCache]
  split_ifs
  · exact Nat.le_refl _
  · simp only [Global.externalBlock, List.length_append]
    exact Nat.le_add_right _ _

end StreamingSSSP.Core.SparseDriver

namespace StreamingSSSP.Core.GuardedDriver

variable {n nb ns nq : ℕ}

theorem cache_section_bound (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (hv : RecordGuard.Valid c budget registry) (j : Fin nq)
    (cache : RecordMap.Map (Fin nb) (Global.BlockState n))
    (hu : RecordMap.Unique cache) (ha : SparseDriver.Active cache)
    (hl : ∀ i, (RecordMap.get Global.emptyBlock cache i).known.length ≤
      (RecordGuard.verticesAt registry.seen j ∩ c.blocks.get i).card) :
    SparseDriver.cacheCells cache ≤ 12 * budget := by
  have hsum := RecordMap.sum_values_le Global.emptyBlock cache hu (fun bs => bs.known.length)
  have hpoint : (∑ i : Fin nb, (RecordMap.get Global.emptyBlock cache i).known.length) ≤
      ∑ i : Fin nb, (RecordGuard.verticesAt registry.seen j ∩ c.blocks.get i).card :=
    Finset.sum_le_sum (fun i _ => hl i)
  have hj : (∑ i : Fin nb, (RecordGuard.verticesAt registry.seen j ∩ c.blocks.get i).card) ≤
      RecordGuard.weight c registry.seen := by
    rw [RecordGuard.weight_sections]
    calc
      _ ≤ (RecordGuard.verticesAt registry.seen j).card +
          ∑ i : Fin nb, (RecordGuard.verticesAt registry.seen j ∩ c.blocks.get i).card :=
        Nat.le_add_left _ _
      _ ≤ _ := Finset.single_le_sum
        (f := fun q : Fin nq => (RecordGuard.verticesAt registry.seen q).card +
          ∑ i : Fin nb, (RecordGuard.verticesAt registry.seen q ∩ c.blocks.get i).card)
        (s := Finset.univ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hlen := SparseDriver.active_count_le cache ha
  have hweight : RecordGuard.weight c registry.seen ≤ budget := hv.1 ▸ hv.2
  unfold SparseDriver.cacheCells
  omega

theorem mixed_state_space (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (hv : RecordGuard.Valid c budget registry)
    (old new mixed : BatchDriver.States n nb nq)
    (hold : ∀ j, SparseDriver.Shape (old.get j)) (hnew : ∀ j, SparseDriver.Shape (new.get j))
    (hco : Cover registry old) (hcn : Cover registry new)
    (hko : ∀ j i,
      ((RecordMap.get Global.emptyBlock (old.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (old.get j).cache i).known ⊆
        SparseLabels.support (old.get j).labels ∩ c.blocks.get i)
    (hkn : ∀ j i,
      ((RecordMap.get Global.emptyBlock (new.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (new.get j).cache i).known ⊆
        SparseLabels.support (new.get j).labels ∩ c.blocks.get i)
    (hm : ∀ j, mixed.get j = old.get j ∨ mixed.get j = new.get j) :
    BatchDriver.stateCells mixed ≤ 2 + 13 * budget := by
  apply registered_state_space c budget registry mixed hv
  · intro j
    rcases hm j with he | he
    · rw [he]; exact hold j
    · rw [he]; exact hnew j
  · intro j v hv
    rcases hm j with he | he
    · rw [he] at hv; exact hco j v hv
    · rw [he] at hv; exact hcn j v hv
  · intro j i
    rcases hm j with he | he
    · rw [he]; exact hko j i
    · rw [he]; exact hkn j i

end StreamingSSSP.Core.GuardedDriver
