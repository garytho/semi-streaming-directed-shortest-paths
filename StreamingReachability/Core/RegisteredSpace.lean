module

public import StreamingReachability.Core.BatchStatistics
public import StreamingReachability.Core.RecordGuardSeen

@[expose] public section

namespace StreamingReachability.Core.RecordGuard

variable {n nb ns nq : ℕ}

def verticesAt (keys : Finset (Key n nq)) (j : Fin nq) : Finset (Fin n) :=
  Finset.univ.filter fun v => (j, v) ∈ keys

theorem weight_sections (c : Shared.Catalog n nb ns nq) (keys : Finset (Key n nq)) :
    weight c keys = ∑ j : Fin nq, ((verticesAt keys j).card +
      ∑ i : Fin nb, (verticesAt keys j ∩ c.blocks.get i).card) := by
  have hsum : (∑ key : Key n nq, if key ∈ keys then charge c key else 0) = weight c keys := by
    rw [← Finset.sum_filter]
    simp [weight]
  rw [← hsum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter]
  change (verticesAt keys j).sum (fun v => charge c (j, v)) = _
  simp_rw [charge_eq]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.card_filter]
    congr 1

end StreamingReachability.Core.RecordGuard

namespace StreamingReachability.Core.GuardedDriver

variable {n nb ns nq : ℕ}

def Cover (registry : RecordGuard.Registry n nq) (states : BatchDriver.States n nb nq) : Prop :=
  ∀ j, ∀ v ∈ SparseLabels.support (states.get j).labels, (j, v) ∈ registry.seen

theorem cover_mono (before after : RecordGuard.Registry n nq) (states : BatchDriver.States n nb nq)
    (hc : Cover before states) (hs : before.seen ⊆ after.seen) : Cover after states :=
  fun j v hv => hs (hc j v hv)

theorem registered_records (c : Shared.Catalog n nb ns nq) (registry : RecordGuard.Registry n nq)
    (states : BatchDriver.States n nb nq)
    (hshape : ∀ j, SparseDriver.Shape (states.get j))
    (hcover : Cover registry states)
    (hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (states.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (states.get j).cache i).known ⊆
        SparseLabels.support (states.get j).labels ∩ c.blocks.get i) :
    BatchDriver.recordCount states ≤ RecordGuard.weight c registry.seen := by
  rw [RecordGuard.weight_sections]
  unfold BatchDriver.recordCount
  apply Finset.sum_le_sum
  intro j _
  have hlabelsub : SparseLabels.support (states.get j).labels ⊆ RecordGuard.verticesAt registry.seen j := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcover j v hv⟩
  have hl : (states.get j).labels.length ≤ (RecordGuard.verticesAt registry.seen j).card := by
    rw [SparseLabels.length_eq_card _ (hshape j).labels_unique]
    exact Finset.card_le_card hlabelsub
  have hm := RecordMap.sum_values_le Global.emptyBlock (states.get j).cache (hshape j).unique
    (fun bs => bs.known.length)
  have hmembership : SparseDriver.membershipRecords (states.get j) ≤
      ∑ i : Fin nb, (RecordGuard.verticesAt registry.seen j ∩ c.blocks.get i).card := by
    apply hm.trans
    apply Finset.sum_le_sum
    intro i _
    rw [SparseLabels.length_eq_card _ (hknown j i).1]
    apply Finset.card_le_card
    exact ((hknown j i).2).trans
      (Finset.inter_subset_inter hlabelsub (Finset.Subset.refl _))
  exact Nat.add_le_add hl hmembership

theorem registered_state_space (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (states : BatchDriver.States n nb nq)
    (hv : RecordGuard.Valid c budget registry) (hshape : ∀ j, SparseDriver.Shape (states.get j))
    (hcover : Cover registry states)
    (hknown : ∀ j i,
      ((RecordMap.get Global.emptyBlock (states.get j).cache i).known.map Prod.fst).Nodup ∧
      SparseLabels.support (RecordMap.get Global.emptyBlock (states.get j).cache i).known ⊆
        SparseLabels.support (states.get j).labels ∩ c.blocks.get i) :
    BatchDriver.stateCells states ≤ 2 + 13 * budget := by
  have hr := registered_records c registry states hshape hcover hknown
  have hc := BatchDriver.stateCells_bound states hshape
  have hb : RecordGuard.weight c registry.seen ≤ budget := hv.1 ▸ hv.2
  nlinarith only [hr, hc, hb]

end StreamingReachability.Core.GuardedDriver
