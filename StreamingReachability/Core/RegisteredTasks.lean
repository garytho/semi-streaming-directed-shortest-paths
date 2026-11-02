module

public import StreamingReachability.Core.RegisteredSpace
public import StreamingReachability.Core.GuardedEngineProofs

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

def taskRecords : Shared.Engine.Task n nb nq → SparseLabels.Labels (Fin n)
  | .active job => job.sources
  | .finished out => out.records

def Tagged (origin : Fin nq × Fin nb) : Shared.Engine.Task n nb nq → Prop
  | .active job => job.searchId = origin.1 ∧ job.blockId = origin.2
  | .finished out => SparseLabels.support out.records = out.vertices

def Registered (c : Shared.Catalog n nb ns nq) (keys : Finset (RecordGuard.Key n nq))
    (origin : Fin nq × Fin nb) (task : Shared.Engine.Task n nb nq) : Prop :=
  Tagged origin task ∧ ((taskRecords task).map Prod.fst).Nodup ∧
    SparseLabels.support (taskRecords task) ⊆ RecordGuard.verticesAt keys origin.1 ∩ c.blocks.get origin.2

theorem registered_mono (c : Shared.Catalog n nb ns nq)
    {before after : Finset (RecordGuard.Key n nq)} (hm : before ⊆ after)
    (origin : Fin nq × Fin nb) (task : Shared.Engine.Task n nb nq)
    (h : Registered c before origin task) : Registered c after origin task := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro v hv
  obtain ⟨hs, hb⟩ := Finset.mem_inter.mp (h.2.2 hv)
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm (Finset.mem_filter.mp hs).2⟩, hb⟩

theorem evaluate_registered (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (origin : Fin nq × Fin nb) (job : Shared.Job n nb nq) (f : DistanceArray n)
    (old next : RecordGuard.Registry n nq) (task : Shared.Engine.Task n nb nq)
    (hreg : Registered c old.seen origin (.active job))
    (h : evaluate c budget r job f old = .ok (next, task)) : Registered c next.seen origin task := by
  let U := found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)
  unfold evaluate at h
  cases he : reserveFound c budget job.searchId U old with
  | error reason =>
      dsimp only [U] at he
      simp only [he] at h
      cases h
  | ok middle =>
      have he' : reserveFound c budget job.searchId
          (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)) old =
          .ok middle := he
      simp only [he'] at h
      have hm := RecordGuard.reserveMany_mono c budget _ old middle he
      have hc : ∀ v ∈ U, (job.searchId, v) ∈ middle.seen := by
        intro v hv
        exact RecordGuard.reserveMany_contains c budget _ old middle he (job.searchId, v)
          (List.mem_map.mpr ⟨v, (Finset.mem_sort _).mpr hv, rfl⟩)
      by_cases hs : U.card < job.threshold
      · have hs' : (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources)
            f.get (c.scale * r)).card < job.threshold := hs
        rw [ite_eq_left hs'] at h
        cases h
        refine ⟨SparseLabels.support_ofSet U f.get, SparseLabels.nodup_ofSet U f.get, ?_⟩
        change SparseLabels.support (SparseLabels.ofSet U f.get) ⊆ _
        rw [SparseLabels.support_ofSet]
        intro v hv
        have hB := (Finset.mem_filter.mp hv).1
        have hseen := hc v hv
        obtain ⟨hj, hi⟩ := hreg.1
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hseen⟩,
            hi ▸ Finset.inter_subset_left hB⟩
      · have hs' : ¬ (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources)
            f.get (c.scale * r)).card < job.threshold := hs
        rw [ite_eq_right hs'] at h
        cases h
        simpa only [Registered, Tagged, taskRecords, Shared.double] using
          registered_mono c hm origin (.active job) hreg

theorem rows_record_bound (c : Shared.Catalog n nb ns nq)
    (keys : Finset (RecordGuard.Key n nq)) (origin : Fin N → Fin nq × Fin nb)
    (hi : Function.Injective origin) (rows : Fin N → SparseLabels.Labels (Fin n))
    (hu : ∀ i, ((rows i).map Prod.fst).Nodup)
    (hs : ∀ i, SparseLabels.support (rows i) ⊆
      RecordGuard.verticesAt keys (origin i).1 ∩ c.blocks.get (origin i).2) :
    (∑ i : Fin N, (rows i).length) ≤ RecordGuard.weight c keys := by
  have hsum : (∑ i : Fin N, (rows i).length) ≤
      ∑ k : Fin nq × Fin nb, (RecordGuard.verticesAt keys k.1 ∩ c.blocks.get k.2).card := by
    apply Finset.sum_le_sum_of_injOn origin
    · intro i _ j _ he
      exact hi he
    · exact Finset.subset_univ _
    · intro i _
      rw [SparseLabels.length_eq_card _ (hu i)]
      exact Finset.card_le_card (hs i)
    · intro _ _ _
      exact Nat.zero_le _
  rw [Fintype.sum_prod_type] at hsum
  apply hsum.trans
  rw [RecordGuard.weight_sections]
  exact Finset.sum_le_sum (fun j _ => Nat.le_add_left _ _)

def tasksCells (tasks : Vector (Shared.Engine.Task n nb nq) N) : ℕ :=
  8 * N + 6 * ∑ i : Fin N, (taskRecords (tasks.get i)).length

theorem tasksCells_bound (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (hv : RecordGuard.Valid c budget registry)
    (origin : Fin N → Fin nq × Fin nb) (hi : Function.Injective origin)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (hn : N ≤ budget)
    (hr : ∀ i, Registered c registry.seen (origin i) (tasks.get i)) :
    tasksCells tasks ≤ 14 * budget := by
  have hrec := rows_record_bound c registry.seen origin hi (fun i => taskRecords (tasks.get i))
    (fun i => (hr i).2.1) (fun i => (hr i).2.2)
  have hweight : RecordGuard.weight c registry.seen ≤ budget := hv.1 ▸ hv.2
  unfold tasksCells
  nlinarith only [hrec, hweight, hn]

end StreamingReachability.Core.GuardedEngine
