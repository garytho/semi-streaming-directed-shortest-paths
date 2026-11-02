module

public import StreamingReachability.Core.BatchStatistics
public import StreamingReachability.Core.RecordGuard
public import StreamingReachability.Core.GlobalFound

@[expose] public section

namespace StreamingReachability.Core.RecordGuard

open StoredEdges

variable {n nb ns nq : ℕ}

noncomputable def allowed (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) :
    Finset (Key n nq) :=
  Finset.univ.filter fun k => k.2 ∈ BatchDriver.reached c stored input k.1

theorem allowed_weight (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) :
    weight c (allowed c stored input) = BatchDriver.Nrec c stored input := by
  rw [weight, allowed, Finset.sum_filter, Fintype.sum_prod_type]
  unfold BatchDriver.Nrec
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp_rw [charge_eq]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.card_filter]
    congr 1

def Context (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : BatchDriver.States n nb nq)
    (job : Shared.Job n nb nq) : Prop :=
  job.sources = (BatchDriver.canonical old job.searchId job.blockId).sources ∧
    r ≤ (c.searches.get job.searchId).radius

theorem context_double (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : BatchDriver.States n nb nq)
    (job : Shared.Job n nb nq) (h : Context c r old job) : Context c r old (Shared.double c job) := h

theorem jobs_context (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : BatchDriver.States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) {job : Shared.Job n nb nq}
    (hj : job ∈ BatchDriver.jobs c r old) : Context c r old job := by
  have he := BatchDriver.job_canonical c r old hu hj
  have hs : job.sources = (BatchDriver.canonical old job.searchId job.blockId).sources :=
    congrArg Shared.Job.sources he
  exact ⟨hs, (BatchDriver.job_origin c r old hj).choose_spec.2.2.2.2.2.2⟩

theorem found_allowed (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (job : Shared.Job n nb nq)
    (hctx : Context c r (BatchDriver.execute hn c stored input x r).states job) :
    ∀ v ∈ found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources)
        (ViewedSkeleton.labels hn (Shared.view c job.searchId) (Shared.block c job.searchId job.blockId)
          (SparseLabels.support job.sources) job.threshold (SparseLabels.vector job.sources) stored input).get
        (c.scale * r),
      (job.searchId, v) ∈ allowed c stored input := by
  let old := (BatchDriver.execute hn c stored input x r).states
  have ha := hctx.2
  have hinv := BatchDriver.execute_global_invariant hn c stored input x r hs hp hA hx job.searchId
  rw [Nat.min_eq_left (by omega)] at hinv
  have hsrc : job.sources =
      ((SparseDriver.observe (old.get job.searchId)).blocks.get job.blockId).known := by
    simpa only [BatchDriver.canonical, SparseDriver.observe, Vector.get_ofFn] using hctx.1
  have hf := Global.every_skeleton_found hn (Shared.referenceProblem c job.searchId)
    ((stored ++ input).filterMap (Shared.view c job.searchId)) hA hinv.1 hinv.2 job.blockId job.threshold
  intro v hv
  have hval : Global.target (Shared.referenceProblem c job.searchId)
      ((stored ++ input).filterMap (Shared.view c job.searchId)) v = (r : Distance) := by
    apply hf v
    simpa only [hsrc, ViewedSkeleton.labels_eq, Shared.referenceProblem, Vector.get_ofFn] using hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hval]
  exact WithTop.coe_le_coe.mpr hctx.2

end StreamingReachability.Core.RecordGuard
