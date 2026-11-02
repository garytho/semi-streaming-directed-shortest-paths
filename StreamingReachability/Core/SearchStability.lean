module

public import StreamingReachability.Core.SharedRun

@[expose] public section

namespace StreamingReachability.Core.BlockSearch

open StoredEdges

variable {n : ℕ}

theorem searchAux_stable (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (input : List (Edge n)) (fuel extra τ : ℕ)
    {out : Outcome n} (hout : searchAux hn B known r initial input fuel τ = some out) :
    searchAux hn B known r initial input (fuel + extra) τ = some out := by
  induction fuel generalizing τ out with
  | zero => simp [searchAux] at hout
  | succ fuel ih =>
      rw [searchAux] at hout
      rw [show fuel + 1 + extra = (fuel + extra) + 1 by omega, searchAux]
      by_cases hs : (found B known (labels hn B known τ initial input).get r).card < τ
      · rw [ite_eq_left hs] at hout ⊢
        exact hout
      · rw [ite_eq_right hs] at hout ⊢
        obtain ⟨out', ho, he⟩ := Option.map_eq_some_iff.mp hout
        rw [ih (2 * τ) (out := out') ho]
        exact congrArg some he

end StreamingReachability.Core.BlockSearch

namespace StreamingReachability.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem finished_result (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (r x : ℕ) (tasks : Vector (Task n nb nq) N) (i : Fin N) (job : Job n nb nq)
    (hi : tasks.get i = .active job)
    (hB : (block c job.searchId job.blockId).card ≤ x)
    (hτ : job.threshold = 1) (hsc : job.spentScans = 0) (hres : job.spentReservations = 0) :
    ∃ out, ViewedSkeleton.search hn (view c job.searchId) (block c job.searchId job.blockId)
        (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources)
        stored input = some out ∧
      ((run hn c stored input r (Nat.log 2 x + 2) tasks).tasks).get i = .finished out := by
  obtain ⟨out, hout⟩ := BlockSearch.search_terminates hn (block c job.searchId job.blockId)
    (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources)
    ((stored ++ input).filterMap (view c job.searchId))
  have hv : ViewedSkeleton.search hn (view c job.searchId) (block c job.searchId job.blockId)
      (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources)
      stored input = some out := by rwa [ViewedSkeleton.search_eq]
  have hle : Nat.log 2 (block c job.searchId job.blockId).card + 2 ≤ Nat.log 2 x + 2 :=
    Nat.add_le_add_right (Nat.log_mono_right hB) 2
  have hb := BlockSearch.searchAux_stable hn (block c job.searchId job.blockId)
    (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources)
    ((stored ++ input).filterMap (view c job.searchId)) _
    (Nat.log 2 x + 2 - (Nat.log 2 (block c job.searchId job.blockId).card + 2)) 1 hout
  rw [Nat.add_sub_of_le hle] at hb
  have hbig : ViewedSkeleton.searchAux hn (view c job.searchId) (block c job.searchId job.blockId)
      (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources)
      stored input (Nat.log 2 x + 2) job.threshold = some out := by
    rw [ViewedSkeleton.searchAux_eq, hτ]
    exact hb
  refine ⟨out, hv, ?_⟩
  rw [run_tasks_get, hi, iterate_searchAux hn c stored input r _ job hbig]
  have he : addSpent job out = out := by
    cases out
    simp [addSpent, hsc, hres]
  rw [he]

end StreamingReachability.Core.Shared.Engine
