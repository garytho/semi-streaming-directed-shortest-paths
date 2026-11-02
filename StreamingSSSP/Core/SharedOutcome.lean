module

public import StreamingSSSP.Core.SharedResources

@[expose] public section

namespace StreamingSSSP.Core.Shared.Engine

open StoredEdges

variable {n nb ns nq N : ℕ}

noncomputable def referenceOutcome (hn : 0 < n) (c : Catalog n nb ns nq)
    (stored input : List (Edge n)) (r : ℕ) (job : Job n nb nq) : BlockSearch.Outcome n :=
  (ViewedSkeleton.search hn (view c job.searchId) (block c job.searchId job.blockId)
    (SparseLabels.support job.sources) (c.scale * r) (SparseLabels.vector job.sources) stored input).getD
      Global.emptyOutcome

def starting (f : Fin N → Job n nb nq) : Vector (Task n nb nq) N :=
  Vector.ofFn fun i => .active (f i)

theorem run_outcome (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (x r : ℕ) (f : Fin N → Job n nb nq)
    (hb : ∀ i, (block c (f i).searchId (f i).blockId).card ≤ x)
    (hτ : ∀ i, (f i).threshold = 1) (hsc : ∀ i, (f i).spentScans = 0)
    (hr : ∀ i, (f i).spentReservations = 0) (i : Fin N) :
    ((run hn c stored input r (Nat.log 2 x + 2) (starting f)).tasks).get i =
      .finished (referenceOutcome hn c stored input r (f i)) := by
  obtain ⟨out, hout, htask⟩ := finished_result hn c stored input r x
    (starting f) i (f i) (by simp [starting]) (hb i) (hτ i) (hsc i) (hr i)
  simpa only [referenceOutcome, hout, Option.getD_some] using htask

theorem run_reservations (hn : 0 < n) (c : Catalog n nb ns nq) (stored input : List (Edge n))
    (x r : ℕ) (f : Fin N → Job n nb nq)
    (hb : ∀ i, (block c (f i).searchId (f i).blockId).card ≤ x)
    (hτ : ∀ i, (f i).threshold = 1) (hsc : ∀ i, (f i).spentScans = 0)
    (hr : ∀ i, (f i).spentReservations = 0) :
    (run hn c stored input r (Nat.log 2 x + 2) (starting f)).reservations =
      ∑ i : Fin N, (referenceOutcome hn c stored input r (f i)).reservations := by
  have h := run_work hn c stored input r (Nat.log 2 x + 2) (starting f)
  have hz : workSum (starting f) = 0 := by
    unfold workSum
    simp only [starting, Vector.get_ofFn, taskWork]
    exact Finset.sum_eq_zero (fun i _ => hr i)
  rw [hz, Nat.zero_add] at h
  rw [← h]
  unfold workSum
  apply Finset.sum_congr rfl
  intro i _
  rw [run_outcome hn c stored input x r f hb hτ hsc hr i]
  rfl

end StreamingSSSP.Core.Shared.Engine
