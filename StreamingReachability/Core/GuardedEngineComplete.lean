module

public import StreamingReachability.Core.GuardedEngineBounded

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

def FoundRule (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (r : ℕ) (P : Shared.Job n nb nq → Prop) (allowed : Finset (RecordGuard.Key n nq)) : Prop :=
  ∀ job, P job → ∀ v ∈ found (Shared.block c job.searchId job.blockId)
    (SparseLabels.support job.sources)
    (ViewedSkeleton.labels hn (Shared.view c job.searchId) (Shared.block c job.searchId job.blockId)
      (SparseLabels.support job.sources) job.threshold (SparseLabels.vector job.sources) stored input).get
    (c.scale * r), (job.searchId, v) ∈ allowed

theorem packs_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (P : Shared.Job n nb nq → Prop)
    (allowed : Finset (RecordGuard.Key n nq)) (packages : List (List (Fin N × Shared.Job n nb nq)))
    (hpack : ∀ slots ∈ packages, ∀ old : RecordGuard.Registry n nq,
      old.seen ⊆ allowed → RecordGuard.Valid c budget old →
      ∃ next result, pack hn c stored input budget r slots old = .ok (next, result) ∧
        next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next ∧
          ∀ pair ∈ result.updates, TaskProperty P pair.2)
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old) :
    ∃ next result, packs hn c stored input budget r packages old = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next ∧
        ∀ pair ∈ result.updates, TaskProperty P pair.2 := by
  induction packages generalizing old with
  | nil => exact ⟨old, ⟨[], 0, 0, 0⟩, rfl, hs, hv, by simp⟩
  | cons slots rest ih =>
      obtain ⟨middle, first, hf, hs', hv', hp⟩ := hpack slots (by simp) old hs hv
      obtain ⟨last, tail, ht, hs'', hv'', hpt⟩ :=
        ih (fun q hq => hpack q (by simp [hq])) middle hs' hv'
      refine ⟨last, ⟨first.updates ++ tail.updates, tail.scans + 1,
        first.reads + tail.reads, max first.peakRows tail.peakRows⟩,
        by simp only [packs, hf, ht], hs'', hv'', ?_⟩
      intro pair hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hp pair hm
      · exact hpt pair hm

theorem phase_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (P : Shared.Job n nb nq → Prop)
    (hdouble : ∀ job, P job → P (Shared.double c job))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (hf : FoundRule hn c stored input r P allowed)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (hp : ∀ i, TaskProperty P (tasks.get i))
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old) :
    ∃ next result, phase hn c stored input budget r tasks old = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next ∧
        ∀ pair ∈ result.updates, TaskProperty P pair.2 := by
  apply packs_bounded hn c stored input budget r P allowed _
  · intro slots hslots reg hsr hvr
    apply pack_bounded hn c stored input budget r P hdouble allowed hb hf slots _ reg hsr hvr
    intro slot hm
    have hmem : slot ∈
        (Packing.pack n (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks)).flatten :=
      List.mem_flatten.mpr ⟨slots, hslots, hm⟩
    rw [Packing.pack_flatten] at hmem
    have hactive := List.mem_reverse.mp hmem
    have htask := (Shared.Engine.active_mem tasks slot.1 slot.2).mp hactive
    simpa only [htask, TaskProperty] using hp slot.1
  · exact hs
  · exact hv

theorem runAux_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (P : Shared.Job n nb nq → Prop)
    (hdouble : ∀ job, P job → P (Shared.double c job))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (hf : FoundRule hn c stored input r P allowed)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (hp : ∀ i, TaskProperty P (tasks.get i))
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old)
    (scans reservations peak : ℕ) :
    ∃ next result, runAux hn c stored input budget r fuel tasks old scans reservations peak = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next := by
  induction fuel generalizing tasks old scans reservations peak with
  | zero => exact ⟨old, ⟨tasks, scans, reservations, peak⟩, rfl, hs, hv⟩
  | succ fuel ih =>
      obtain ⟨middle, replies, he, hs', hv', hprops⟩ :=
        phase_bounded hn c stored input budget r P hdouble allowed hb hf tasks hp old hs hv
      have hnext : ∀ i, TaskProperty P ((Shared.Engine.commitTasks tasks replies.updates).get i) := by
        intro i
        rw [Shared.Engine.commitTasks, Vector.get_ofFn]
        exact property_get (TaskProperty P) (tasks.get i) (hp i) replies.updates hprops i
      obtain ⟨last, result, ht, hs'', hv''⟩ := ih _ hnext middle hs' hv' _ _ _
      exact ⟨last, result, by rw [runAux, he]; exact ht, hs'', hv''⟩

theorem run_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (P : Shared.Job n nb nq → Prop)
    (hdouble : ∀ job, P job → P (Shared.double c job))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (hf : FoundRule hn c stored input r P allowed)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (hp : ∀ i, TaskProperty P (tasks.get i))
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old) :
    ∃ next result, run hn c stored input budget r fuel tasks old = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next :=
  runAux_bounded hn c stored input budget r fuel P hdouble allowed hb hf tasks hp old hs hv 0 0 0

end StreamingReachability.Core.GuardedEngine
