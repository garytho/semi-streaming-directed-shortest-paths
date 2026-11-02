module

public import StreamingReachability.Core.RegisteredTaskExecution
public import StreamingReachability.Core.IndexedSums

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

def updatesCells (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq)) : ℕ :=
  8 * updates.length + 6 * (updates.map fun pair => (taskRecords pair.2).length).sum

theorem updatesCells_bound (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (hv : RecordGuard.Valid c budget registry)
    (origin : Fin N → Fin nq × Fin nb) (hi : Function.Injective origin)
    (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq)) (hu : RecordMap.Unique updates)
    (hn : N ≤ budget)
    (hr : ∀ pair ∈ updates, Registered c registry.seen (origin pair.1) pair.2) :
    updatesCells updates ≤ 14 * budget := by
  have hkey := RecordMap.index_key_injective updates hu
  have hlen : updates.length ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hkey
  have hrec := rows_record_bound c registry.seen (fun i : Fin updates.length => origin ((updates.get i).1))
    (hi.comp hkey) (fun i => taskRecords ((updates.get i).2))
    (fun i => (hr _ (List.get_mem updates i)).2.1)
    (fun i => (hr _ (List.get_mem updates i)).2.2)
  have hb : RecordGuard.weight c registry.seen ≤ budget := hv.1 ▸ hv.2
  unfold updatesCells
  rw [list_sum_get]
  nlinarith only [hlen, hrec, hb, hn]

theorem process_keys (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (h : process hn c budget r slots works old = .ok (last, updates)) :
    updates.map Prod.fst = (slots.take works.length).map Prod.fst := by
  rw [process_erases hn c budget r slots works old last updates h]
  have hz (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq)) :
      (slots.zipWith (Shared.Engine.completeWork hn c r) works).map Prod.fst =
        (slots.take works.length).map Prod.fst := by
    induction slots generalizing works with
    | nil => simp
    | cons slot slots ih =>
        cases works with
        | nil => rfl
        | cons work works =>
            simpa only [List.zipWith_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons,
              Shared.Engine.completeWork] using congrArg (slot.1 :: ·) (ih works)
  exact hz slots works

theorem process_unique (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (hu : RecordMap.Unique slots)
    (h : process hn c budget r slots works old = .ok (last, updates)) : RecordMap.Unique updates := by
  unfold RecordMap.Unique
  rw [process_keys hn c budget r slots works old last updates h, List.map_take]
  exact hu.take

theorem packs_unique (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ)
    (packages : List (List (Fin N × Shared.Job n nb nq))) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N) (hu : RecordMap.Unique packages.flatten)
    (h : packs hn c stored input budget r packages old = .ok (last, result)) :
    RecordMap.Unique result.updates := by
  rw [packs_erases hn c stored input budget r packages old last result h, Shared.Engine.executePacks_eq]
  simpa only [RecordMap.Unique, List.map_map, Function.comp_def, Shared.Engine.slotStep] using hu

theorem phase_unique (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Phase n nb nq N)
    (h : phase hn c stored input budget r tasks old = .ok (last, result)) :
    RecordMap.Unique result.updates := by
  apply packs_unique hn c stored input budget r _ old last result _ h
  rw [Packing.pack_flatten]
  simpa [RecordMap.Unique, List.map_reverse] using Shared.Engine.active_unique tasks

theorem phase_buffers (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ)
    (origin : Fin N → Fin nq × Fin nb) (hi : Function.Injective origin)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (hq : N ≤ budget)
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Phase n nb nq N)
    (hv : RecordGuard.Valid c budget old)
    (hr : ∀ i, Registered c old.seen (origin i) (tasks.get i))
    (h : phase hn c stored input budget r tasks old = .ok (last, result)) :
    tasksCells tasks + updatesCells result.updates + (2 + 3 * last.seen.card) ≤ 2 + 31 * budget := by
  have hl := packs_valid hn c stored input budget r _ old last result hv h
  have hm := packs_post hn c stored input budget r (fun reg => old.seen ⊆ reg.seen)
    (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
    _ old last result (Finset.Subset.refl _) h
  have ht := tasksCells_bound c budget last hl origin hi tasks hq
    (fun i => registered_mono c hm _ _ (hr i))
  have hu := updatesCells_bound c budget last hl origin hi result.updates
    (phase_unique hn c stored input budget r tasks old last result h) hq
    (phase_registered hn c stored input budget r origin tasks old last result hr h)
  have hg := RecordGuard.registry_cells c budget last hl
  omega

end StreamingReachability.Core.GuardedEngine
