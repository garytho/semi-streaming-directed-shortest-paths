module

public import StreamingReachability.Core.GuardedEngineProofs
public import StreamingReachability.Core.RecordGuardSeen

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem evaluate_mono (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (job : Shared.Job n nb nq) (f : DistanceArray n) (old next : RecordGuard.Registry n nq)
    (task : Shared.Engine.Task n nb nq)
    (h : evaluate c budget r job f old = .ok (next, task)) : old.seen ⊆ next.seen := by
  unfold evaluate at h
  cases hg : reserveFound c budget job.searchId
      (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)) old with
  | error reason => simp [hg] at h
  | ok middle =>
      simp only [hg] at h
      have hm := RecordGuard.reserveMany_mono c budget _ old middle hg
      split_ifs at h <;> cases h <;> exact hm

theorem process_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (he : ∀ job f old next task, P old →
      evaluate c budget r job f old = .ok (next, task) → P next)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (hp : P old) (h : process hn c budget r slots works old = .ok (last, updates)) : P last := by
  induction slots generalizing works old last updates with
  | nil => cases h; exact hp
  | cons slot slots ih =>
      cases works with
      | nil => cases h; exact hp
      | cons work works =>
          rw [process] at h
          cases hs : evaluate c budget r slot.2
              (StoredSearch.run (Shared.storedEdges hn work) (SparseLabels.vector slot.2.sources)) old with
          | error reason => simp [hs] at h
          | ok pair =>
              obtain ⟨middle, task⟩ := pair
              simp only [hs] at h
              have hm := he _ _ old middle task hp hs
              cases ht : process hn c budget r slots works middle with
              | error reason => simp [ht] at h
              | ok pair =>
                  obtain ⟨endRegistry, tail⟩ := pair
                  simp only [ht] at h
                  have hreg := congrArg Prod.fst (Except.ok.inj h)
                  dsimp only at hreg
                  rw [← hreg]
                  exact ih works middle endRegistry tail hm ht

theorem pack_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (P : RecordGuard.Registry n nq → Prop)
    (he : ∀ job f old next task, P old →
      evaluate c budget r job f old = .ok (next, task) → P next)
    (slots : List (Fin N × Shared.Job n nb nq)) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N) (hp : P old)
    (h : pack hn c stored input budget r slots old = .ok (last, result)) : P last := by
  unfold pack at h
  cases hs : process hn c budget r slots (Shared.scanPack c (slots.map Prod.snd) stored input).state old with
  | error reason => simp [hs] at h
  | ok pair =>
      obtain ⟨next, updates⟩ := pair
      simp only [hs] at h
      have hreg := congrArg Prod.fst (Except.ok.inj h)
      dsimp only at hreg
      rw [← hreg]
      exact process_post hn c budget r P he slots _ old next updates hp hs

theorem packs_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (P : RecordGuard.Registry n nq → Prop)
    (he : ∀ job f old next task, P old →
      evaluate c budget r job f old = .ok (next, task) → P next)
    (packages : List (List (Fin N × Shared.Job n nb nq))) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N) (hp : P old)
    (h : packs hn c stored input budget r packages old = .ok (last, result)) : P last := by
  induction packages generalizing old last result with
  | nil => cases h; exact hp
  | cons slots rest ih =>
      rw [packs] at h
      cases hs : pack hn c stored input budget r slots old with
      | error reason => simp [hs] at h
      | ok pair =>
          obtain ⟨middle, first⟩ := pair
          simp only [hs] at h
          have hm := pack_post hn c stored input budget r P he slots old middle first hp hs
          cases ht : packs hn c stored input budget r rest middle with
          | error reason => simp [ht] at h
          | ok pair =>
              obtain ⟨endRegistry, tail⟩ := pair
              simp only [ht] at h
              have hreg := congrArg Prod.fst (Except.ok.inj h)
              dsimp only at hreg
              rw [← hreg]
              exact ih middle endRegistry tail hm ht

theorem runAux_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (P : RecordGuard.Registry n nq → Prop)
    (he : ∀ job f old next task, P old →
      evaluate c budget r job f old = .ok (next, task) → P next)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (old last : RecordGuard.Registry n nq)
    (scans reservations peak : ℕ) (result : Shared.Engine.Run n nb nq N) (hp : P old)
    (h : runAux hn c stored input budget r fuel tasks old scans reservations peak = .ok (last, result)) : P last := by
  induction fuel generalizing tasks old scans reservations peak with
  | zero => cases h; exact hp
  | succ fuel ih =>
      rw [runAux] at h
      cases hs : phase hn c stored input budget r tasks old with
      | error reason => simp [hs] at h
      | ok pair =>
          obtain ⟨middle, replies⟩ := pair
          simp only [hs] at h
          have hm := packs_post hn c stored input budget r P he _ old middle replies hp hs
          exact ih _ middle _ _ _ hm h

theorem run_valid (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Run n nb nq N)
    (hv : RecordGuard.Valid c budget old)
    (h : run hn c stored input budget r fuel tasks old = .ok (last, result)) :
    RecordGuard.Valid c budget last :=
  runAux_post hn c stored input budget r fuel (RecordGuard.Valid c budget)
    (fun job f old next task hv he => evaluate_valid c budget r job f old next task hv he)
    tasks old last 0 0 0 result hv h

theorem run_mono (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Run n nb nq N)
    (h : run hn c stored input budget r fuel tasks old = .ok (last, result)) : old.seen ⊆ last.seen :=
  runAux_post hn c stored input budget r fuel (fun registry => old.seen ⊆ registry.seen)
    (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
    tasks old last 0 0 0 result (Finset.Subset.refl _) h

end StreamingReachability.Core.GuardedEngine
