module

public import StreamingSSSP.Core.RegisteredTaskExecution

@[expose] public section

namespace StreamingSSSP.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem process_task_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Fin N → Shared.Engine.Task n nb nq → Prop)
    (mono : ∀ old next, old.seen ⊆ next.seen → ∀ i task, P old i task → P next i task)
    (step : ∀ i job f old next task, P old i (.active job) →
      evaluate c budget r job f old = .ok (next, task) → P next i task)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (hp : ∀ slot ∈ slots, P old slot.1 (.active slot.2))
    (h : process hn c budget r slots works old = .ok (last, updates)) :
    ∀ pair ∈ updates, P last pair.1 pair.2 := by
  induction slots generalizing works old last updates with
  | nil => cases h; simp
  | cons slot slots ih =>
      cases works with
      | nil => cases h; simp
      | cons work works =>
          rw [process] at h
          cases he : evaluate c budget r slot.2
              (StoredSearch.run (Shared.storedEdges hn work) (SparseLabels.vector slot.2.sources)) old with
          | error reason => simp [he] at h
          | ok pair =>
              obtain ⟨middle, task⟩ := pair
              simp only [he] at h
              have hmono := evaluate_mono c budget r _ _ old middle task he
              have hhead := step slot.1 slot.2 _ old middle task (hp slot (by simp)) he
              cases ht : process hn c budget r slots works middle with
              | error reason => simp [ht] at h
              | ok pair =>
                  obtain ⟨endRegistry, tail⟩ := pair
                  simp only [ht] at h
                  have htail := ih works middle endRegistry tail
                    (fun q hq => mono old middle hmono _ _ (hp q (by simp [hq]))) ht
                  have hm := process_mono hn c budget r slots works middle endRegistry tail ht
                  have hreg := congrArg Prod.fst (Except.ok.inj h)
                  have hup := congrArg Prod.snd (Except.ok.inj h)
                  dsimp only at hreg hup
                  rw [← hreg, ← hup]
                  intro pair hm'
                  rcases List.mem_cons.mp hm' with rfl | hm'
                  · exact mono middle endRegistry hm _ _ hhead
                  · exact htail pair hm'

theorem pack_task_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Fin N → Shared.Engine.Task n nb nq → Prop)
    (mono : ∀ old next, old.seen ⊆ next.seen → ∀ i task, P old i task → P next i task)
    (step : ∀ i job f old next task, P old i (.active job) →
      evaluate c budget r job f old = .ok (next, task) → P next i task)
    (slots : List (Fin N × Shared.Job n nb nq)) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N)
    (hp : ∀ slot ∈ slots, P old slot.1 (.active slot.2))
    (h : pack hn c stored input budget r slots old = .ok (last, result)) :
    ∀ pair ∈ result.updates, P last pair.1 pair.2 := by
  unfold pack at h
  cases he : process hn c budget r slots (Shared.scanPack c (slots.map Prod.snd) stored input).state old with
  | error reason => simp [he] at h
  | ok pair =>
      obtain ⟨next, updates⟩ := pair
      simp only [he] at h
      have hreg := congrArg Prod.fst (Except.ok.inj h)
      have hup := congrArg (fun p => p.2.updates) (Except.ok.inj h)
      dsimp only at hreg hup
      rw [← hreg, ← hup]
      exact process_task_post hn c budget r P mono step slots _ old next updates hp he

theorem packs_task_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Fin N → Shared.Engine.Task n nb nq → Prop)
    (mono : ∀ old next, old.seen ⊆ next.seen → ∀ i task, P old i task → P next i task)
    (step : ∀ i job f old next task, P old i (.active job) →
      evaluate c budget r job f old = .ok (next, task) → P next i task)
    (packages : List (List (Fin N × Shared.Job n nb nq))) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N)
    (hp : ∀ slot ∈ packages.flatten, P old slot.1 (.active slot.2))
    (h : packs hn c stored input budget r packages old = .ok (last, result)) :
    ∀ pair ∈ result.updates, P last pair.1 pair.2 := by
  induction packages generalizing old last result with
  | nil => cases h; simp
  | cons slots rest ih =>
      rw [packs] at h
      cases he : pack hn c stored input budget r slots old with
      | error reason => simp [he] at h
      | ok pair =>
          obtain ⟨middle, first⟩ := pair
          simp only [he] at h
          have hm := pack_post hn c stored input budget r (fun reg => old.seen ⊆ reg.seen)
            (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
            slots old middle first (Finset.Subset.refl _) he
          have hfirst := pack_task_post hn c stored input budget r P mono step slots old middle first
            (fun slot hs => hp slot (by simp [hs])) he
          cases ht : packs hn c stored input budget r rest middle with
          | error reason => simp [ht] at h
          | ok pair =>
              obtain ⟨endRegistry, tail⟩ := pair
              simp only [ht] at h
              have htail := ih middle endRegistry tail
                (fun slot hs => mono old middle hm _ _ (hp slot (by simp [hs]))) ht
              have hm' := packs_post hn c stored input budget r (fun reg => middle.seen ⊆ reg.seen)
                (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
                rest middle endRegistry tail (Finset.Subset.refl _) ht
              have hreg := congrArg Prod.fst (Except.ok.inj h)
              have hup := congrArg (fun p => p.2.updates) (Except.ok.inj h)
              dsimp only at hreg hup
              rw [← hreg, ← hup]
              intro pair hs
              rcases List.mem_append.mp hs with hs | hs
              · exact mono middle endRegistry hm' _ _ (hfirst pair hs)
              · exact htail pair hs

theorem runAux_task_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r fuel : ℕ)
    (P : RecordGuard.Registry n nq → Fin N → Shared.Engine.Task n nb nq → Prop)
    (mono : ∀ old next, old.seen ⊆ next.seen → ∀ i task, P old i task → P next i task)
    (step : ∀ i job f old next task, P old i (.active job) →
      evaluate c budget r job f old = .ok (next, task) → P next i task)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (old last : RecordGuard.Registry n nq)
    (scans reservations peak : ℕ) (result : Shared.Engine.Run n nb nq N)
    (hp : ∀ i, P old i (tasks.get i))
    (h : runAux hn c stored input budget r fuel tasks old scans reservations peak = .ok (last, result)) :
    ∀ i, P last i (result.tasks.get i) := by
  induction fuel generalizing tasks old scans reservations peak with
  | zero => cases h; exact hp
  | succ fuel ih =>
      rw [runAux] at h
      cases he : phase hn c stored input budget r tasks old with
      | error reason => simp [he] at h
      | ok pair =>
          obtain ⟨middle, replies⟩ := pair
          simp only [he] at h
          have hm := packs_post hn c stored input budget r (fun reg => old.seen ⊆ reg.seen)
            (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
            _ old middle replies (Finset.Subset.refl _) he
          have hreply := packs_task_post hn c stored input budget r P mono step _ old middle replies
            (by
              intro slot hs
              rw [Packing.pack_flatten] at hs
              have ht := (Shared.Engine.active_mem tasks slot.1 slot.2).mp (List.mem_reverse.mp hs)
              simpa only [ht] using hp slot.1) he
          have hnext : ∀ i, P middle i ((Shared.Engine.commitTasks tasks replies.updates).get i) := by
            intro i
            rw [Shared.Engine.commitTasks, Vector.get_ofFn]
            apply property_get_key (P middle i) (tasks.get i) (mono old middle hm _ _ (hp i)) replies.updates i
            intro pair hpair hkey
            simpa only [hkey] using hreply pair hpair
          exact ih _ middle _ _ _ hnext h

end StreamingSSSP.Core.GuardedEngine
