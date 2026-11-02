module

public import StreamingSSSP.Core.RegisteredTasks
public import StreamingSSSP.Core.GuardedPosts

@[expose] public section

namespace StreamingSSSP.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem property_get_key {K S : Type*} [DecidableEq K] (P : S → Prop) (zero : S) (hz : P zero)
    (xs : RecordMap.Map K S) (k : K) (hx : ∀ pair ∈ xs, pair.1 = k → P pair.2) :
    P (RecordMap.get zero xs k) := by
  induction xs with
  | nil => exact hz
  | cons pair ps ih =>
      rw [RecordMap.get_cons]
      split_ifs with he
      · exact hx pair (by simp) he
      · exact ih (fun q hq hkey => hx q (by simp [hq]) hkey)

theorem process_mono (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (h : process hn c budget r slots works old = .ok (last, updates)) : old.seen ⊆ last.seen :=
  process_post hn c budget r (fun reg => old.seen ⊆ reg.seen)
    (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
    slots works old last updates (Finset.Subset.refl _) h

theorem process_registered (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (origin : Fin N → Fin nq × Fin nb)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (hp : ∀ slot ∈ slots, Registered c old.seen (origin slot.1) (.active slot.2))
    (h : process hn c budget r slots works old = .ok (last, updates)) :
    ∀ pair ∈ updates, Registered c last.seen (origin pair.1) pair.2 := by
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
              have hhead := evaluate_registered c budget r (origin slot.1) slot.2 _ old middle task
                (hp slot (by simp)) he
              cases ht : process hn c budget r slots works middle with
              | error reason => simp [ht] at h
              | ok pair =>
                  obtain ⟨endRegistry, tail⟩ := pair
                  simp only [ht] at h
                  have htail := ih works middle endRegistry tail
                    (fun q hq => registered_mono c hmono _ _ (hp q (by simp [hq]))) ht
                  have hmono' := process_mono hn c budget r slots works middle endRegistry tail ht
                  have heq := Except.ok.inj h
                  have hreg := congrArg Prod.fst heq
                  have hupdates := congrArg Prod.snd heq
                  dsimp only at hreg hupdates
                  rw [← hreg, ← hupdates]
                  intro pair hm
                  rcases List.mem_cons.mp hm with rfl | hm
                  · exact registered_mono c hmono' _ _ hhead
                  · exact htail pair hm

theorem pack_registered (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ) (origin : Fin N → Fin nq × Fin nb)
    (slots : List (Fin N × Shared.Job n nb nq)) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N)
    (hp : ∀ slot ∈ slots, Registered c old.seen (origin slot.1) (.active slot.2))
    (h : pack hn c stored input budget r slots old = .ok (last, result)) :
    ∀ pair ∈ result.updates, Registered c last.seen (origin pair.1) pair.2 := by
  unfold pack at h
  cases he : process hn c budget r slots (Shared.scanPack c (slots.map Prod.snd) stored input).state old with
  | error reason => simp [he] at h
  | ok pair =>
      obtain ⟨next, updates⟩ := pair
      simp only [he] at h
      have hreg := congrArg Prod.fst (Except.ok.inj h)
      have hupdates := congrArg (fun p => p.2.updates) (Except.ok.inj h)
      dsimp only at hreg hupdates
      rw [← hreg, ← hupdates]
      exact process_registered hn c budget r origin slots _ old next updates hp he

theorem packs_registered (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ) (origin : Fin N → Fin nq × Fin nb)
    (packages : List (List (Fin N × Shared.Job n nb nq))) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N)
    (hp : ∀ slot ∈ packages.flatten, Registered c old.seen (origin slot.1) (.active slot.2))
    (h : packs hn c stored input budget r packages old = .ok (last, result)) :
    ∀ pair ∈ result.updates, Registered c last.seen (origin pair.1) pair.2 := by
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
          have hfirst := pack_registered hn c stored input budget r origin slots old middle first
            (fun slot hs => hp slot (by simp [hs])) he
          cases ht : packs hn c stored input budget r rest middle with
          | error reason => simp [ht] at h
          | ok pair =>
              obtain ⟨endRegistry, tail⟩ := pair
              simp only [ht] at h
              have htail := ih middle endRegistry tail
                (fun slot hs => registered_mono c hm _ _ (hp slot (by simp [hs]))) ht
              have hm' := packs_post hn c stored input budget r (fun reg => middle.seen ⊆ reg.seen)
                (fun job f before after task hp he => hp.trans (evaluate_mono c budget r job f before after task he))
                rest middle endRegistry tail (Finset.Subset.refl _) ht
              have hreg := congrArg Prod.fst (Except.ok.inj h)
              have hupdates := congrArg (fun p => p.2.updates) (Except.ok.inj h)
              dsimp only at hreg hupdates
              rw [← hreg, ← hupdates]
              intro pair hs
              rcases List.mem_append.mp hs with hs | hs
              · exact registered_mono c hm' _ _ (hfirst pair hs)
              · exact htail pair hs

theorem phase_registered (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ) (origin : Fin N → Fin nq × Fin nb)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (old last : RecordGuard.Registry n nq)
    (result : Shared.Engine.Phase n nb nq N)
    (hp : ∀ i, Registered c old.seen (origin i) (tasks.get i))
    (h : phase hn c stored input budget r tasks old = .ok (last, result)) :
    ∀ pair ∈ result.updates, Registered c last.seen (origin pair.1) pair.2 := by
  apply packs_registered hn c stored input budget r origin _ old last result _ h
  intro slot hs
  rw [Packing.pack_flatten] at hs
  have ha := List.mem_reverse.mp hs
  have he := (Shared.Engine.active_mem tasks slot.1 slot.2).mp ha
  simpa only [he] using hp slot.1

theorem runAux_registered (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r fuel : ℕ) (origin : Fin N → Fin nq × Fin nb)
    (tasks : Vector (Shared.Engine.Task n nb nq) N) (old last : RecordGuard.Registry n nq)
    (scans reservations peak : ℕ) (result : Shared.Engine.Run n nb nq N)
    (hp : ∀ i, Registered c old.seen (origin i) (tasks.get i))
    (h : runAux hn c stored input budget r fuel tasks old scans reservations peak = .ok (last, result)) :
    ∀ i, Registered c last.seen (origin i) (result.tasks.get i) := by
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
          have hreply := phase_registered hn c stored input budget r origin tasks old middle replies hp he
          have hnext : ∀ i, Registered c middle.seen (origin i)
              ((Shared.Engine.commitTasks tasks replies.updates).get i) := by
            intro i
            rw [Shared.Engine.commitTasks, Vector.get_ofFn]
            apply property_get_key (Registered c middle.seen (origin i)) (tasks.get i)
              (registered_mono c hm _ _ (hp i)) replies.updates i
            intro pair hpair hkey
            simpa only [hkey] using hreply pair hpair
          exact ih _ middle _ _ _ hnext h

end StreamingSSSP.Core.GuardedEngine
