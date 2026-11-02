module

public import StreamingSSSP.Core.RegisteredUpdates
public import StreamingSSSP.Core.GuardedCandidates

@[expose] public section

namespace StreamingSSSP.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

def RepliesCovered (registry : RecordGuard.Registry n nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) : Prop :=
  ∀ pair ∈ replies, ∀ out, pair.2 = some out → ∀ v ∈ out.vertices, (pair.1.1, v) ∈ registry.seen

theorem answers_cover (c : Shared.Catalog n nb ns nq) (registry : RecordGuard.Registry n nq)
    (jobs : List (Shared.Job n nb nq)) (tasks : Vector (Shared.Engine.Task n nb nq) jobs.length)
    (hr : ∀ i, GuardedEngine.Registered c registry.seen (BatchDriver.key (jobs.get i)) (tasks.get i)) :
    RepliesCovered registry (BatchDriver.answers jobs tasks) := by
  intro pair hp out hout v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
  have hi := hr i
  cases he : tasks.get i with
  | active job => simp [he] at hout
  | finished actual =>
      have ho : actual = out := by simpa only [he, Option.some.injEq] using hout
      subst out
      rw [he] at hi
      apply (Finset.mem_filter.mp (Finset.mem_inter.mp (hi.2.2 ?_)).1).2
      change v ∈ SparseLabels.support actual.records
      rw [hi.1]
      exact hv

theorem replies_get_cover (registry : RecordGuard.Registry n nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (hc : RepliesCovered registry replies) (j : Fin nq) (i : Fin nb) :
    ∀ out, RecordMap.get none replies (j, i) = some out → ∀ v ∈ out.vertices, (j, v) ∈ registry.seen := by
  apply GuardedEngine.property_get_key
    (fun reply : Option (BlockSearch.Outcome n) =>
      ∀ out, reply = some out → ∀ v ∈ out.vertices, (j, v) ∈ registry.seen) none
    (by intro out h; cases h) replies (j, i)
  intro pair hp hk out ho v hv
  have he : pair.1.1 = j := congrArg Prod.fst hk
  rw [← he]
  exact hc pair hp out ho v hv

theorem proposed_cover (c : Shared.Catalog n nb ns nq) (r : ℕ)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (registry : RecordGuard.Registry n nq)
    (hs : ∀ j, (j, (c.searches.get j).source) ∈ registry.seen)
    (hC : CandidatesCovered registry C) (hR : RepliesCovered registry replies) :
    ∀ j, ∀ v ∈ proposed c r j (old.get j) (C.get j) replies, (j, v) ∈ registry.seen := by
  intro j v hv
  unfold proposed at hv
  by_cases ha : r ≤ (c.searches.get j).radius
  · rw [ite_eq_left ha] at hv
    have hu := (Finset.mem_sdiff.mp hv).1
    rcases Finset.mem_union.mp hu with hu | hfound
    · rcases Finset.mem_union.mp hu with hsource | hcandidate
      · by_cases hz : r = 0
        · rw [ite_eq_left hz] at hsource
          have hv : v = (c.searches.get j).source := Finset.mem_singleton.mp hsource
          subst v
          exact hs j
        · simp [hz] at hsource
      · exact hC j v hcandidate
    · obtain ⟨pair, hp, hv⟩ := (SparseDriver.resultUnion_mem _ v).mp hfound
      obtain ⟨item, _, rfl⟩ := List.mem_map.mp hp
      dsimp only at hv
      by_cases hn : item.2.next = (r : Distance)
      · simp only [hn, ↓reduceIte] at hv
        cases he : RecordMap.get none replies (j, item.1) with
        | none => simp [he] at hv
        | some out =>
            simp only [he] at hv
            exact replies_get_cover registry replies hR j item.1 out he v hv
      · simp [hn] at hv
  · simp [ha] at hv

theorem reserveMany_existing (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (keys : List (RecordGuard.Key n nq)) (registry : RecordGuard.Registry n nq)
    (h : ∀ key ∈ keys, key ∈ registry.seen) :
    RecordGuard.reserveMany c budget keys registry = .ok registry := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      rw [RecordGuard.reserveMany, RecordGuard.reserve, ite_eq_left (h key (by simp))]
      exact ih (fun q hq => h q (by simp [hq]))

theorem finishQueries_existing (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (indices : List (Fin nq)) (registry : RecordGuard.Registry n nq) (acc : BatchDriver.States n nb nq)
    (hc : ∀ j, ∀ v ∈ proposed c r j (old.get j) (C.get j) replies, (j, v) ∈ registry.seen) :
    ∃ result, finishQueries c budget r old C replies indices registry acc = .ok (registry, result) := by
  induction indices generalizing acc with
  | nil => exact ⟨acc, rfl⟩
  | cons j js ih =>
      rw [finishQueries]
      have hres : GuardedEngine.reserveFound c budget j (proposed c r j (old.get j) (C.get j) replies)
          registry = .ok registry := by
        apply reserveMany_existing
        intro key hk
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hk
        exact hc j v ((Finset.mem_sort _).mp hv)
      rw [hres]
      exact ih _

end StreamingSSSP.Core.GuardedDriver
