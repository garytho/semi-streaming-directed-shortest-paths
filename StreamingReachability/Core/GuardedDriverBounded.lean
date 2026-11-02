module

public import StreamingReachability.Core.GuardedErasure
public import StreamingReachability.Core.GuardedEngineComplete
public import StreamingReachability.Core.RecordGuardSeen

@[expose] public section

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem ordinaryOne_bounded (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq)
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (ht : ∀ v, ordinaryTarget c r old raw j = some v → (j, v) ∈ allowed)
    (registry : RecordGuard.Registry n nq) (hs : registry.seen ⊆ allowed) (hv : RecordGuard.Valid c budget registry)
    (C : Vector (Finset (Fin n)) nq) :
    ∃ next result, ordinaryOne c budget r old raw j registry C = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next := by
  cases he : ordinaryTarget c r old raw j with
  | none => exact ⟨registry, C, by simp [ordinaryOne, he], hs, hv⟩
  | some v =>
      obtain ⟨next, hn, hs'⟩ := RecordGuard.reserve_bounded c budget allowed hb (j, v) (ht v he)
        registry hs hv.1
      exact ⟨next, VectorStore.set C j (insert v (C.get j)),
        by simp [ordinaryOne, he, hn], hs', RecordGuard.reserve_valid c budget _ registry next hv hn⟩

theorem ordinaryQueries_bounded (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (indices : List (Fin nq))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (ht : ∀ j v, ordinaryTarget c r old raw j = some v → (j, v) ∈ allowed)
    (registry : RecordGuard.Registry n nq) (hs : registry.seen ⊆ allowed) (hv : RecordGuard.Valid c budget registry)
    (C : Vector (Finset (Fin n)) nq) :
    ∃ next result, ordinaryQueries c budget r old raw indices registry C = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next := by
  induction indices generalizing registry C with
  | nil => exact ⟨registry, C, rfl, hs, hv⟩
  | cons j js ih =>
      obtain ⟨middle, nextC, he, hs', hv'⟩ := ordinaryOne_bounded c budget r old raw j
        allowed hb (ht j) registry hs hv C
      obtain ⟨last, result, he', hs'', hv''⟩ := ih middle hs' hv' nextC
      exact ⟨last, result, by simp only [ordinaryQueries, he, he'], hs'', hv''⟩

theorem ordinaryScan_bounded (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (input : List (Edge n))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (ht : ∀ raw ∈ input, ∀ j v, ordinaryTarget c r old raw j = some v → (j, v) ∈ allowed)
    (registry : RecordGuard.Registry n nq) (hs : registry.seen ⊆ allowed) (hv : RecordGuard.Valid c budget registry)
    (C : Vector (Finset (Fin n)) nq) :
    ∃ next result, ordinaryScan c budget r old input registry C = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next := by
  induction input generalizing registry C with
  | nil => exact ⟨registry, C, rfl, hs, hv⟩
  | cons raw rest ih =>
      obtain ⟨middle, nextC, he, hs', hv'⟩ := ordinaryQueries_bounded c budget r old raw (List.finRange nq)
        allowed hb (ht raw (by simp)) registry hs hv C
      obtain ⟨last, result, he', hs'', hv''⟩ :=
        ih (fun e he => ht e (by simp [he])) middle hs' hv' nextC
      exact ⟨last, result, by simp only [ordinaryScan, he, he'], hs'', hv''⟩

theorem ordinary_bounded (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (ht : ∀ raw ∈ stored ++ input, ∀ j v, ordinaryTarget c r old raw j = some v → (j, v) ∈ allowed)
    (registry : RecordGuard.Registry n nq) (hs : registry.seen ⊆ allowed) (hv : RecordGuard.Valid c budget registry) :
    ∃ next result, ordinary c budget r old stored input registry = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next := by
  obtain ⟨middle, C, he, hs', hv'⟩ := ordinaryScan_bounded c budget r old stored allowed hb
    (fun raw hr => ht raw (List.mem_append_left _ hr)) registry hs hv (Vector.replicate nq ∅)
  obtain ⟨last, result, he', hs'', hv''⟩ := ordinaryScan_bounded c budget r old input allowed hb
    (fun raw hr => ht raw (List.mem_append_right _ hr)) middle hs' hv' C
  exact ⟨last, result, by simp only [ordinary, he, he'], hs'', hv''⟩

theorem finishQueries_bounded (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (indices : List (Fin nq)) (allowed : Finset (RecordGuard.Key n nq))
    (hb : RecordGuard.weight c allowed ≤ budget)
    (ht : ∀ j v, v ∈ proposed c r j (old.get j) (C.get j) replies → (j, v) ∈ allowed)
    (registry : RecordGuard.Registry n nq) (hs : registry.seen ⊆ allowed) (hv : RecordGuard.Valid c budget registry)
    (acc : BatchDriver.States n nb nq) :
    ∃ next result, finishQueries c budget r old C replies indices registry acc = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next := by
  induction indices generalizing registry acc with
  | nil => exact ⟨registry, acc, rfl, hs, hv⟩
  | cons j js ih =>
      let U := proposed c r j (old.get j) (C.get j) replies
      obtain ⟨middle, he, hs', hv'⟩ := RecordGuard.reserveMany_bounded c budget allowed hb
        ((U.sort (· ≤ ·)).map fun v => (j, v)) (by
          intro key hk
          obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hk
          exact ht j v ((Finset.mem_sort _).mp hvm)) registry hs hv
      have he' : GuardedEngine.reserveFound c budget j U registry = .ok middle := he
      change GuardedEngine.reserveFound c budget j (proposed c r j (old.get j) (C.get j) replies)
        registry = .ok middle at he'
      obtain ⟨last, result, htail, hs'', hv''⟩ := ih middle hs' hv'
        (VectorStore.set acc j (BatchDriver.finishQuery c r j (old.get j) (C.get j) replies))
      exact ⟨last, result, by simp only [finishQueries, he', htail], hs'', hv''⟩

end StreamingReachability.Core.GuardedDriver
