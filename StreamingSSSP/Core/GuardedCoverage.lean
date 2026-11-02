module

public import StreamingSSSP.Core.GuardedDriverPosts
public import StreamingSSSP.Core.GuardedComplete
public import StreamingSSSP.Core.RegisteredSpace

@[expose] public section

namespace StreamingSSSP.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem reserve_mono (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (key : RecordGuard.Key n nq) (old next : RecordGuard.Registry n nq)
    (h : RecordGuard.reserve c budget key old = .ok next) : old.seen ⊆ next.seen := by
  rw [RecordGuard.reserve_seen c budget key old next h]
  exact Finset.subset_insert _ _

theorem finishQuery_support (c : Shared.Catalog n nb ns nq) (r : ℕ) (j : Fin nq)
    (old : SparseDriver.State n nb) (C : Finset (Fin n))
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n))) :
    SparseLabels.support (BatchDriver.finishQuery c r j old C replies).labels =
      SparseLabels.support old.labels ∪ proposed c r j old C replies := by
  by_cases ha : r ≤ (c.searches.get j).radius <;>
    simp only [BatchDriver.finishQuery, proposed, ha, ↓reduceIte,
      SparseLabels.support_addNew, Finset.union_empty]

theorem finishQueries_cover (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (indices : List (Fin nq)) (registry last : RecordGuard.Registry n nq)
    (acc result : BatchDriver.States n nb nq)
    (hold : Cover registry old) (hacc : Cover registry acc)
    (h : finishQueries c budget r old C replies indices registry acc = .ok (last, result)) :
    Cover last result := by
  induction indices generalizing registry acc with
  | nil => cases h; exact hacc
  | cons j js ih =>
      rw [finishQueries] at h
      cases hg : GuardedEngine.reserveFound c budget j (proposed c r j (old.get j) (C.get j) replies) registry with
      | error reason => simp [hg] at h
      | ok next =>
          simp only [hg] at h
          have hm := RecordGuard.reserveMany_mono c budget _ registry next hg
          have hreg : ∀ v ∈ proposed c r j (old.get j) (C.get j) replies, (j, v) ∈ next.seen := by
            intro v hv
            exact RecordGuard.reserveMany_contains c budget _ registry next hg (j, v)
              (List.mem_map.mpr ⟨v, (Finset.mem_sort _).mpr hv, rfl⟩)
          have hnew : Cover next
              (VectorStore.set acc j (BatchDriver.finishQuery c r j (old.get j) (C.get j) replies)) := by
            intro k v hv
            rw [VectorStore.get_set] at hv
            by_cases hk : k = j
            · subst k
              rw [ite_eq_left rfl, finishQuery_support] at hv
              rcases Finset.mem_union.mp hv with hv | hv
              · exact hm (hold j v hv)
              · exact hreg v hv
            · rw [ite_eq_right hk] at hv
              exact hm (hacc k v hv)
          exact ih next _ (cover_mono registry next old hold hm) hnew h

theorem round_cover (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ) (old : BatchDriver.States n nb nq)
    (registry last : RecordGuard.Registry n nq) (result : BatchDriver.Round n nb nq)
    (hc : Cover registry old) (h : round hn c stored input budget x r old registry = .ok (last, result)) :
    Cover last result.states := by
  unfold round at h
  cases hb : GuardedEngine.run hn c stored input budget r (Nat.log 2 x + 2)
      (BatchDriver.tasks (BatchDriver.jobs c r old)) registry with
  | error reason => simp [hb] at h
  | ok pair =>
      obtain ⟨afterBlocks, blocks⟩ := pair
      simp only [hb] at h
      have hB := GuardedEngine.run_mono hn c stored input budget r _ _ registry afterBlocks blocks hb
      cases ho : ordinary c budget r old stored input afterBlocks with
      | error reason => simp [ho] at h
      | ok pair =>
          obtain ⟨afterEdges, candidates⟩ := pair
          simp only [ho] at h
          have hE : afterBlocks.seen ⊆ afterEdges.seen :=
            ordinary_post c budget r (fun reg => afterBlocks.seen ⊆ reg.seen)
              (fun key before after hp he => hp.trans (reserve_mono c budget key before after he))
              old stored input afterBlocks afterEdges candidates (Finset.Subset.refl _) ho
          have hcover := cover_mono registry afterEdges old hc (hB.trans hE)
          cases hf : finishQueries c budget r old candidates
              (BatchDriver.answers (BatchDriver.jobs c r old) blocks.tasks) (List.finRange nq) afterEdges old with
          | error reason => simp [hf] at h
          | ok pair =>
              obtain ⟨endRegistry, states⟩ := pair
              simp only [hf] at h
              have he := Except.ok.inj h
              have hreg : endRegistry = last := congrArg Prod.fst he
              have hstates : states = result.states := congrArg (fun p => p.2.states) he
              rw [← hreg, ← hstates]
              exact finishQueries_cover c budget r old candidates _ _ afterEdges endRegistry old states
                hcover hcover hf

set_option maxHeartbeats 800000 in
theorem drive_cover (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (registry last : RecordGuard.Registry n nq)
    (state result : BatchDriver.Run n nb nq) (hc : Cover registry state.states)
    (h : drive hn c stored input budget x fuel r registry state = .ok (last, result)) :
    Cover last result.states := by
  induction fuel generalizing r registry state with
  | zero => cases h; exact hc
  | succ fuel ih =>
      rw [drive] at h
      cases hs : round hn c stored input budget x r state.states registry with
      | error reason => simp [hs] at h
      | ok pair =>
          obtain ⟨next, step⟩ := pair
          simp only [hs] at h
          exact ih (r + 1) next _ (round_cover hn c stored input budget x r state.states registry next step hc hs) h

theorem initSources_valid (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (h : initSources c budget = .ok registry) :
    RecordGuard.Valid c budget registry :=
  RecordGuard.reserveMany_valid c budget _ RecordGuard.empty registry (RecordGuard.empty_valid c budget) h

theorem initSources_cover (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (h : initSources c budget = .ok registry) :
    Cover registry (BatchDriver.initial c) := by
  intro j v hv
  have he : v = (c.searches.get j).source := by
    simpa [BatchDriver.initial, SparseDriver.initial, SparseLabels.support, SparseDriver.ofCatalog] using hv
  subst v
  exact RecordGuard.reserveMany_contains c budget _ RecordGuard.empty registry h
    (j, (c.searches.get j).source) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

theorem initSources_queries_le (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (h : initSources c budget = .ok registry) : nq ≤ budget := by
  have hc := initSources_cover c budget registry h
  have hcard : nq ≤ registry.seen.card := by
    have hs : (Finset.univ : Finset (Fin nq)).card ≤ registry.seen.card := by
      apply Finset.card_le_card_of_injOn (fun j => (j, (c.searches.get j).source))
      · intro j _
        exact hc j _ (by simp [BatchDriver.initial, SparseDriver.initial, SparseLabels.support, SparseDriver.ofCatalog])
      · intro j _ k _ he
        exact (Prod.mk.inj he).1
    simpa using hs
  exact hcard.trans (RecordGuard.registry_card c budget registry (initSources_valid c budget registry h))

theorem drive_valid (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (registry last : RecordGuard.Registry n nq)
    (state result : BatchDriver.Run n nb nq) (hv : RecordGuard.Valid c budget registry)
    (h : drive hn c stored input budget x fuel r registry state = .ok (last, result)) :
    RecordGuard.Valid c budget last :=
  drive_post hn c stored input budget x fuel r (RecordGuard.Valid c budget)
    (fun key old next hv he => RecordGuard.reserve_valid c budget key old next hv he)
    registry last state result hv h

end StreamingSSSP.Core.GuardedDriver
