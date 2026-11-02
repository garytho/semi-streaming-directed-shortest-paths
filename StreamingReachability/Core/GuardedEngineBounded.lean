module

public import StreamingReachability.Core.GuardedEngineProofs

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

def TaskProperty (P : Shared.Job n nb nq → Prop) : Shared.Engine.Task n nb nq → Prop
  | .active job => P job
  | .finished _ => True

theorem property_get {K S : Type*} [DecidableEq K] (P : S → Prop)
    (zero : S) (hz : P zero) (xs : RecordMap.Map K S) (hx : ∀ p ∈ xs, P p.2) (k : K) :
    P (RecordMap.get zero xs k) := by
  induction xs with
  | nil => exact hz
  | cons p ps ih =>
      rw [RecordMap.get_cons]
      split_ifs
      · exact hx p (by simp)
      · exact ih (fun q hq => hx q (by simp [hq]))

theorem evaluate_bounded (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : Shared.Job n nb nq → Prop) (hdouble : ∀ job, P job → P (Shared.double c job))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (job : Shared.Job n nb nq) (hj : P job) (f : DistanceArray n)
    (hf : ∀ v ∈ found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources)
      f.get (c.scale * r), (job.searchId, v) ∈ allowed)
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old) :
    ∃ next task, evaluate c budget r job f old = .ok (next, task) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next ∧ TaskProperty P task := by
  let U := found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)
  obtain ⟨next, hn, hs', hv'⟩ := RecordGuard.reserveMany_bounded c budget allowed hb
    ((U.sort (· ≤ ·)).map fun v => (job.searchId, v)) (by
      intro key hk
      obtain ⟨v, hvm, rfl⟩ := List.mem_map.mp hk
      exact hf v ((Finset.mem_sort _).mp hvm)) old hs hv
  have hr : reserveFound c budget job.searchId U old = .ok next := hn
  have hr' : reserveFound c budget job.searchId
      (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r))
      old = .ok next := hr
  refine ⟨next, Shared.Engine.evaluate c r job f, ?_, hs', hv', ?_⟩
  · unfold evaluate
    dsimp only
    rw [hr']
    unfold Shared.Engine.evaluate
    dsimp only
    split_ifs <;> rfl
  · unfold Shared.Engine.evaluate
    dsimp only
    split_ifs
    · trivial
    · exact hdouble job hj

def expectedWork (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (job : Shared.Job n nb nq) : Shared.Work n nb nq :=
  ⟨job, ViewedSkeleton.rows (Shared.view c job.searchId) (Shared.block c job.searchId job.blockId)
    (SparseLabels.support job.sources) job.threshold stored input⟩

theorem process_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ)
    (P : Shared.Job n nb nq → Prop) (hdouble : ∀ job, P job → P (Shared.double c job))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (hf : ∀ job, P job → ∀ v ∈ found (Shared.block c job.searchId job.blockId)
      (SparseLabels.support job.sources)
      (ViewedSkeleton.labels hn (Shared.view c job.searchId) (Shared.block c job.searchId job.blockId)
        (SparseLabels.support job.sources) job.threshold (SparseLabels.vector job.sources) stored input).get
      (c.scale * r), (job.searchId, v) ∈ allowed)
    (slots : List (Fin N × Shared.Job n nb nq)) (hp : ∀ slot ∈ slots, P slot.2)
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old) :
    ∃ next updates,
      process hn c budget r slots (slots.map fun slot => expectedWork c stored input slot.2) old =
        .ok (next, updates) ∧ next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next ∧
          ∀ pair ∈ updates, TaskProperty P pair.2 := by
  induction slots generalizing old with
  | nil => exact ⟨old, [], rfl, hs, hv, by simp⟩
  | cons slot slots ih =>
      have hjob := hp slot (by simp)
      obtain ⟨middle, task, heval, hs', hv', ht⟩ := evaluate_bounded c budget r P hdouble allowed hb
        slot.2 hjob
        (ViewedSkeleton.labels hn (Shared.view c slot.2.searchId) (Shared.block c slot.2.searchId slot.2.blockId)
          (SparseLabels.support slot.2.sources) slot.2.threshold (SparseLabels.vector slot.2.sources) stored input)
        (hf slot.2 hjob) old hs hv
      obtain ⟨next, tail, htail, hs'', hv'', hprops⟩ :=
        ih (fun q hq => hp q (by simp [hq])) middle hs' hv'
      refine ⟨next, (slot.1, task) :: tail, ?_, hs'', hv'', ?_⟩
      · rw [List.map_cons, process]
        change evaluate c budget r slot.2
          (StoredSearch.run (Shared.storedEdges hn (expectedWork c stored input slot.2))
            (SparseLabels.vector slot.2.sources)) old = .ok (middle, task) at heval
        simp only [heval, htail]
      · intro pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact ht
        · exact hprops pair hm

theorem pack_bounded (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (budget r : ℕ)
    (P : Shared.Job n nb nq → Prop) (hdouble : ∀ job, P job → P (Shared.double c job))
    (allowed : Finset (RecordGuard.Key n nq)) (hb : RecordGuard.weight c allowed ≤ budget)
    (hf : ∀ job, P job → ∀ v ∈ found (Shared.block c job.searchId job.blockId)
      (SparseLabels.support job.sources)
      (ViewedSkeleton.labels hn (Shared.view c job.searchId) (Shared.block c job.searchId job.blockId)
        (SparseLabels.support job.sources) job.threshold (SparseLabels.vector job.sources) stored input).get
      (c.scale * r), (job.searchId, v) ∈ allowed)
    (slots : List (Fin N × Shared.Job n nb nq)) (hp : ∀ slot ∈ slots, P slot.2)
    (old : RecordGuard.Registry n nq) (hs : old.seen ⊆ allowed) (hv : RecordGuard.Valid c budget old) :
    ∃ next result, pack hn c stored input budget r slots old = .ok (next, result) ∧
      next.seen ⊆ allowed ∧ RecordGuard.Valid c budget next ∧
        ∀ pair ∈ result.updates, TaskProperty P pair.2 := by
  obtain ⟨next, updates, hproc, hs', hv', ht⟩ :=
    process_bounded hn c stored input budget r P hdouble allowed hb hf slots hp old hs hv
  refine ⟨next, ⟨updates, 1, (Shared.scanPack c (slots.map Prod.snd) stored input).reads,
    (Shared.scanPack c (slots.map Prod.snd) stored input).peakCells⟩, ?_, hs', hv', ht⟩
  have hproc' : process hn c budget r slots
      (Shared.scanPack c (slots.map Prod.snd) stored input).state old = .ok (next, updates) := by
    rw [Shared.scanPack_state]
    simpa only [List.map_map, Function.comp_def, expectedWork] using hproc
  simp only [pack, hproc']

end StreamingReachability.Core.GuardedEngine
