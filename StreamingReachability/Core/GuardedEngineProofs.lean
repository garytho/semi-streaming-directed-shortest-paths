module

public import StreamingReachability.Core.GuardedEngine

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

theorem process_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (h : process hn c budget r slots works old = .ok (last, updates)) :
    updates = slots.zipWith (Shared.Engine.completeWork hn c r) works := by
  induction slots generalizing works old last updates with
  | nil => cases h; rfl
  | cons slot slots ih =>
      cases works with
      | nil => cases h; rfl
      | cons work works =>
          rw [process] at h
          cases he : evaluate c budget r slot.2
              (StoredSearch.run (Shared.storedEdges hn work) (SparseLabels.vector slot.2.sources)) old with
          | error reason => simp [he] at h
          | ok pair =>
              obtain ⟨middle, task⟩ := pair
              simp only [he] at h
              cases ht : process hn c budget r slots works middle with
              | error reason => simp [ht] at h
              | ok pair =>
                  obtain ⟨endRegistry, tail⟩ := pair
                  simp only [ht] at h
                  have hu := congrArg Prod.snd (Except.ok.inj h)
                  dsimp only at hu
                  rw [← hu, evaluate_erases c budget r _ _ old middle task he,
                    ih works middle endRegistry tail ht]
                  rfl

theorem process_valid (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (slots : List (Fin N × Shared.Job n nb nq)) (works : List (Shared.Work n nb nq))
    (old last : RecordGuard.Registry n nq) (updates : RecordMap.Map (Fin N) (Shared.Engine.Task n nb nq))
    (hv : RecordGuard.Valid c budget old)
    (h : process hn c budget r slots works old = .ok (last, updates)) : RecordGuard.Valid c budget last := by
  induction slots generalizing works old last updates with
  | nil => cases h; exact hv
  | cons slot slots ih =>
      cases works with
      | nil => cases h; exact hv
      | cons work works =>
          rw [process] at h
          cases he : evaluate c budget r slot.2
              (StoredSearch.run (Shared.storedEdges hn work) (SparseLabels.vector slot.2.sources)) old with
          | error reason => simp [he] at h
          | ok pair =>
              obtain ⟨middle, task⟩ := pair
              simp only [he] at h
              have hm := evaluate_valid c budget r _ _ old middle task hv he
              cases ht : process hn c budget r slots works middle with
              | error reason => simp [ht] at h
              | ok pair =>
                  obtain ⟨endRegistry, tail⟩ := pair
                  simp only [ht] at h
                  have heq := congrArg Prod.fst (Except.ok.inj h)
                  dsimp only at heq
                  rw [← heq]
                  exact ih works middle endRegistry tail hm ht

theorem pack_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (slots : List (Fin N × Shared.Job n nb nq))
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Phase n nb nq N)
    (h : pack hn c stored input budget r slots old = .ok (last, result)) :
    result = Shared.Engine.executePackResult hn c stored input r slots := by
  unfold pack at h
  cases hp : process hn c budget r slots (Shared.scanPack c (slots.map Prod.snd) stored input).state old with
  | error reason => simp [hp] at h
  | ok pair =>
      obtain ⟨next, updates⟩ := pair
      simp only [hp] at h
      have he := (congrArg Prod.snd (Except.ok.inj h)).symm
      dsimp only at he
      rw [he, process_erases hn c budget r slots _ old next updates hp]
      rfl

theorem pack_valid (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (slots : List (Fin N × Shared.Job n nb nq))
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Phase n nb nq N)
    (hv : RecordGuard.Valid c budget old)
    (h : pack hn c stored input budget r slots old = .ok (last, result)) : RecordGuard.Valid c budget last := by
  unfold pack at h
  cases hp : process hn c budget r slots (Shared.scanPack c (slots.map Prod.snd) stored input).state old with
  | error reason => simp [hp] at h
  | ok pair =>
      obtain ⟨next, updates⟩ := pair
      simp only [hp] at h
      have he := congrArg Prod.fst (Except.ok.inj h)
      dsimp only at he
      rw [← he]
      exact process_valid hn c budget r slots _ old next updates hv hp

theorem packs_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (packages : List (List (Fin N × Shared.Job n nb nq)))
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Phase n nb nq N)
    (h : packs hn c stored input budget r packages old = .ok (last, result)) :
    result = Shared.Engine.executePacks hn c stored input r packages := by
  induction packages generalizing old last result with
  | nil => cases h; rfl
  | cons slots rest ih =>
      rw [packs] at h
      cases hp : pack hn c stored input budget r slots old with
      | error reason => simp [hp] at h
      | ok pair =>
          obtain ⟨middle, first⟩ := pair
          simp only [hp] at h
          cases ht : packs hn c stored input budget r rest middle with
          | error reason => simp [ht] at h
          | ok pair =>
              obtain ⟨endRegistry, tail⟩ := pair
              simp only [ht] at h
              have he := (congrArg Prod.snd (Except.ok.inj h)).symm
              dsimp only at he
              rw [he, pack_erases hn c stored input budget r slots old middle first hp,
                ih middle endRegistry tail ht]
              rfl

theorem packs_valid (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r : ℕ) (packages : List (List (Fin N × Shared.Job n nb nq)))
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Phase n nb nq N)
    (hv : RecordGuard.Valid c budget old)
    (h : packs hn c stored input budget r packages old = .ok (last, result)) :
    RecordGuard.Valid c budget last := by
  induction packages generalizing old last result with
  | nil => cases h; exact hv
  | cons slots rest ih =>
      rw [packs] at h
      cases hp : pack hn c stored input budget r slots old with
      | error reason => simp [hp] at h
      | ok pair =>
          obtain ⟨middle, first⟩ := pair
          simp only [hp] at h
          have hm := pack_valid hn c stored input budget r slots old middle first hv hp
          cases ht : packs hn c stored input budget r rest middle with
          | error reason => simp [ht] at h
          | ok pair =>
              obtain ⟨endRegistry, tail⟩ := pair
              simp only [ht] at h
              have he := congrArg Prod.fst (Except.ok.inj h)
              dsimp only at he
              rw [← he]
              exact ih middle endRegistry tail hm ht

theorem runAux_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (old last : RecordGuard.Registry n nq) (scans reservations peak : ℕ)
    (result : Shared.Engine.Run n nb nq N)
    (h : runAux hn c stored input budget r fuel tasks old scans reservations peak = .ok (last, result)) :
    result = Shared.Engine.runTailAux hn c stored input r fuel tasks scans reservations peak := by
  induction fuel generalizing tasks old scans reservations peak with
  | zero => cases h; rfl
  | succ fuel ih =>
      rw [runAux] at h
      cases hp : phase hn c stored input budget r tasks old with
      | error reason => simp [hp] at h
      | ok pair =>
          obtain ⟨middle, replies⟩ := pair
          simp only [hp] at h
          have he : replies = Shared.Engine.phase hn c stored input r tasks :=
            packs_erases hn c stored input budget r _ old middle replies hp
          subst replies
          exact ih _ middle _ _ _ h

theorem run_erases (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget r fuel : ℕ) (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (old last : RecordGuard.Registry n nq) (result : Shared.Engine.Run n nb nq N)
    (h : run hn c stored input budget r fuel tasks old = .ok (last, result)) :
    result = Shared.Engine.runTail hn c stored input r fuel tasks :=
  runAux_erases hn c stored input budget r fuel tasks old last 0 0 0 result h

end StreamingReachability.Core.GuardedEngine
