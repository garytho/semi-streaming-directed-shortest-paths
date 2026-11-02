module

public import StreamingSSSP.Core.GuardedPosts
public import StreamingSSSP.Core.GuardedDriver

@[expose] public section

namespace StreamingSSSP.Core

namespace RecordGuard

variable {n nb ns nq : ℕ}

theorem reserveMany_post (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (P : Registry n nq → Prop)
    (hp : ∀ key old next, P old → reserve c budget key old = .ok next → P next)
    (keys : List (Key n nq)) (old next : Registry n nq) (hP : P old)
    (h : reserveMany c budget keys old = .ok next) : P next := by
  induction keys generalizing old with
  | nil => cases h; exact hP
  | cons key keys ih =>
      rw [reserveMany] at h
      cases hr : reserve c budget key old with
      | error reason => simp [hr] at h
      | ok middle =>
          simp only [hr] at h
          exact ih middle (hp key old middle hP hr) h

end RecordGuard

namespace GuardedEngine

open StoredEdges

variable {n nb ns nq : ℕ}

theorem evaluate_post (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (job : Shared.Job n nb nq) (f : DistanceArray n) (old next : RecordGuard.Registry n nq)
    (task : Shared.Engine.Task n nb nq) (hP : P old)
    (h : evaluate c budget r job f old = .ok (next, task)) : P next := by
  unfold evaluate at h
  cases hg : reserveFound c budget job.searchId
      (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)) old with
  | error reason => simp [hg] at h
  | ok middle =>
      simp only [hg] at h
      have hm := RecordGuard.reserveMany_post c budget P hp _ old middle hP hg
      split_ifs at h <;> cases h <;> exact hm

end GuardedEngine

namespace GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem ordinaryOne_post (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq)
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (hP : P registry) (h : ordinaryOne c budget r old raw j registry C = .ok (last, result)) : P last := by
  unfold ordinaryOne at h
  cases ht : ordinaryTarget c r old raw j with
  | none => simp only [ht] at h; cases h; exact hP
  | some v =>
      simp only [ht] at h
      cases hg : RecordGuard.reserve c budget (j, v) registry with
      | error reason => simp [hg] at h
      | ok next =>
          simp only [hg] at h
          have he := congrArg Prod.fst (Except.ok.inj h)
          dsimp only at he
          rw [← he]
          exact hp (j, v) registry next hP hg

theorem ordinaryQueries_post (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (indices : List (Fin nq))
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (hP : P registry)
    (h : ordinaryQueries c budget r old raw indices registry C = .ok (last, result)) : P last := by
  induction indices generalizing registry C with
  | nil => cases h; exact hP
  | cons j js ih =>
      rw [ordinaryQueries] at h
      cases hg : ordinaryOne c budget r old raw j registry C with
      | error reason => simp [hg] at h
      | ok pair =>
          obtain ⟨middle, next⟩ := pair
          simp only [hg] at h
          exact ih middle next (ordinaryOne_post c budget r P hp old raw j registry middle C next hP hg) h

theorem ordinaryScan_post (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (old : BatchDriver.States n nb nq) (input : List (Edge n))
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (hP : P registry)
    (h : ordinaryScan c budget r old input registry C = .ok (last, result)) : P last := by
  induction input generalizing registry C with
  | nil => cases h; exact hP
  | cons raw rest ih =>
      rw [ordinaryScan] at h
      cases hg : ordinaryQueries c budget r old raw (List.finRange nq) registry C with
      | error reason => simp [hg] at h
      | ok pair =>
          obtain ⟨middle, next⟩ := pair
          simp only [hg] at h
          exact ih middle next
            (ordinaryQueries_post c budget r P hp old raw _ registry middle C next hP hg) h

theorem ordinary_post (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (registry last : RecordGuard.Registry n nq) (result : Vector (Finset (Fin n)) nq) (hP : P registry)
    (h : ordinary c budget r old stored input registry = .ok (last, result)) : P last := by
  unfold ordinary at h
  cases hg : ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | error reason => simp [hg] at h
  | ok pair =>
      obtain ⟨middle, C⟩ := pair
      simp only [hg] at h
      exact ordinaryScan_post c budget r P hp old input middle last C result
        (ordinaryScan_post c budget r P hp old stored registry middle _ C hP hg) h

theorem finishQueries_post (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (old : BatchDriver.States n nb nq) (C : Vector (Finset (Fin n)) nq)
    (replies : RecordMap.Map (Fin nq × Fin nb) (Option (BlockSearch.Outcome n)))
    (indices : List (Fin nq)) (registry last : RecordGuard.Registry n nq)
    (acc result : BatchDriver.States n nb nq) (hP : P registry)
    (h : finishQueries c budget r old C replies indices registry acc = .ok (last, result)) : P last := by
  induction indices generalizing registry acc with
  | nil => cases h; exact hP
  | cons j js ih =>
      rw [finishQueries] at h
      cases hg : GuardedEngine.reserveFound c budget j (proposed c r j (old.get j) (C.get j) replies) registry with
      | error reason => simp [hg] at h
      | ok next =>
          simp only [hg] at h
          exact ih next _ (RecordGuard.reserveMany_post c budget P hp _ registry next hP hg) h

theorem round_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x r : ℕ) (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (old : BatchDriver.States n nb nq) (registry last : RecordGuard.Registry n nq)
    (result : BatchDriver.Round n nb nq) (hP : P registry)
    (h : round hn c stored input budget x r old registry = .ok (last, result)) : P last := by
  unfold round at h
  cases hb : GuardedEngine.run hn c stored input budget r (Nat.log 2 x + 2)
      (BatchDriver.tasks (BatchDriver.jobs c r old)) registry with
  | error reason => simp [hb] at h
  | ok pair =>
      obtain ⟨afterBlocks, blocks⟩ := pair
      simp only [hb] at h
      have hB := GuardedEngine.runAux_post hn c stored input budget r (Nat.log 2 x + 2) P
        (fun job f old next task hP he => GuardedEngine.evaluate_post c budget r P hp job f old next task hP he)
        _ registry afterBlocks 0 0 0 blocks hP hb
      cases ho : ordinary c budget r old stored input afterBlocks with
      | error reason => simp [ho] at h
      | ok pair =>
          obtain ⟨afterEdges, candidates⟩ := pair
          simp only [ho] at h
          have hE := ordinary_post c budget r P hp old stored input afterBlocks afterEdges candidates hB ho
          cases hf : finishQueries c budget r old candidates
              (BatchDriver.answers (BatchDriver.jobs c r old) blocks.tasks) (List.finRange nq) afterEdges old with
          | error reason => simp [hf] at h
          | ok pair =>
              obtain ⟨endRegistry, states⟩ := pair
              simp only [hf] at h
              have he := congrArg Prod.fst (Except.ok.inj h)
              dsimp only at he
              rw [← he]
              exact finishQueries_post c budget r P hp old candidates _ _ afterEdges endRegistry old states hE hf

theorem drive_post (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (budget x fuel r : ℕ) (P : RecordGuard.Registry n nq → Prop)
    (hp : ∀ key old next, P old → RecordGuard.reserve c budget key old = .ok next → P next)
    (registry last : RecordGuard.Registry n nq) (state result : BatchDriver.Run n nb nq)
    (hP : P registry)
    (h : drive hn c stored input budget x fuel r registry state = .ok (last, result)) : P last := by
  induction fuel generalizing r registry state with
  | zero => cases h; exact hP
  | succ fuel ih =>
      rw [drive] at h
      cases hs : round hn c stored input budget x r state.states registry with
      | error reason => simp [hs] at h
      | ok pair =>
          obtain ⟨next, step⟩ := pair
          simp only [hs] at h
          exact ih (r + 1) next _ (round_post hn c stored input budget x r P hp state.states registry next step hP hs) h

end GuardedDriver

end StreamingSSSP.Core
