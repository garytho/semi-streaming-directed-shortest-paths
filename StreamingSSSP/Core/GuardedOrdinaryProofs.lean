module

public import StreamingSSSP.Core.GuardedDriver
public import StreamingSSSP.Core.OrdinaryPeak

@[expose] public section

namespace StreamingSSSP.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

def ordinaryFunction (c : Shared.Catalog n nb ns nq) (r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq) (C : Finset (Fin n)) :
    Finset (Fin n) :=
  match ordinaryTarget c r old raw j with
  | none => C
  | some v => insert v C

theorem ordinaryFunction_eq (c : Shared.Catalog n nb ns nq) (r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq) (C : Finset (Fin n)) :
    ordinaryFunction c r old raw j C =
      if r ≤ (c.searches.get j).radius
      then SparseDriver.edgeStep (SparseDriver.ofCatalog c j) r (old.get j) C raw else C := by
  by_cases ha : r ≤ (c.searches.get j).radius
  · cases hv : Shared.view c j raw with
    | none => simp [ordinaryFunction, ordinaryTarget, ha, hv, SparseDriver.edgeStep, SparseDriver.ofCatalog]
    | some e =>
        by_cases he : e.source ∈ (old.get j).settled ∧ e.target ∉ (old.get j).settled ∧
            SparseLabels.get (old.get j).labels e.source + (ceilNat c.scale e.weight : Distance) ≤ (r : Distance) <;>
          simp [ordinaryFunction, ordinaryTarget, ha, hv, he,
            SparseDriver.edgeStep, SparseDriver.ofCatalog, Global.edgeStep]
  · simp [ordinaryFunction, ordinaryTarget, ha]

theorem ordinaryOne_erases (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq)
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (h : ordinaryOne c budget r old raw j registry C = .ok (last, result)) :
    result = VectorStore.set C j (ordinaryFunction c r old raw j (C.get j)) := by
  unfold ordinaryOne at h
  cases ht : ordinaryTarget c r old raw j with
  | none =>
      simp only [ht] at h
      cases h
      rw [ordinaryFunction, ht, VectorStore.set_get]
  | some v =>
      simp only [ht] at h
      cases hg : RecordGuard.reserve c budget (j, v) registry with
      | error reason => simp [hg] at h
      | ok next =>
          simp only [hg] at h
          have he := (congrArg Prod.snd (Except.ok.inj h)).symm
          dsimp only at he
          rw [he, ordinaryFunction, ht]

theorem ordinaryOne_valid (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq)
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (hv : RecordGuard.Valid c budget registry)
    (h : ordinaryOne c budget r old raw j registry C = .ok (last, result)) :
    RecordGuard.Valid c budget last := by
  unfold ordinaryOne at h
  cases ht : ordinaryTarget c r old raw j with
  | none => simp only [ht] at h; cases h; exact hv
  | some v =>
      simp only [ht] at h
      cases hg : RecordGuard.reserve c budget (j, v) registry with
      | error reason => simp [hg] at h
      | ok next =>
          simp only [hg] at h
          have he := congrArg Prod.fst (Except.ok.inj h)
          dsimp only at he
          rw [← he]
          exact RecordGuard.reserve_valid c budget (j, v) registry next hv hg

theorem ordinaryQueries_erases (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (indices : List (Fin nq))
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (h : ordinaryQueries c budget r old raw indices registry C = .ok (last, result)) :
    result = VectorStore.applyEach (ordinaryFunction c r old raw) indices C := by
  induction indices generalizing registry C with
  | nil => cases h; rfl
  | cons j js ih =>
      rw [ordinaryQueries] at h
      cases hg : ordinaryOne c budget r old raw j registry C with
      | error reason => simp [hg] at h
      | ok pair =>
          obtain ⟨middle, next⟩ := pair
          simp only [hg] at h
          have he := ordinaryOne_erases c budget r old raw j registry middle C next hg
          rw [ih middle next h, he]
          rfl

theorem ordinaryQueries_valid (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (indices : List (Fin nq))
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (hv : RecordGuard.Valid c budget registry)
    (h : ordinaryQueries c budget r old raw indices registry C = .ok (last, result)) :
    RecordGuard.Valid c budget last := by
  induction indices generalizing registry C with
  | nil => cases h; exact hv
  | cons j js ih =>
      rw [ordinaryQueries] at h
      cases hg : ordinaryOne c budget r old raw j registry C with
      | error reason => simp [hg] at h
      | ok pair =>
          obtain ⟨middle, next⟩ := pair
          simp only [hg] at h
          exact ih middle next (ordinaryOne_valid c budget r old raw j registry middle C next hv hg) h

theorem apply_ordinary_all (c : Shared.Catalog n nb ns nq) (r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (C : Vector (Finset (Fin n)) nq) :
    VectorStore.applyEach (ordinaryFunction c r old raw) (List.finRange nq) C =
      BatchDriver.ordinaryStep c r old C raw := by
  rw [VectorStore.applyEach_all]
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  rw [Vector.get_ofFn, Vector.get_ofFn]
  exact ordinaryFunction_eq c r old raw _ _

theorem ordinaryScan_erases (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (input : List (Edge n))
    (registry last : RecordGuard.Registry n nq) (C result : Vector (Finset (Fin n)) nq)
    (h : ordinaryScan c budget r old input registry C = .ok (last, result)) :
    result = input.foldl (BatchDriver.ordinaryStep c r old) C := by
  induction input generalizing registry C with
  | nil => cases h; rfl
  | cons raw rest ih =>
      rw [ordinaryScan] at h
      cases hg : ordinaryQueries c budget r old raw (List.finRange nq) registry C with
      | error reason => simp [hg] at h
      | ok pair =>
          obtain ⟨middle, next⟩ := pair
          simp only [hg] at h
          have he := ordinaryQueries_erases c budget r old raw _ registry middle C next hg
          rw [apply_ordinary_all] at he
          rw [ih middle next h, he]
          rfl

theorem ordinary_erases (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (registry last : RecordGuard.Registry n nq) (result : Vector (Finset (Fin n)) nq)
    (h : ordinary c budget r old stored input registry = .ok (last, result)) :
    result = (BatchDriver.ordinary c r old stored input).state := by
  unfold ordinary at h
  cases hg : ordinaryScan c budget r old stored registry (Vector.replicate nq ∅) with
  | error reason => simp [hg] at h
  | ok pair =>
      obtain ⟨middle, next⟩ := pair
      simp only [hg] at h
      rw [ordinaryScan_erases c budget r old input middle last next result h,
        ordinaryScan_erases c budget r old stored registry middle _ next hg]
      rw [BatchDriver.ordinary, Streaming.readPass_state]

end StreamingSSSP.Core.GuardedDriver
