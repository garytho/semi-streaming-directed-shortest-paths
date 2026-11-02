module

public import StreamingReachability.Hopset.OwnerGeometry

@[expose] public section

namespace StreamingReachability.Hopset

open scoped Classical

variable {n ns : ℕ}

theorem pivotFilter_flatMap {A : Type*} (L : List A) (f : A → List (Target n ns)) :
    ((L.flatMap f).filter fun target => decide (target.kind = .pivot)) =
      L.flatMap (fun a => (f a).filter fun target => decide (target.kind = .pivot)) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.flatMap_cons, List.filter_append, ih]

theorem pivotFilter_map (vertices : List (Fin n)) (i : Fin ns) (kind : TargetKind) :
    ((vertices.map fun v => (⟨i, v, kind⟩ : Target n ns)).filter
        fun target => decide (target.kind = .pivot)) =
      if kind = .pivot then vertices.map (fun v => ⟨i, v, kind⟩) else [] := by
  induction vertices with
  | nil => simp
  | cons v vertices ih => by_cases hk : kind = .pivot <;> simp [hk, ih]

theorem earlyTargets_pivotFilter (cfg : Config) (r : ℕ) (rank : Vector ℕ n)
    (sets : Vector (Finset (Fin n)) ns) (hr : r < cfg.earlyLevel) :
    ((earlyTargets cfg r rank sets).filter fun target => decide (target.kind = .pivot)) =
      pivotTargets (fun i => CopyHistory.pivots (sets.get i) r (fun v => rank.get v)) := by
  rw [earlyTargets, pivotFilter_flatMap, pivotTargets]
  apply List.flatMap_congr
  intro i hi
  rw [List.filter_append, pivotFilter_map, pivotFilter_map]
  simpa using congrArg (List.map fun v => (⟨i, v, .pivot⟩ : Target n ns))
    (pivotMembers_eq cfg r rank (sets.get i) hr)

theorem pivotTargets_pivotFilter (P : Fin ns → Finset (Fin n)) :
    ((pivotTargets P).filter fun target => decide (target.kind = .pivot)) = pivotTargets P := by
  rw [pivotTargets, pivotFilter_flatMap]
  apply List.flatMap_congr
  intro i hi
  rw [pivotFilter_map]
  simp

theorem pivotsFromOwners_keys (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (offset : ℕ) :
    ∀ owners : Fin targets.length → Fin cfg.groups × Fin cfg.shifts,
      (pivotsFromOwners cfg r sets reply targets offset owners).map (fun p => (p.setId, p.vertex)) =
        ((targets.filter fun target => decide (target.kind = .pivot)).map fun target =>
          (target.setId, target.vertex)) := by
  induction targets generalizing offset with
  | nil => intro owners; rfl
  | cons target targets ih =>
      intro owners
      by_cases hk : target.kind = .pivot <;> simp [pivotsFromOwners, hk, ih]

end StreamingReachability.Hopset
