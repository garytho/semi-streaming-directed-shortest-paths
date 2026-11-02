module

public import StreamingReachability.Hopset.TrialFacts
public import StreamingReachability.Probability.Projection

@[expose] public section

namespace StreamingReachability.Hopset

variable {n ns : ℕ}

def pivotsFromOwners (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) :
    (targets : List (Target n ns)) → ℕ →
      (Fin targets.length → Fin cfg.groups × Fin cfg.shifts) → List (Pivot n ns)
  | [], _, _ => []
  | target :: targets, offset, owners =>
      let rest := pivotsFromOwners cfg r sets reply targets (offset + 1)
        (fun i => owners i.succ)
      if target.kind = .pivot then
        let owner := owners 0
        ⟨target.setId, target.vertex,
          chooseEta cfg r (sets.get target.setId) reply (2 * offset) (2 * offset + 1)
            owner.1 owner.2,
          owner.2.val, 2 * offset, 2 * offset + 1⟩ :: rest
      else rest

theorem expect_pivotLoop (handler : Code.Handler n) (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (offset : ℕ) (f : Option (List (Pivot n ns)) → ℝ) :
    (Code.evaluate handler (pivotLoop cfg r sets reply targets offset)).expect f =
      (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
          (fun owners => f (some (pivotsFromOwners cfg r sets reply targets offset owners))) := by
  induction targets generalizing offset f with
  | nil => simp [pivotLoop, pivotsFromOwners, Code.evaluate, Law.family]
  | cons target targets ih =>
      simp only [List.length_cons]
      dsimp only [pivotLoop]
      split
      next hk =>
        rw [Code.expect_bind, Code.expect_drawPair, Law.expect_family_succ]
        apply congrArg (Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos).expect
        funext owner
        dsimp only
        rw [Code.expect_map]
        simpa only [pivotsFromOwners, hk, ↓reduceIte, Fin.cases_zero, Fin.cases_succ,
          Option.map_some] using
          ih (offset + 1) (fun result => f (result.map fun ps =>
            ⟨target.setId, target.vertex,
              chooseEta cfg r (sets.get target.setId) reply (2 * offset) (2 * offset + 1)
                owner.1 owner.2,
              owner.2.val, 2 * offset, 2 * offset + 1⟩ :: ps))
      next hk =>
        rw [Law.expect_family_succ]
        simp only [pivotsFromOwners, hk, ↓reduceIte, Fin.cases_succ]
        rw [Law.expect_const]
        exact ih (offset + 1) f

end StreamingReachability.Hopset
