module

public import StreamingSSSP.Core.MeasuredPrefixes

@[expose] public section

set_option maxHeartbeats 1000000

namespace StreamingSSSP.Core.PassMeter

open StoredEdges

theorem solve_prefix {n : ℕ} (hn : 0 < n) (request : BatchAPI.Request n)
    (budget : ℕ) (input : List (Edge n)) :
    ∃ point : BatchAPI.PassPrefix hn request budget input, (solve request budget input).passes = point.passes := by
  unfold solve
  rw [dite_eq_left hn]
  cases hi : GuardedDriver.initSources request.catalog budget with
  | error reason =>
      refine ⟨.initializing, rfl⟩
  | ok first =>
      simp only
      let initial : BatchDriver.Run n request.blockCount request.queryCount :=
        ⟨BatchDriver.initial request.catalog, 0, 0, 0, 0⟩
      change ∃ point : BatchAPI.PassPrefix hn request budget input,
        (drive hn request.catalog request.explicit input budget request.workspace
          (request.radius + 1) 0 first initial).passes = point.passes
      cases hd : (drive hn request.catalog request.explicit input budget request.workspace
          (request.radius + 1) 0 first initial).result with
      | error reason =>
          obtain ⟨k, hk, before, out, hp, error, hr, hc⟩ :=
            drive_abort_prefix hn request.catalog request.explicit input budget request.workspace
              (request.radius + 1) 0 first initial reason hd
          let p : Live.Boundary hn request.catalog request.explicit input budget request.workspace :=
            ⟨k, first, before, out, hi, hp⟩
          have hclock : p.rounds ≤ request.radius := by dsimp only [p]; omega
          simp only [Nat.zero_add] at hr hc
          obtain ⟨point, hpoint⟩ := round_successful_blocks (R := request.radius) p hclock error hr
          exact ⟨point, hc.trans hpoint⟩
      | ok pair =>
          obtain ⟨last, out⟩ := pair
          have hp : GuardedDriver.drive hn request.catalog request.explicit input budget request.workspace
              (request.radius + 1) 0 first initial = .ok (last, out) :=
            (drive_erases _ _ _ _ _ _ _ _ _ _).symm.trans hd
          let p : Live.Boundary hn request.catalog request.explicit input budget request.workspace :=
            ⟨request.radius + 1, first, last, out, hi, hp⟩
          refine ⟨.boundary p (Nat.le_refl _), ?_⟩
          exact drive_success_passes hn request.catalog request.explicit input budget request.workspace
            (request.radius + 1) 0 first last initial out hd

end StreamingSSSP.Core.PassMeter

namespace StreamingSSSP.Core.BatchAPI

theorem runGuardedMeasured_pass_bound {n : ℕ} (hn : 0 < n) (request : Request n)
    (budget : ℕ) (input : List (StoredEdges.Edge n))
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    (runGuardedMeasured request budget input).passes ≤
      (request.radius + 1) * (Nat.log 2 request.workspace + 3) + 32 * request.workspace * budget / n := by
  obtain ⟨point, he⟩ := PassMeter.solve_prefix hn request budget input
  change (PassMeter.solve request budget input).passes ≤ _
  rw [he]
  exact prefix_pass_bound hn request budget input point hs hp hA hx

end StreamingSSSP.Core.BatchAPI
