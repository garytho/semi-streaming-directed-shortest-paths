module

public import StreamingReachability.Core.LiveSpace
public import StreamingReachability.Core.MeasuredViewed
public import StreamingReachability.Core.DriverWordBounds

@[expose] public section

namespace StreamingReachability.Core.BatchAPI

open StoredEdges

variable {n : ℕ}

noncomputable def semanticDistance (request : Request n) (input : List (Edge n))
    (j : Fin request.queryCount) (v : Fin n) : Distance :=
  (fullQueryGraph ((request.explicit ++ input).filterMap (Shared.view request.catalog j))
    (Shared.referenceProblem request.catalog j).blocks.toList request.catalog.scale).dist
      (request.catalog.searches.get j).source v

def ExactWithin (request : Request n) (input : List (Edge n)) (records : SparseReply n) : Prop :=
  ∀ j v, lookup records j.val v =
    if semanticDistance request input j v ≤ ((request.catalog.searches.get j).radius : Distance)
    then semanticDistance request input j v else ⊤

theorem raw_pass_bound (request : Request n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    (run request input).passes ≤ (request.radius + 1) * (Nat.log 2 request.workspace + 3) +
      16 * request.workspace * replyCharge request (run request input).records / n := by
  have h := BatchDriver.core_pass_bound hn request.catalog request.explicit input request.workspace request.radius
    hs hp hA hx (radius_bound request)
  rw [← raw_reply_charge request input hn hs hp hA hx] at h
  have he : (run request input).passes =
      (BatchDriver.execute hn request.catalog request.explicit input request.workspace (request.radius + 1)).passes := by
    simp only [run, dite_eq_left hn]
    rw [BatchDriver.executeTail_eq]
  apply Live.divide_pass_bound hn
  rw [he]
  simpa only [Nat.mul_assoc] using h

theorem runGuardedMeasured_coupled (request : Request n) (budget : ℕ) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace) :
    (runGuardedMeasured request budget input).result = .ok (run request input) ↔
      replyCharge request (run request input).records ≤ budget := by
  rw [runGuardedMeasured_erases]
  exact runGuarded_coupled request budget input hn hs hp hA hx

theorem raw_records_sensitive_space (request : Request n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (hspace : 2 * request.workspace * request.workspace ≤ n) :
    (runGuardedMeasured request (replyCharge request (run request input).records) input).result =
      .ok (run request input) ∧
      MemorySafe hn request (replyCharge request (run request input).records) input := by
  exact ⟨(runGuardedMeasured_coupled request _ input hn hs hp hA hx).mpr (Nat.le_refl _),
    runGuarded_every_prefix_space hn request _ input hs hp hA hx hspace⟩

/-- The deterministic core: genuine streamed execution, exact whole-closure
rounding, and closed scan/record/space contracts. No search, schedule, accuracy,
or resource certificate is an input. -/
theorem deterministic_core (request : Request n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (hspace : 2 * request.workspace * request.workspace ≤ n) :
    ExactWithin request input (run request input).records ∧
      (run request input).passes ≤ (request.radius + 1) * (Nat.log 2 request.workspace + 3) +
        16 * request.workspace * replyCharge request (run request input).records / n ∧
      (∀ budget, MemorySafe hn request budget input) ∧
      (∀ budget, (runGuardedMeasured request budget input).result = .ok (run request input) ↔
        replyCharge request (run request input).records ≤ budget) ∧
      (∀ budget, (runGuardedMeasured request budget input).passes ≤
        (request.radius + 1) * (Nat.log 2 request.workspace + 3) + 32 * request.workspace * budget / n) := by
  refine ⟨?_, raw_pass_bound request input hn hs hp hA hx, ?_, ?_, ?_⟩
  · intro j v
    exact run_correct request input hn hs hp hA hx j v
  · intro budget
    exact runGuarded_every_prefix_space hn request budget input hs hp hA hx hspace
  · intro budget
    exact runGuardedMeasured_coupled request budget input hn hs hp hA hx
  · intro budget
    exact runGuardedMeasured_pass_bound hn request budget input hs hp hA hx

theorem deterministic_core_viewed {E : Type*} (request : Request n)
    (view : E → Option (Edge n)) (input : List E) (hn : 0 < n)
    (hs : ∀ e ∈ request.explicit, 0 < e.weight) (hp : ∀ e ∈ input.filterMap view, 0 < e.weight)
    (hA : 0 < request.catalog.scale)
    (hx : ∀ i, (request.catalog.blocks.get i).card ≤ request.workspace)
    (hspace : 2 * request.workspace * request.workspace ≤ n) :
    (∀ budget, (runGuardedMeasuredViewed request budget view input).result =
      .ok (run request (input.filterMap view)) ↔
        replyCharge request (run request (input.filterMap view)).records ≤ budget) ∧
      (∀ budget, (runGuardedMeasuredViewed request budget view input).passes ≤
        (request.radius + 1) * (Nat.log 2 request.workspace + 3) + 32 * request.workspace * budget / n) ∧
      (∀ budget, MemorySafe hn request budget (input.filterMap view)) ∧
      ExactWithin request (input.filterMap view) (run request (input.filterMap view)).records := by
  have h := deterministic_core request (input.filterMap view) hn hs hp hA hx hspace
  refine ⟨?_, ?_, h.2.2.1, h.1⟩
  · intro budget
    rw [runGuardedMeasuredViewed_eq]
    exact h.2.2.2.1 budget
  · intro budget
    exact runGuardedMeasuredViewed_pass_bound hn request budget view input hs hp hA hx

end StreamingReachability.Core.BatchAPI
