module

public import StreamingReachability.Hopset.PathAudit

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

inductive Run (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) :
    (r : ℕ) → State cfg stored input r → Prop
  | root : Run cfg hnum stored input root ranks 0 root
  | step {r : ℕ} {st : State cfg stored input r}
      (previous : Run cfg hnum stored input root ranks r st)
      (early : r < cfg.earlyLevel) (good : Batched.AllGood cfg stored input r st.queue)
      (owners : Fin st.queue.toArray.size → Reference.Owners n cfg) :
      Run cfg hnum stored input root ranks (r + 1)
        (st.update hnum early (fun v => decide (ranks v = r), owners))

def HasRun {cfg : Config} (hnum : 0 < cfg.initialNumerator)
    {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) {r : ℕ} :
    Option (State cfg stored input r) → Prop
  | none => True
  | some st => Run cfg hnum stored input root ranks r st

theorem fixedPathStateLaw_run (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (r : ℕ) :
    Early.Sampling.Holds (fixedPathStateLaw cfg hnum stored input root ranks r) (HasRun hnum root ranks) := by
  induction r with
  | zero => exact Early.Sampling.holds_pure (some root) _ Run.root
  | succ r ih =>
      refine Reference.holds_bind_on _ _ (HasRun hnum root ranks) (HasRun hnum root ranks) ih ?_
      intro state hrun
      cases state with
      | none => exact Early.Sampling.holds_pure none _ trivial
      | some st =>
          by_cases he : r < cfg.earlyLevel
          · by_cases hg : Batched.AllGood cfg stored input r st.queue
            · simp only [fixedPathStep, he, hg, ↓reduceDIte, ↓reduceIte]
              refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
              intro owners _
              exact Run.step hrun he hg owners
            · simpa only [fixedPathStep, he, hg, ↓reduceDIte, ↓reduceIte] using
                Early.Sampling.holds_pure (none : Option (State cfg stored input (r + 1))) (HasRun hnum root ranks) trivial
          · simpa only [fixedPathStep, he, ↓reduceDIte] using
              Early.Sampling.holds_pure (none : Option (State cfg stored input (r + 1))) (HasRun hnum root ranks) trivial

theorem Run.known {cfg : Config} {hnum : 0 < cfg.initialNumerator} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {root : State cfg stored input 0} {ranks : Fin n → ℕ}
    {r : ℕ} {st : State cfg stored input r} (h : Run cfg hnum stored input root ranks r st) :
    st.known = (fun v => RankPrefix.observe r (ranks v)) := by
  induction h with
  | root =>
      funext v
      have ho : RankPrefix.observe 0 (ranks v) = none := by simp [RankPrefix.observe]
      rw [ho]
      cases hx : root.known v with
      | none => rfl
      | some i => exact Fin.elim0 i
  | @step r st previous early good owners ih =>
      funext v
      change RankPrefix.nextKnown r (st.known v) (decide (ranks v = r)) = RankPrefix.observe (r + 1) (ranks v)
      rw [congrFun ih v]
      exact (RankPrefix.observe_next r (ranks v)).symm

theorem Run.levels {cfg : Config} {hnum : 0 < cfg.initialNumerator} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {root : State cfg stored input 0} {ranks : Fin n → ℕ}
    {r : ℕ} {st : State cfg stored input r} (h : Run cfg hnum stored input root ranks r st)
    (hroot : root.layers = []) : st.layers.map Layer.level = List.range r := by
  induction h with
  | root => simp only [hroot, List.map_nil, List.range_zero]
  | @step r st previous early good owners ih =>
      simpa only [State.update, List.map_append, List.map_singleton, List.range_succ] using
        congrArg (· ++ [r]) ih

theorem probability_of_holds {A : Type*} (mu : Law A) (P : A → Prop)
    (h : Early.Sampling.Holds mu P) : mu.prob P = 1 := by
  calc
    _ = mu.expect (fun _ => 1) := by
      apply Reference.expect_congr_on
      refine Early.Sampling.holds_mono h ?_
      intro a ha
      simp only [ha, ↓reduceIte]
    _ = _ := Law.expect_const _ _

theorem geometric_replay_run (cfg : Config) (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (fuel : ℕ) (hfuel : cfg.earlyLevel ≤ fuel)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    (Batched.geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue).prob
      (fun trace => HasRun hnum root ranks
        (replayEarly cfg hnum stored input root ranks (trace.map Batched.GeometricEntry.control))) = 1 := by
  have he := geometric_replay_fixed cfg hnum stored input hn root ranks fuel hfuel hs hp hsize
    (fun state => if HasRun hnum root ranks state then 1 else 0)
  exact he.trans (probability_of_holds _ _ (fixedPathStateLaw_run cfg hnum stored input root ranks cfg.earlyLevel))

end

end StreamingReachability.Hopset.Following
