module

public import StreamingReachability.Hopset.PathControlReplay

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem iterateLaw_add {A : Type*} (kernel : A → Law A) (a : A) (left right : ℕ) (f : A → ℝ) :
    (iterateLaw kernel (left + right) a).expect f =
      (iterateLaw kernel left a).expect (fun b => (iterateLaw kernel right b).expect f) := by
  induction left generalizing a with
  | zero => simp only [Nat.zero_add, iterateLaw, Law.expect_pure]
  | succ left ih =>
      have he : left + 1 + right = (left + right) + 1 := by omega
      simp only [he, iterateLaw, Law.expect_bind]
      apply congrArg (kernel a).expect
      funext b
      exact ih b

def unpackState {cfg : Config} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)} (r : ℕ) :
    Option (PackedState cfg stored input) → Option (State cfg stored input r)
  | none => none
  | some ⟨j, st⟩ => if h : j = r then some (h ▸ st) else none

theorem unpack_pack {cfg : Config} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    (r : ℕ) (state : Option (State cfg stored input r)) : unpackState r (packState r state) = state := by
  cases state <;> simp [unpackState, packState]

theorem packed_final_pure (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ)
    (state : Option (State cfg stored input cfg.earlyLevel)) :
    packedStep cfg hnum stored input ranks (packState cfg.earlyLevel state) =
      Law.pure (packState cfg.earlyLevel state) := by
  cases state <;> simp [packedStep, packState]

theorem finish_pack_final (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (state : Option (State cfg stored input cfg.earlyLevel)) :
    finishPacked (packState cfg.earlyLevel state) = packState cfg.earlyLevel state := by
  cases state <;> simp [finishPacked, packState]

theorem control_follow_full (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (root : State cfg stored input 0) (ranks : Fin n → ℕ)
    (fuel : ℕ) (hfuel : cfg.earlyLevel ≤ fuel) (f : Option (PackedState cfg stored input) → ℝ) :
    (Batched.controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue).expect
        (fun trace => f (followControls cfg hnum stored input ranks trace (some ⟨0, root⟩))) =
      (fixedPathStateLaw cfg hnum stored input root ranks cfg.earlyLevel).expect
        (fun state => f (packState cfg.earlyLevel state)) := by
  let kernel := packedStep cfg hnum stored input ranks
  let obs := fun state => f (finishPacked state)
  calc
    _ = (iterateLaw kernel fuel (some ⟨0, root⟩)).expect obs :=
      control_follow_equiv cfg hnum stored input hn ranks fuel 0 root f
    _ = (iterateLaw kernel cfg.earlyLevel (some ⟨0, root⟩)).expect
        (fun state => (iterateLaw kernel (fuel - cfg.earlyLevel) state).expect obs) := by
      have he : cfg.earlyLevel + (fuel - cfg.earlyLevel) = fuel := by omega
      simpa only [he] using iterateLaw_add kernel (some ⟨0, root⟩) cfg.earlyLevel (fuel - cfg.earlyLevel) obs
    _ = (fixedPathStateLaw cfg hnum stored input root ranks cfg.earlyLevel).expect (fun state =>
        (iterateLaw kernel (fuel - cfg.earlyLevel) (packState cfg.earlyLevel state)).expect obs) :=
      packed_iterate_fixed cfg hnum stored input root ranks cfg.earlyLevel le_rfl _
    _ = _ := by
      apply congrArg (fixedPathStateLaw cfg hnum stored input root ranks cfg.earlyLevel).expect
      funext state
      have hi := iterate_pure_point kernel (packState cfg.earlyLevel state)
        (packed_final_pure cfg hnum stored input ranks state) (fuel - cfg.earlyLevel) obs
      simpa only [obs, finish_pack_final] using hi

def replayEarly (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (trace : List (Batched.ControlEntry n cfg)) :
    Option (State cfg stored input cfg.earlyLevel) :=
  unpackState cfg.earlyLevel (followControls cfg hnum stored input ranks trace (some ⟨0, root⟩))

theorem control_replay_fixed (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (fuel : ℕ) (hfuel : cfg.earlyLevel ≤ fuel)
    (f : Option (State cfg stored input cfg.earlyLevel) → ℝ) :
    (Batched.controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue).expect
        (fun trace => f (replayEarly cfg hnum stored input root ranks trace)) =
      (fixedPathStateLaw cfg hnum stored input root ranks cfg.earlyLevel).expect f := by
  have h := control_follow_full cfg hnum stored input hn root ranks fuel hfuel
    (fun state => f (unpackState cfg.earlyLevel state))
  simpa only [replayEarly, unpack_pack] using h

theorem geometric_replay_fixed (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (hn : 0 < n)
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (fuel : ℕ) (hfuel : cfg.earlyLevel ≤ fuel)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (f : Option (State cfg stored input cfg.earlyLevel) → ℝ) :
    (Batched.geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue).expect
        (fun trace => f (replayEarly cfg hnum stored input root ranks (trace.map Batched.GeometricEntry.control))) =
      (fixedPathStateLaw cfg hnum stored input root ranks cfg.earlyLevel).expect f :=
  (Batched.geometricTrace_control cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue hs hp hsize hnum
    (fun trace => f (replayEarly cfg hnum stored input root ranks trace))).trans
      (control_replay_fixed cfg hnum stored input hn root ranks fuel hfuel f)

end

end StreamingReachability.Hopset.Following
