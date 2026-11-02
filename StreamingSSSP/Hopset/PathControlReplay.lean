module

public import StreamingSSSP.Hopset.PathPosterior

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

abbrev PackedState (cfg : Config) (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :=
  Sigma (State cfg stored input)

def packState {cfg : Config} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)} (r : ℕ) :
    Option (State cfg stored input r) → Option (PackedState cfg stored input) :=
  Option.map (fun st => ⟨r, st⟩)

def packedStep (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) :
    Option (PackedState cfg stored input) → Law (Option (PackedState cfg stored input))
  | none => Law.pure none
  | some ⟨r, st⟩ =>
      if he : r < cfg.earlyLevel then
        if Batched.AllGood cfg stored input r st.queue then
          (Law.family st.queue.toArray.size (fun _ => Reference.ownerLaw n cfg)).map
            (fun owners => some ⟨r + 1, st.update hnum he (fun v => decide (ranks v = r), owners)⟩)
        else Law.pure none
      else Law.pure (some ⟨r, st⟩)

def iterateLaw {A : Type*} (kernel : A → Law A) : ℕ → A → Law A
  | 0, a => Law.pure a
  | fuel + 1, a => (kernel a).bind (iterateLaw kernel fuel)

theorem iterateLaw_forward {A : Type*} (kernel : A → Law A) (fuel : ℕ) (a : A) (f : A → ℝ) :
    (iterateLaw kernel (fuel + 1) a).expect f =
      (iterateLaw kernel fuel a).expect (fun b => (kernel b).expect f) := by
  induction fuel generalizing a with
  | zero => simp only [iterateLaw, Law.expect_bind, Law.expect_pure]
  | succ fuel ih =>
      simp only [iterateLaw, Law.expect_bind]
      apply congrArg (kernel a).expect
      funext b
      simpa only [iterateLaw, Law.expect_bind] using ih b

theorem packedStep_early (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ)
    (r : ℕ) (he : r < cfg.earlyLevel) (state : Option (State cfg stored input r))
    (f : Option (PackedState cfg stored input) → ℝ) :
    (packedStep cfg hnum stored input ranks (packState r state)).expect f =
      (fixedPathStep cfg hnum stored input r ranks state).expect (fun next => f (packState (r + 1) next)) := by
  cases state with
  | none => rfl
  | some st =>
      by_cases hg : Batched.AllGood cfg stored input r st.queue <;>
        simp only [packState, Option.map_some, Option.map_none, packedStep, fixedPathStep, he, hg, ↓reduceDIte,
          ↓reduceIte, Law.expect_map, Law.expect_pure]

theorem packed_iterate_fixed (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (r : ℕ) (hr : r ≤ cfg.earlyLevel)
    (f : Option (PackedState cfg stored input) → ℝ) :
    (iterateLaw (packedStep cfg hnum stored input ranks) r (some ⟨0, root⟩)).expect f =
      (fixedPathStateLaw cfg hnum stored input root ranks r).expect (fun state => f (packState r state)) := by
  induction r generalizing f with
  | zero => rfl
  | succ r ih =>
      rw [iterateLaw_forward]
      rw [ih (by omega) (fun state => (packedStep cfg hnum stored input ranks state).expect f)]
      simp_rw [packedStep_early cfg hnum stored input ranks r (by omega)]
      rw [fixedPathStateLaw, Law.expect_bind]

def finishPacked {cfg : Config} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)} :
    Option (PackedState cfg stored input) → Option (PackedState cfg stored input)
  | none => none
  | some ⟨r, st⟩ => if r < cfg.earlyLevel then none else some ⟨r, st⟩

def entryOwners {cfg : Config} (queue : List (Finset (Fin n))) (entry : Batched.ControlEntry n cfg)
    (h : entry.queue = queue) : Fin queue.toArray.size → Reference.Owners n cfg :=
  fun i => (entry.choices ⟨i.val, by simpa only [h] using i.isLt⟩).owners

def followControls (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) :
    List (Batched.ControlEntry n cfg) → Option (PackedState cfg stored input) → Option (PackedState cfg stored input)
  | [], state => finishPacked state
  | entry :: tail, state =>
      match state with
      | none => none
      | some ⟨r, st⟩ =>
          if he : r < cfg.earlyLevel then
            if entry.level = r then
              if hqueue : entry.queue = st.queue then
                followControls cfg hnum stored input ranks tail
                  (some ⟨r + 1, st.update hnum he
                    (fun v => decide (ranks v = r), entryOwners st.queue entry hqueue)⟩)
              else none
            else none
          else some ⟨r, st⟩

theorem followControls_done (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ)
    (trace : List (Batched.ControlEntry n cfg)) (r : ℕ) (st : State cfg stored input r) (hr : cfg.earlyLevel ≤ r) :
    followControls cfg hnum stored input ranks trace (some ⟨r, st⟩) = some ⟨r, st⟩ := by
  cases trace <;> simp only [followControls, finishPacked, show ¬ r < cfg.earlyLevel by omega, ↓reduceDIte, ↓reduceIte]

theorem followControls_head (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ)
    (r : ℕ) (st : State cfg stored input r) (he : r < cfg.earlyLevel)
    (owners : Fin st.queue.toArray.size → Reference.Owners n cfg) (tail : List (Batched.ControlEntry n cfg)) :
    let choices := Batched.currentChoices cfg st.queue.toArray.toVector (fun v => decide (ranks v = r)) owners
    followControls cfg hnum stored input ranks (⟨r, st.queue, choices⟩ :: tail) (some ⟨r, st⟩) =
      followControls cfg hnum stored input ranks tail
        (some ⟨r + 1, st.update hnum he (fun v => decide (ranks v = r), owners)⟩) := by
  simp only [followControls, he, ↓reduceDIte, ↓reduceIte]
  rfl

theorem iterate_pure_point {A : Type*} (kernel : A → Law A) (a : A) (h : kernel a = Law.pure a)
    (fuel : ℕ) (f : A → ℝ) : (iterateLaw kernel fuel a).expect f = f a := by
  induction fuel with
  | zero => simp only [iterateLaw, Law.expect_pure]
  | succ fuel ih => simpa only [iterateLaw, h, Law.expect_bind, Law.expect_pure] using ih

theorem control_follow_equiv (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (hn : 0 < n) (ranks : Fin n → ℕ)
    (fuel r : ℕ) (st : State cfg stored input r) (f : Option (PackedState cfg stored input) → ℝ) :
    (Batched.controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel r st.queue).expect
        (fun trace => f (followControls cfg hnum stored input ranks trace (some ⟨r, st⟩))) =
      (iterateLaw (packedStep cfg hnum stored input ranks) fuel (some ⟨r, st⟩)).expect (fun state => f (finishPacked state)) := by
  induction fuel generalizing r st with
  | zero => rfl
  | succ fuel ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : Batched.AllGood cfg stored input r st.queue
        · simp only [Batched.controlTraceLaw, hg, ↓reduceIte, Batched.choiceRowsLaw, he, Law.expect_bind,
            Law.expect_map, Vector.get_ofFn]
          have hchoices (owners : Fin st.queue.toArray.size → Reference.Owners n cfg) :
              (fun i => Reference.Choice.mk
                (CopyHistory.pivots (st.queue.toArray.toVector.get i) r ranks) (owners i)) =
              Batched.currentChoices cfg st.queue.toArray.toVector (fun v => decide (ranks v = r)) owners :=
            (Batched.currentChoices_decide cfg st.queue.toArray.toVector ranks r owners).symm
          simp_rw [hchoices, followControls_head cfg hnum stored input ranks r st he]
          simp only [iterateLaw, packedStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_bind, Law.expect_map]
          apply congrArg (Law.family st.queue.toArray.size (fun _ => Reference.ownerLaw n cfg)).expect
          funext owners
          exact ih (r + 1) (st.update hnum he (fun v => decide (ranks v = r), owners))
        · simp only [Batched.controlTraceLaw, hg, ↓reduceIte, Law.expect_pure, followControls, finishPacked, he]
          simp only [iterateLaw, packedStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_bind, Law.expect_pure]
          exact (iterate_pure_point (packedStep cfg hnum stored input ranks) none rfl fuel
            (fun state => f (finishPacked state))).symm
      · have hr : cfg.earlyLevel ≤ r := by omega
        simp_rw [followControls_done cfg hnum stored input ranks _ r st hr]
        rw [Law.expect_const]
        have hpure : packedStep cfg hnum stored input ranks (some ⟨r, st⟩) = Law.pure (some ⟨r, st⟩) := by
          simp only [packedStep, he, ↓reduceDIte]
        have hi := iterate_pure_point (packedStep cfg hnum stored input ranks) (some ⟨r, st⟩) hpure (fuel + 1)
          (fun state => f (finishPacked state))
        simpa only [finishPacked, he, ↓reduceIte] using hi.symm

end

end StreamingSSSP.Hopset.Following
