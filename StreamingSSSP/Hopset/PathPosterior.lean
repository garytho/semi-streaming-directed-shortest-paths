module

public import StreamingSSSP.Hopset.PathProcess

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ}

def someValue {A : Type*} (c : ℝ) (f : A → ℝ) : Option A → ℝ
  | none => c
  | some a => f a

def fixedPathStep (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (r : ℕ) (ranks : Fin n → ℕ) :
    Option (State cfg stored input r) → Law (Option (State cfg stored input (r + 1)))
  | none => Law.pure none
  | some st =>
      if he : r < cfg.earlyLevel then
        if Batched.AllGood cfg stored input r st.queue then
          (Law.family st.queue.toArray.size (fun _ => Reference.ownerLaw n cfg)).map
            (fun owners => some (st.update hnum he (fun v => decide (ranks v = r), owners)))
        else Law.pure none
      else Law.pure none

def fixedPathStateLaw (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) : (r : ℕ) → Law (Option (State cfg stored input r))
  | 0 => Law.pure (some root)
  | r + 1 => (fixedPathStateLaw cfg hnum stored input root ranks r).bind
      (fixedPathStep cfg hnum stored input r ranks)

theorem pathStep_posterior (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (r : ℕ)
    (hprefix : ∀ i < cfg.earlyLevel, i < ps.length ∧ ((ps.take i).map Rate.value).sum ≤ 1 / 2)
    (st : State cfg stored input r) (f : State cfg stored input (r + 1) → (Fin n → ℕ) → ℝ) (c : ℝ) :
    (RankPrefix.law ps r st.known).expect (fun ranks =>
        (fixedPathStep cfg hnum stored input r ranks (some st)).expect
          (someValue c (fun next => f next ranks))) =
      (pathStep cfg ps hnum stored input r (some st)).expect
        (someValue c (fun next => (RankPrefix.law ps (r + 1) next.known).expect (f next))) := by
  by_cases he : r < cfg.earlyLevel
  · by_cases hg : Batched.AllGood cfg stored input r st.queue
    · let ownersLaw := Law.family st.queue.toArray.size (fun _ => Reference.ownerLaw n cfg)
      let F := fun (coins : Fin n → Bool) (ranks : Fin n → ℕ) =>
        ownersLaw.expect (fun owners => f (st.update hnum he (coins, owners)) ranks)
      have ho := RankPrefix.next_observed ps r (hprefix r he).1 (hprefix r he).2 st.known F
      calc
        _ = (Law.family n (fun v => RankPrefix.currentLaw ps r (st.known v))).expect (fun coins =>
            (RankPrefix.law ps (r + 1) (fun v => RankPrefix.nextKnown r (st.known v) (coins v))).expect (F coins)) := by
          simpa only [fixedPathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_map, someValue, F, ownersLaw] using ho
        _ = (Law.family n (fun v => RankPrefix.currentLaw ps r (st.known v))).expect (fun coins =>
            ownersLaw.expect (fun owners =>
              (RankPrefix.law ps (r + 1) (fun v => RankPrefix.nextKnown r (st.known v) (coins v))).expect
                (fun ranks => f (st.update hnum he (coins, owners)) ranks))) := by
          apply congrArg (Law.family n (fun v => RankPrefix.currentLaw ps r (st.known v))).expect
          funext coins
          exact Law.expect_comm
            (RankPrefix.law ps (r + 1) (fun v => RankPrefix.nextKnown r (st.known v) (coins v))) ownersLaw
            (fun ranks owners => f (st.update hnum he (coins, owners)) ranks)
        _ = _ := by
          simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_map, currentDraw,
            Law.expect_bind, someValue]
          rfl
    · simp only [fixedPathStep, pathStep, he, hg, ↓reduceDIte, ↓reduceIte,
        Law.expect_pure, someValue, Law.expect_const]
  · simp only [fixedPathStep, pathStep, he, ↓reduceDIte, Law.expect_pure, someValue, Law.expect_const]

theorem pathState_posterior (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (root : State cfg stored input 0)
    (hprefix : ∀ i < cfg.earlyLevel, i < ps.length ∧ ((ps.take i).map Rate.value).sum ≤ 1 / 2)
    (r : ℕ) (f : State cfg stored input r → (Fin n → ℕ) → ℝ) (c : ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
        (fixedPathStateLaw cfg hnum stored input root ranks r).expect
          (someValue c (fun state => f state ranks))) =
      (pathStateLaw cfg ps hnum stored input root r).expect
        (someValue c (fun state => (RankPrefix.law ps r state.known).expect (f state))) := by
  induction r generalizing c with
  | zero =>
      have hknown : root.known = (fun _ => none) := by
        funext v
        cases h : root.known v with
        | none => rfl
        | some i => exact Fin.elim0 i
      simp only [fixedPathStateLaw, pathStateLaw, Law.expect_pure, someValue, hknown]
      exact (RankPrefix.zero_expect ps (f root)).symm
  | succ r ih =>
      let g := fun (st : State cfg stored input r) (ranks : Fin n → ℕ) =>
        (fixedPathStep cfg hnum stored input r ranks (some st)).expect
          (someValue c (fun next => f next ranks))
      have hflat (ranks : Fin n → ℕ) :
          (fixedPathStateLaw cfg hnum stored input root ranks r).expect (fun state =>
            (fixedPathStep cfg hnum stored input r ranks state).expect
              (someValue c (fun next => f next ranks))) =
          (fixedPathStateLaw cfg hnum stored input root ranks r).expect
            (someValue c (fun st => g st ranks)) := by
        apply congrArg (fixedPathStateLaw cfg hnum stored input root ranks r).expect
        funext state
        cases state <;> simp only [fixedPathStep, Law.expect_pure, someValue, g]
      calc
        _ = (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
            (fixedPathStateLaw cfg hnum stored input root ranks r).expect
              (someValue c (fun st => g st ranks))) := by
          simp only [fixedPathStateLaw, Law.expect_bind]
          apply congrArg (Law.family n (fun _ => Ranks.firstHit ps)).expect
          funext ranks
          exact hflat ranks
        _ = (pathStateLaw cfg ps hnum stored input root r).expect
            (someValue c (fun st => (RankPrefix.law ps r st.known).expect (g st))) := ih g c
        _ = (pathStateLaw cfg ps hnum stored input root r).expect (fun state =>
            (pathStep cfg ps hnum stored input r state).expect
              (someValue c (fun next => (RankPrefix.law ps (r + 1) next.known).expect (f next)))) := by
          apply congrArg (pathStateLaw cfg ps hnum stored input root r).expect
          funext state
          cases state with
          | none => simp only [someValue, pathStep, Law.expect_pure]
          | some st => exact pathStep_posterior cfg ps hnum stored input r hprefix st f c
        _ = _ := by rw [pathStateLaw, Law.expect_bind]

theorem pathState_equiv (cfg : Config) (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (root : State cfg stored input 0)
    (hprefix : ∀ i < cfg.earlyLevel, i < ps.length ∧ ((ps.take i).map Rate.value).sum ≤ 1 / 2)
    (r : ℕ) (f : Option (State cfg stored input r) → ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
        (fixedPathStateLaw cfg hnum stored input root ranks r).expect f) =
      (pathStateLaw cfg ps hnum stored input root r).expect f := by
  have h := pathState_posterior cfg ps hnum stored input root hprefix r (fun st _ => f (some st)) (f none)
  have hf : someValue (f none) (fun st => f (some st)) = f := by
    funext state
    cases state <;> rfl
  simpa only [Law.expect_const, hf] using h

end

end StreamingSSSP.Hopset.Following
