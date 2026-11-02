module

public import StreamingReachability.Hopset.PathMeans

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {r : ℕ}

def recordedCount (hnum : 0 < cfg.initialNumerator) (i : ℕ) (layers : List (Layer cfg stored input)) : ℕ :=
  (layers.map fun layer => if layer.level = i then (layer.pieces hnum).length else 0).sum

def HistoryPast : Option (State cfg stored input r) → Prop
  | none => True
  | some st => ∀ layer ∈ st.layers, layer.level < r

theorem recordedCount_zero (hnum : 0 < cfg.initialNumerator) (i : ℕ)
    (layers : List (Layer cfg stored input)) (hp : ∀ layer ∈ layers, layer.level < i) :
    recordedCount hnum i layers = 0 := by
  induction layers with
  | nil => rfl
  | cons layer layers ih =>
      have hne : layer.level ≠ i := by have h := hp layer (by simp); omega
      simp only [recordedCount, List.map_cons, List.sum_cons, hne, ↓reduceIte, Nat.zero_add]
      exact ih (fun l hl => hp l (List.mem_cons_of_mem _ hl))

theorem recordedCount_update (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (st : State cfg stored input r)
    (sample : (Fin n → Bool) × (Fin st.queue.toArray.size → Reference.Owners n cfg)) (i : ℕ) :
    recordedCount hnum i (st.update hnum he sample).layers =
      recordedCount hnum i st.layers + if r = i then (splitAll cfg r hnum st.paths).length else 0 := by
  simp only [State.update, recordedCount, List.map_append, List.sum_append,
    List.map_singleton, List.sum_singleton, Layer.pieces]

theorem pathStep_past (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (state : Option (State cfg stored input r)) (hp : HistoryPast state) :
    Early.Sampling.Holds (pathStep cfg ps hnum stored input r state) HistoryPast := by
  cases state with
  | none => exact Early.Sampling.holds_pure none _ trivial
  | some st =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : Batched.AllGood cfg stored input r st.queue
        · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte]
          refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
          intro sample _
          intro layer hl
          rcases List.mem_append.mp hl with hold | hnew
          · exact (hp layer hold).trans (Nat.lt_succ_self _)
          · have heq := List.mem_singleton.mp hnew
            subst layer
            exact Nat.lt_succ_self _
        · simpa only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte] using
            Early.Sampling.holds_pure (none : Option (State cfg stored input (r + 1))) HistoryPast trivial
      · simpa only [pathStep, he, ↓reduceDIte] using
          Early.Sampling.holds_pure (none : Option (State cfg stored input (r + 1))) HistoryPast trivial

theorem pathStateLaw_past (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (root : State cfg stored input 0) (hroot : HistoryPast (some root)) (r : ℕ) :
    Early.Sampling.Holds (pathStateLaw cfg ps hnum stored input root r) HistoryPast := by
  induction r with
  | zero => exact Early.Sampling.holds_pure (some root) _ hroot
  | succ r ih =>
      exact Reference.holds_bind_on _ _ HistoryPast HistoryPast ih
        (fun state hp => pathStep_past ps hnum state hp)

theorem recorded_step_old (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (i : ℕ) (hi : i < r) (state : Option (State cfg stored input r)) :
    (pathStep cfg ps hnum stored input r state).expect
        (liftCount (fun st => recordedCount hnum i st.layers)) ≤
      liftCount (fun st => recordedCount hnum i st.layers) state := by
  have hne : r ≠ i := by omega
  cases state with
  | none => simp [pathStep, liftCount]
  | some st =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : Batched.AllGood cfg stored input r st.queue
        · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_map, liftCount,
            recordedCount_update, hne, Nat.add_zero, Law.expect_const, le_refl]
        · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_pure, liftCount]
          exact Nat.cast_nonneg _
      · simp only [pathStep, he, ↓reduceDIte, Law.expect_pure, liftCount]
        exact Nat.cast_nonneg _

theorem recorded_step_new (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (state : Option (State cfg stored input r)) (hp : HistoryPast state) :
    (pathStep cfg ps hnum stored input r state).expect
        (liftCount (fun st => recordedCount hnum r st.layers)) ≤
      liftCount (State.primeCount hnum) state := by
  cases state with
  | none => simp [pathStep, liftCount]
  | some st =>
      have hzero := recordedCount_zero hnum r st.layers hp
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : Batched.AllGood cfg stored input r st.queue
        · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_map, liftCount,
            recordedCount_update, hzero, Nat.zero_add, Law.expect_const, State.primeCount, le_refl]
        · simp only [pathStep, he, hg, ↓reduceDIte, ↓reduceIte, Law.expect_pure, liftCount,
            State.primeCount, Nat.cast_zero, le_refl]
      · simp only [pathStep, he, ↓reduceDIte, Law.expect_pure, liftCount]
        exact Nat.cast_nonneg _

theorem recorded_mean_le (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (root : State cfg stored input 0) (hroot : HistoryPast (some root)) (horizon : ℕ) :
    ∀ i < horizon,
      (pathStateLaw cfg ps hnum stored input root horizon).expect
          (liftCount (fun st => recordedCount hnum i st.layers)) ≤
        meanZ cfg ps hnum stored input root i := by
  induction horizon with
  | zero => intro i hi; omega
  | succ horizon ih =>
      intro i hi
      by_cases hold : i < horizon
      · calc
          _ = (pathStateLaw cfg ps hnum stored input root horizon).expect (fun state =>
              (pathStep cfg ps hnum stored input horizon state).expect
                (liftCount (fun st => recordedCount hnum i st.layers))) := by
            rw [pathStateLaw, Law.expect_bind]
          _ ≤ (pathStateLaw cfg ps hnum stored input root horizon).expect
              (liftCount (fun st => recordedCount hnum i st.layers)) :=
            Law.expect_mono _ (recorded_step_old ps hnum i hold)
          _ ≤ _ := ih i hold
      · have he : i = horizon := by omega
        subst i
        rw [pathStateLaw, Law.expect_bind]
        apply Early.Sampling.expect_mono_on
        refine Early.Sampling.holds_mono (pathStateLaw_past ps hnum root hroot horizon) ?_
        intro state hp
        exact recorded_step_new ps hnum state hp

def observedCount (hnum : 0 < cfg.initialNumerator) (i : ℕ) : Option (State cfg stored input r) → ℕ
  | none => 0
  | some st => if i < r then recordedCount hnum i st.layers else if i = r then st.primeCount hnum else 0

theorem observed_mean_le (ps : List Rate) (hnum : 0 < cfg.initialNumerator)
    (root : State cfg stored input 0) (hroot : HistoryPast (some root)) (horizon i : ℕ) (hi : i ≤ horizon) :
    (pathStateLaw cfg ps hnum stored input root horizon).expect (fun state => (observedCount hnum i state : ℝ)) ≤
      meanZ cfg ps hnum stored input root i := by
  by_cases hold : i < horizon
  · have hf : (fun state : Option (State cfg stored input horizon) => (observedCount hnum i state : ℝ)) =
        liftCount (fun st => recordedCount hnum i st.layers) := by
      funext state
      cases state <;> simp [observedCount, liftCount, hold]
    rw [hf]
    exact recorded_mean_le ps hnum root hroot horizon i hold
  · have he : i = horizon := by omega
    subst i
    have hf : (fun state : Option (State cfg stored input horizon) => (observedCount hnum horizon state : ℝ)) =
        liftCount (State.primeCount hnum) := by
      funext state
      cases state <;> simp [observedCount, liftCount]
    rw [hf]
    exact le_rfl

end

end StreamingReachability.Hopset.Following
