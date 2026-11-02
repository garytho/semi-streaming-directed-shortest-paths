module

public import StreamingReachability.Hopset.StoppedTrace
public import StreamingReachability.Hopset.TraceRewards

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

inductive ValidTrace (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → List (Entry n) → Prop
  | done (r : ℕ) (queue : List (Finset (Fin n))) : ValidTrace cfg hn stored input rank 0 r queue []
  | stopped (fuel r : ℕ) (queue : List (Finset (Fin n)))
      (hg : ¬ AllGood cfg stored input r queue) :
      ValidTrace cfg hn stored input rank (fuel + 1) r queue []
  | next {fuel r : ℕ} {queue : List (Finset (Fin n))} {step : Step n} {tail : List (Entry n)}
      (hg : AllGood cfg stored input r queue)
      (hs : ∃ weight, (step, weight) ∈ (levelLaw cfg hn stored input rank r queue.toArray.toVector).atoms)
      (ht : ValidTrace cfg hn stored input rank fuel (r + 1) step.children tail) :
      ValidTrace cfg hn stored input rank (fuel + 1) r queue (⟨r, queue, step⟩ :: tail)

theorem traceLaw_valid (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) :
    Early.Sampling.Holds (traceLaw cfg hn stored input rank fuel r queue)
      (ValidTrace cfg hn stored input rank fuel r queue) := by
  induction fuel generalizing r queue with
  | zero => exact Early.Sampling.holds_pure _ _ (ValidTrace.done r queue)
  | succ fuel ih =>
      by_cases hg : AllGood cfg stored input r queue
      · simp only [traceLaw, hg, ↓reduceIte]
        refine Reference.holds_bind_on _ _ (fun step =>
          ∃ weight, (step, weight) ∈ (levelLaw cfg hn stored input rank r queue.toArray.toVector).atoms) _
          (by intro z hz; exact ⟨z.2, by simpa using hz⟩) ?_
        intro step hs
        refine Early.Sampling.holds_map (ih (r + 1) step.children) (⟨r, queue, step⟩ :: ·) _ ?_
        intro tail ht
        exact ValidTrace.next hg hs ht
      · simp only [traceLaw, hg, ↓reduceIte]
        exact Early.Sampling.holds_pure _ _ (ValidTrace.stopped fuel r queue hg)

namespace ValidTrace

variable {cfg : Config} {hn : 0 < n} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}
    {fuel r : ℕ} {queue : List (Finset (Fin n))} {trace : List (Entry n)}

theorem length_le (h : ValidTrace cfg hn stored input rank fuel r queue trace) : trace.length ≤ fuel := by
  induction h with
  | done => simp
  | stopped => simp
  | next hg hs ht ih => exact Nat.succ_le_succ ih

theorem levels_good (h : ValidTrace cfg hn stored input rank fuel r queue trace) :
    ∀ entry ∈ trace, r ≤ entry.level ∧ entry.level < r + fuel ∧
      AllGood cfg stored input entry.level entry.queue := by
  induction h with
  | done => simp
  | stopped => simp
  | @next fuel r queue step tail hg hs ht ih =>
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨le_rfl, by simp, hg⟩
      · have hb := ih entry he
        exact ⟨by omega, by omega, hb.2.2⟩

theorem short_has_bad (h : ValidTrace cfg hn stored input rank fuel r queue trace) :
    AllGood cfg stored input r queue → trace.length < fuel →
      0 < traceCost (badReward cfg stored input) trace := by
  induction h with
  | done => simp
  | stopped fuel r queue hnot => intro hg; exact False.elim (hnot hg)
  | @next fuel r queue step tail hg hs ht ih =>
      intro hgood hshort
      have hlen : tail.length < fuel := by simpa using hshort
      change 0 < badReward cfg stored input r queue step + traceCost (badReward cfg stored input) tail
      by_cases hnext : AllGood cfg stored input (r + 1) step.children
      · have hpos := ih hnext hlen
        omega
      · have hex : ∃ T ∈ step.children, ¬ Reference.BallsGood cfg stored input (r + 1) T := by
          by_contra h
          apply hnext
          intro T hT
          by_contra hb
          exact h ⟨T, hT, hb⟩
        obtain ⟨T, hT, hb⟩ := hex
        have hm : T ∈ step.children.filter (fun S =>
            decide (¬ Reference.BallsGood cfg stored input (r + 1) S)) :=
          List.mem_filter.mpr ⟨hT, by simpa only [decide_eq_true_eq] using hb⟩
        have hpos : 0 < badReward cfg stored input r queue step := by
          unfold badReward
          cases he : step.children.filter (fun S =>
              decide (¬ Reference.BallsGood cfg stored input (r + 1) S)) with
          | nil => simp only [he, List.not_mem_nil] at hm
          | cons S Ss => simp
        omega

end ValidTrace

def replay : State n → List (Entry n) → State n
  | state, [] => state
  | state, entry :: trace => replay (applyStep state entry.step) trace

def pendingQueue : List (Finset (Fin n)) → List (Entry n) → List (Finset (Fin n))
  | queue, [] => queue
  | _, entry :: trace => pendingQueue entry.step.children trace

theorem replay_records (state : State n) (trace : List (Entry n)) :
    (replay state trace).records = state.records + traceCost recordReward trace := by
  induction trace generalizing state with
  | nil => simp [replay, traceCost]
  | cons entry trace ih =>
      simp only [replay, ih, applyStep, traceCost, recordReward, List.map_cons, List.sum_cons]
      omega

theorem replay_blocks (state : State n) (trace : List (Entry n)) :
    volume (replay state trace).output.blocks =
      volume state.output.blocks + traceCost blockReward trace := by
  induction trace generalizing state with
  | nil => simp [replay, traceCost]
  | cons entry trace ih =>
      rw [replay, ih]
      simp only [applyStep, traceCost, blockReward, volume,
        List.map_append, List.sum_append, List.map_cons, List.sum_cons]
      omega

theorem replay_copies_mono (state : State n) (trace : List (Entry n)) :
    state.copies ≤ (replay state trace).copies := by
  induction trace generalizing state with
  | nil => exact le_rfl
  | cons entry trace ih =>
      change state.copies ≤ (replay (applyStep state entry.step) trace).copies
      exact (Nat.le_add_right state.copies (volume entry.step.children)).trans (ih (applyStep state entry.step))

theorem ValidTrace.copy_telescope {cfg : Config} {hn : 0 < n} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n} {fuel r : ℕ}
    {queue : List (Finset (Fin n))} {trace : List (Entry n)}
    (h : ValidTrace cfg hn stored input rank fuel r queue trace) (state : State n) :
    (replay state trace).copies + volume queue =
      state.copies + traceCost copyReward trace + volume (pendingQueue queue trace) := by
  induction h generalizing state with
  | done => simp [replay, traceCost, pendingQueue]
  | stopped => simp [replay, traceCost, pendingQueue]
  | @next fuel r queue step tail hg hs ht ih =>
      have htail := ih (applyStep state step)
      simp only [replay, pendingQueue, traceCost, List.map_cons, List.sum_cons,
        copyReward, applyStep] at *
      omega

end

end StreamingReachability.Hopset.Batched
