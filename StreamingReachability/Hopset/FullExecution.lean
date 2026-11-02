module

public import StreamingReachability.Hopset.FullSemantics
public import StreamingReachability.Hopset.DeferredControl

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n : ℕ}

theorem FrameValid.currentChoices {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n} {r ns : ℕ}
    {sets : Vector (Finset (Fin n)) ns} {frame : Frame n cfg ns}
    (valid : FrameValid cfg stored input rank r sets frame) (he : r < cfg.earlyLevel) :
    currentChoices cfg sets (fun v => decide (rank.get v = r))
      (fun i => (frame.choices i).owners) = frame.choices := by
  rw [currentChoices_decide]
  funext i
  have hp := valid.earlyPivots he i
  cases hc : frame.choices i with
  | mk pivots owners =>
      change Reference.Choice.mk (CopyHistory.pivots (sets.get i) r (fun v => rank.get v)) owners = _
      exact congrArg (fun P => Reference.Choice.mk P owners) (by simpa only [hc] using hp.symm)

/-- A proof-only view of the literal trace with canonical child queues. -/
inductive FullExecution (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → Type
  | done (r : ℕ) (queue : List (Finset (Fin n))) :
      FullExecution cfg stored input rank 0 r queue
  | next {fuel r : ℕ} {queue : List (Finset (Fin n))}
      (frame : Frame n cfg queue.toArray.size)
      (valid : FrameValid cfg stored input rank r queue.toArray.toVector frame)
      (rest : FullExecution cfg stored input rank fuel (r + 1)
        (geometricChildren cfg r stored input queue.toArray.toVector frame.choices)) :
      FullExecution cfg stored input rank (fuel + 1) r queue

namespace FullExecution

variable {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n}
    {fuel r : ℕ} {queue : List (Finset (Fin n))}

def entries : {fuel r : ℕ} → {queue : List (Finset (Fin n))} →
    FullExecution cfg stored input rank fuel r queue → List (GeometricEntry n cfg)
  | _, _, _, .done _ _ => []
  | _, r, queue, .next frame _ rest => ⟨r, queue, frame⟩ :: rest.entries

def castQueue {other : List (Finset (Fin n))} (h : queue = other)
    (run : FullExecution cfg stored input rank fuel r queue) :
    FullExecution cfg stored input rank fuel r other :=
  h ▸ run

theorem castQueue_entries {other : List (Finset (Fin n))} (h : queue = other)
    (run : FullExecution cfg stored input rank fuel r queue) :
    (run.castQueue h).entries = run.entries := by
  cases h
  rfl

theorem length (run : FullExecution cfg stored input rank fuel r queue) :
    run.entries.length = fuel := by
  induction run with
  | done => rfl
  | next frame valid rest ih => exact congrArg (· + 1) ih

theorem fullValid (run : FullExecution cfg stored input rank fuel r queue) :
    FullValid cfg stored input rank fuel r queue run.entries := by
  induction run with
  | done r queue => exact FullValid.done r queue
  | next frame valid rest ih =>
      exact FullValid.next valid (by simpa only [valid.children] using ih)

theorem head_good {frame : Frame n cfg queue.toArray.size}
    {valid : FrameValid cfg stored input rank r queue.toArray.toVector frame}
    {rest : FullExecution cfg stored input rank fuel (r + 1)
      (geometricChildren cfg r stored input queue.toArray.toVector frame.choices)}
    (hg : TraceGood cfg stored input (FullExecution.next frame valid rest).entries) :
    AllGood cfg stored input r queue :=
  hg _ List.mem_cons_self

theorem tail_good {frame : Frame n cfg queue.toArray.size}
    {valid : FrameValid cfg stored input rank r queue.toArray.toVector frame}
    {rest : FullExecution cfg stored input rank fuel (r + 1)
      (geometricChildren cfg r stored input queue.toArray.toVector frame.choices)}
    (hg : TraceGood cfg stored input (FullExecution.next frame valid rest).entries) :
    TraceGood cfg stored input rest.entries :=
  fun entry he => hg entry (List.mem_cons_of_mem _ he)

end FullExecution

theorem FullValid.execution {cfg : Config} {stored : Implicit.Representation n}
    {input : List (StoredEdges.Edge n)} {rank : Vector ℕ n} {fuel r : ℕ}
    {queue : List (Finset (Fin n))} {trace : List (GeometricEntry n cfg)}
    (h : FullValid cfg stored input rank fuel r queue trace) :
    ∃ run : FullExecution cfg stored input rank fuel r queue, run.entries = trace := by
  induction h with
  | done r queue => exact ⟨.done r queue, rfl⟩
  | next valid rest ih =>
      obtain ⟨run, hrun⟩ := ih
      refine ⟨.next _ valid (run.castQueue valid.children), ?_⟩
      simp only [FullExecution.entries, FullExecution.castQueue_entries, hrun]

end

end StreamingReachability.Hopset.Batched
