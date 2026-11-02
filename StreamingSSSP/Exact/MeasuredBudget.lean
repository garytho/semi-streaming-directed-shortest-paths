module

public import StreamingSSSP.Exact.MeasuredProgram
public import StreamingSSSP.Hopset.EnvelopeCosts

@[expose] public section

namespace StreamingSSSP.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram
open Hopset.Measured

variable {n : ℕ} {A : Type*}

structure Budget where
  passes : ℕ
  calls : ℕ
  draws : ℕ

def solveBudget (n accuracy confidence : ℕ) (bounds : Approx.Bounds) : Budget :=
  let count := executionCount n confidence bounds.minWeight bounds.maximum
  let calls := Approx.Measured.solveCallLimit n confidence bounds.minWeight bounds.maximum
  ⟨1 + calls * passLimit n (Parameters.blockSize n)
      (8 * Parameters.queryUnit n accuracy (Parameters.blockSize n)) (recordLimit n accuracy count),
    calls, count * drawLimit n accuracy (Parameters.blockSize n)⟩

def requestBudget (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n)) :
    Request n → Budget
  | .base descriptor _ denominator _ =>
      solveBudget n (safeAccuracy denominator) confidence
        (Approx.scanAuxiliary (baseView descriptor) input (baseAuxiliary descriptor source (n ^ exponent)))
  | .level descriptor denominator _ =>
      solveBudget (n + 1) (safeAccuracy denominator) confidence
        (Approx.scanAuxiliary (levelView descriptor) input (levelAuxiliary descriptor source (n ^ exponent)))
  | .parents .. => ⟨1, 0, 0⟩

structure WorkFits (budget : Budget) (out : Work n A) : Prop where
  passes_le : out.passes ≤ budget.passes
  calls_le : out.calls.length ≤ budget.calls
  draws_le : out.draws.length ≤ budget.draws

theorem handler_budget (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (request : Request n) :
    Early.Sampling.Holds (handler source exponent confidence input request)
      (WorkFits (requestBudget source exponent confidence input request)) := by
  cases request with
  | base descriptor querySource denominator clock =>
      have h := Approx.Measured.solve_resources (baseView descriptor) input
        (baseAuxiliary descriptor source (n ^ exponent)) (sourcePositive querySource)
        (safeAccuracy denominator) (Parameters.blockSize n) confidence (safeAccuracy_pos denominator) querySource
        (base_input_positive descriptor source (n ^ exponent) input)
      refine Early.Sampling.holds_map h (fun out => (fromBase out).map integerLabels) _ ?_
      intro out ho
      exact ⟨ho.passes_le, by simpa only [Work.map, fromBase, List.length_map, requestBudget, solveBudget] using ho.calls_le,
        ho.draws_le⟩
  | level descriptor denominator clock =>
      have h := Approx.Measured.solve_resources (levelView descriptor) input
        (levelAuxiliary descriptor source (n ^ exponent)) (Nat.succ_pos n)
        (safeAccuracy denominator) (Parameters.blockSize (n + 1)) confidence (safeAccuracy_pos denominator) (Fin.last n)
        (level_input_positive descriptor source (n ^ exponent) input)
      refine Early.Sampling.holds_map h (fun out => (fromLevel out).map integerLevelAnswer) _ ?_
      intro out ho
      exact ⟨ho.passes_le, by simpa only [Work.map, fromLevel, List.length_map, requestBudget, solveBudget] using ho.calls_le,
        ho.draws_le⟩
  | parents => exact Early.Sampling.holds_pure _ _ ⟨le_rfl, le_rfl, le_rfl⟩

def traceBudget (budget : Request n → Budget) (trace : List (Answered n)) : Budget :=
  ⟨(trace.map (fun entry => (budget entry.request).passes)).sum,
    (trace.map (fun entry => (budget entry.request).calls)).sum,
    (trace.map (fun entry => (budget entry.request).draws)).sum⟩

theorem execute_budget (handler : (request : Request n) → Law (Work n request.Reply))
    (budget : Request n → Budget)
    (hb : ∀ request, Early.Sampling.Holds (handler request) (WorkFits (budget request)))
    (program : Program n A) (cache : Cache n) :
    Early.Sampling.Holds (execute handler program cache)
      (fun out => WorkFits (traceBudget budget out.result.trace) out) := by
  induction program generalizing cache with
  | pure value => exact Early.Sampling.holds_pure _ _ ⟨le_rfl, le_rfl, le_rfl⟩
  | ask request next ih =>
      cases hr : cache.response request with
      | some answer =>
          simp only [execute, hr]
          refine Early.Sampling.holds_map (ih answer cache)
            (fun out => out.map (Outcome.prepend ⟨request, answer, false⟩)) _ ?_
          intro out ho
          refine ⟨?_, ?_, ?_⟩
          · exact ho.passes_le.trans (Nat.le_add_left _ _)
          · exact ho.calls_le.trans (Nat.le_add_left _ _)
          · exact ho.draws_le.trans (Nat.le_add_left _ _)
      | none =>
          simp only [execute, hr]
          refine Hopset.Reference.holds_bind_on _ _ _ _ (hb request) ?_
          intro first hf
          refine Early.Sampling.holds_map (ih first.result (cache.store request first.result))
            (fun last => first.then (last.map (Outcome.prepend ⟨request, first.result, true⟩))) _ ?_
          intro last hl
          exact ⟨Nat.add_le_add hf.passes_le hl.passes_le,
            by simpa only [Work.then, Work.map, List.length_append, traceBudget, Outcome.prepend,
              List.map_cons, List.sum_cons] using Nat.add_le_add hf.calls_le hl.calls_le,
            by simpa only [Work.then, Work.map, List.length_append, traceBudget, Outcome.prepend,
              List.map_cons, List.sum_cons] using Nat.add_le_add hf.draws_le hl.draws_le⟩

theorem trace_budget_bound (budget : Request n → Budget) (trace : List (Answered n)) (limit : Budget)
    (h : ∀ entry ∈ trace,
      (budget entry.request).passes ≤ limit.passes ∧
      (budget entry.request).calls ≤ limit.calls ∧
      (budget entry.request).draws ≤ limit.draws) :
    (traceBudget budget trace).passes ≤ trace.length * limit.passes ∧
      (traceBudget budget trace).calls ≤ trace.length * limit.calls ∧
      (traceBudget budget trace).draws ≤ trace.length * limit.draws := by
  have hp := List.sum_le_sum (l := trace)
    (f := fun entry => (budget entry.request).passes) (g := fun _ => limit.passes)
    (fun entry he => (h entry he).1)
  have hc := List.sum_le_sum (l := trace)
    (f := fun entry => (budget entry.request).calls) (g := fun _ => limit.calls)
    (fun entry he => (h entry he).2.1)
  have hd := List.sum_le_sum (l := trace)
    (f := fun entry => (budget entry.request).draws) (g := fun _ => limit.draws)
    (fun entry he => (h entry he).2.2)
  exact ⟨by simpa [traceBudget] using hp,
    by simpa [traceBudget] using hc, by simpa [traceBudget] using hd⟩

end StreamingSSSP.Exact.Implementation.Measured
