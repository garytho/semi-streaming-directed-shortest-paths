module

public import StreamingSSSP.Exact.QueryProgram
public import StreamingSSSP.Exact.Resources

@[expose] public section

namespace StreamingSSSP.Exact.DescriptorProgram

open StoredEdges

variable {n : ℕ}

@[simp] theorem vector_get_ofFn {α : Type*} (f : Fin n → α) :
    (Vector.ofFn f).get = f := by
  funext v
  simp

abbrev ParentReply (n : ℕ) :=
  Fin n → ℕ → Labels n → Vector (Option (Edge n)) n

/-- Graphs and the stream are interpreter parameters only. They are absent from
the request syntax, program state, and all runtime transition definitions. -/
def interpretReply (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n) :
    (request : Request n) → request.Reply
  | .base descriptor source denominator clock =>
      Vector.ofFn (baseCall (descriptor.graph G) source denominator clock)
  | .level descriptor denominator clock =>
      LevelAnswer.ofFn (levelCall (descriptor.graph G) none denominator clock)
  | .parents source weightBound distances => parentReply source weightBound distances

def observeQuery (G : Graph (Fin n)) : Request n → List (CombinedQuery (Fin n))
  | .base descriptor source denominator clock =>
      [Sum.inl ⟨descriptor.graph G, source, denominator, clock⟩]
  | .level descriptor denominator clock =>
      [Sum.inr ⟨descriptor.graph G, none, denominator, clock⟩]
  | .parents .. => []

def positiveCombinedQuery (q : CombinedQuery (Fin n)) : CombinedQuery (Fin n) :=
  q.map Query.positive Query.positive

def guardedOracle {U : Type*} [Fintype U] (cap : ℕ) (call : Oracle U) : Oracle U :=
  nonnegativeOracle (cappedOracle cap call)

theorem baseDescriptor_graph (G : Graph (Fin n)) (potential : Labels n) (denominator : ℕ) :
    (baseDescriptor potential denominator).graph G =
      affineGraph (positiveResidual G potential.get)
        (3 * Fintype.card (Fin n) * denominator) 1 := by
  simp only [baseDescriptor, BaseDescriptor.graph, positiveResidual, Fintype.card_fin]

theorem levelDescriptor_graph (G : Graph (Fin n)) (potential labels : Labels n)
    (slope width shift denominator : ℕ) :
    (levelDescriptor potential labels slope width shift denominator).graph G =
      affineGraph
        (levelGraph (positiveResidual G potential.get) labels.get slope width shift)
        (3 * Fintype.card (Option (Fin n)) * denominator) 1 := by
  simp only [levelDescriptor, LevelDescriptor.graph, positiveResidual,
    Fintype.card_fin, Fintype.card_option]

theorem baseQuery_run (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (potential : Labels n) (source : Fin n) (denominator clock cap : ℕ) :
    Program.run (interpretReply G baseCall levelCall parentReply)
      (baseQuery potential source denominator clock cap) =
        Vector.ofFn (guardedOracle cap baseCall
          (positiveResidual G potential.get) source denominator clock) := by
  simp only [baseQuery, Program.run, interpretReply, vector_get_ofFn]
  rw [baseDescriptor_graph]
  congr 1
  funext v
  simp only [guardedOracle, nonnegativeOracle, positiveAnswer, cappedOracle, Fintype.card_fin]

theorem levelQuery_run (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (potential labels : Labels n) (slope width shift denominator clock cap : ℕ) :
    Program.run (interpretReply G baseCall levelCall parentReply)
      (levelQuery potential labels slope width shift denominator clock cap) =
        LevelAnswer.ofFn (guardedOracle cap levelCall
          (levelGraph (positiveResidual G potential.get) labels.get slope width shift)
          none denominator clock) := by
  simp only [levelQuery, Program.run, interpretReply, LevelAnswer.at_ofFn]
  rw [levelDescriptor_graph]
  congr 1
  funext v
  simp only [guardedOracle, nonnegativeOracle, positiveAnswer, cappedOracle,
    Fintype.card_option, Fintype.card_fin]

theorem baseQuery_trace (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (potential : Labels n) (source : Fin n) (denominator clock cap : ℕ) :
    Program.trace (observeQuery G) (interpretReply G baseCall levelCall parentReply)
      (baseQuery potential source denominator clock cap) =
        [Sum.inl ((⟨positiveResidual G potential.get, source, denominator, clock⟩ :
          Query (Fin n)).positive)] := by
  simp only [baseQuery, Program.trace, observeQuery, List.append_nil]
  rw [baseDescriptor_graph]
  rfl

theorem levelQuery_trace (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (potential labels : Labels n) (slope width shift denominator clock cap : ℕ) :
    Program.trace (observeQuery G) (interpretReply G baseCall levelCall parentReply)
      (levelQuery potential labels slope width shift denominator clock cap) =
        [Sum.inr ((⟨levelGraph (positiveResidual G potential.get) labels.get slope width shift,
          none, denominator, clock⟩ : Query (Option (Fin n))).positive)] := by
  simp only [levelQuery, Program.trace, observeQuery, List.append_nil]
  rw [levelDescriptor_graph]
  rfl

theorem smoothRounds_run (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (potential : Labels n) (M cap offset rounds slope : ℕ) (labels : Labels n) :
    Program.run (interpretReply G baseCall levelCall parentReply)
      (smoothRounds potential M cap offset rounds slope labels) =
        Vector.ofFn
          (smoothFrom (offsetOracle offset (guardedOracle cap levelCall))
            (positiveResidual G potential.get) M rounds slope labels.get) := by
  induction rounds generalizing slope labels with
  | zero =>
      simp only [smoothRounds, Program.run, smoothFrom]
      ext i
      simp
      rfl
  | succ rounds ih =>
      simp only [smoothRounds, Program.run_bind, levelQuery_run]
      rw [ih]
      simp only [vector_get_ofFn, LevelAnswer.at_ofFn, smoothFrom, offsetOracle]

theorem smoothRounds_trace (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (potential : Labels n) (M cap offset rounds slope : ℕ) (labels : Labels n) :
    Program.trace (observeQuery G) (interpretReply G baseCall levelCall parentReply)
      (smoothRounds potential M cap offset rounds slope labels) =
        (levelTrace (offsetOracle offset (guardedOracle cap levelCall))
          (positiveResidual G potential.get) M rounds slope labels.get).map
          (fun q => Sum.inr ((Query.offset offset q).positive)) := by
  induction rounds generalizing slope labels with
  | zero => rfl
  | succ rounds ih =>
      simp only [smoothRounds, Program.trace_bind, levelQuery_trace, levelQuery_run]
      rw [ih]
      simp only [vector_get_ofFn, LevelAnswer.at_ofFn, levelTrace, offsetOracle,
        List.map_cons, List.singleton_append]
      rfl

theorem smoothing_run (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (source : Fin n) (potential : Labels n) (rounds cap offset : ℕ) :
    Program.run (interpretReply G baseCall levelCall parentReply)
      (smoothing source potential rounds cap offset) =
        Vector.ofFn (StreamingSSSP.Exact.smoothing
          (offsetOracle offset (guardedOracle cap baseCall))
          (offsetOracle offset (guardedOracle cap levelCall))
          (positiveResidual G potential.get) source rounds) := by
  simp only [smoothing, Program.run_bind, baseQuery_run, smoothRounds_run, vector_get_ofFn]
  rfl

theorem smoothing_trace (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (source : Fin n) (potential : Labels n) (rounds cap offset : ℕ) :
    Program.trace (observeQuery G) (interpretReply G baseCall levelCall parentReply)
      (smoothing source potential rounds cap offset) =
        (smoothingTrace
          (offsetOracle offset (guardedOracle cap baseCall))
          (offsetOracle offset (guardedOracle cap levelCall))
          (positiveResidual G potential.get) source rounds).map
          (fun q => positiveCombinedQuery (offsetQuery offset q)) := by
  simp only [smoothing, Program.trace_bind, baseQuery_trace, baseQuery_run,
    smoothRounds_trace, vector_get_ofFn]
  simp only [smoothingTrace, List.map_cons, List.map_map, List.singleton_append]
  rfl

theorem outerRounds_run (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (source : Fin n) (rounds cap iterations : ℕ) (potential : Labels n) :
    Program.run (interpretReply G baseCall levelCall parentReply)
      (outerRounds source rounds cap iterations potential) =
        Vector.ofFn (outerFrom (guardedOracle cap baseCall) (guardedOracle cap levelCall)
          G source rounds iterations potential.get) := by
  induction iterations generalizing potential with
  | zero =>
      simp only [outerRounds, Program.run, outerFrom]
      ext i
      simp
      rfl
  | succ iterations ih =>
      simp only [outerRounds, Program.run_bind, smoothing_run]
      rw [ih]
      simp only [updatePotential, vector_get_ofFn, outerFrom]
      rfl

theorem outerRounds_trace (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (source : Fin n) (rounds cap iterations : ℕ) (potential : Labels n) :
    Program.trace (observeQuery G) (interpretReply G baseCall levelCall parentReply)
      (outerRounds source rounds cap iterations potential) =
        (outerTrace (guardedOracle cap baseCall) (guardedOracle cap levelCall)
          G source rounds iterations potential.get).map positiveCombinedQuery := by
  induction iterations generalizing potential with
  | zero => rfl
  | succ iterations ih =>
      simp only [outerRounds, Program.trace_bind, smoothing_trace, smoothing_run]
      rw [ih]
      simp only [updatePotential, vector_get_ofFn, outerTrace, List.map_append, List.map_map]
      rfl

theorem estimates_run (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (source : Fin n) (exponent : ℕ) :
    Program.run (interpretReply G baseCall levelCall parentReply) (estimates source exponent) =
      Vector.ofFn (exactDistances
        (guardedOracle (replyCap (inputBits n exponent)) baseCall)
        (guardedOracle (replyCap (inputBits n exponent)) levelCall)
        G source (inputBits n exponent)) := by
  simp only [estimates, outerRounds_run, vector_get_ofFn]
  rfl

theorem estimates_trace (G : Graph (Fin n)) (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (parentReply : ParentReply n)
    (source : Fin n) (exponent : ℕ) :
    Program.trace (observeQuery G) (interpretReply G baseCall levelCall parentReply)
      (estimates source exponent) =
        (outerTrace
          (guardedOracle (replyCap (inputBits n exponent)) baseCall)
          (guardedOracle (replyCap (inputBits n exponent)) levelCall)
          G source (smoothingRounds (inputBits n exponent)) (inputBits n exponent + 1)
          (fun _ => 0)).map positiveCombinedQuery := by
  simp only [estimates, outerRounds_trace, vector_get_ofFn]

/-- This handler is the interpretation of the final scan, not runtime input
stored by the descriptor program. `ParentPass.run` is the proved one-pass fold. -/
def parentReplyOfEdges (edges : List (Edge n)) : ParentReply n :=
  fun source weightBound distances =>
    Vector.ofFn (ParentPass.run source weightBound distances.get edges)

theorem transformedEstimates_eq (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ) :
    Program.run
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges))
      (estimates source exponent) =
        Vector.ofFn (transformedEstimates baseCall levelCall edges source exponent) := by
  rw [estimates_run]
  rfl

/-- Unconditional implementation equivalence, including failed/oversized replies.
The interpreter alone receives the input graph and parent-scan stream. -/
theorem exact_eq (baseCall : Oracle (Fin n)) (levelCall : Oracle (Option (Fin n)))
    (edges : List (Edge n)) (source : Fin n) (exponent : ℕ) :
    Program.run
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges))
      (exact source exponent) = exactSSSP baseCall levelCall edges source exponent := by
  simp only [exact, Program.run_bind, transformedEstimates_eq, Program.run,
    interpretReply, parentReplyOfEdges, vector_get_ofFn]
  rfl

/-- The physical positive-integer oracle trace is exactly the existing actual
trace, with its positive wrapper reified as a descriptor constructor. -/
theorem exact_trace_eq (baseCall : Oracle (Fin n)) (levelCall : Oracle (Option (Fin n)))
    (edges : List (Edge n)) (source : Fin n) (exponent : ℕ) :
    Program.trace
      (observeQuery (preprocess (graphOfEdges edges) source (n ^ exponent)))
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges))
      (exact source exponent) =
        (exactSSSPTrace baseCall levelCall edges source exponent).map positiveCombinedQuery := by
  simp only [exact, Program.trace_bind, estimates_trace, Program.trace, observeQuery,
    List.append_nil]
  rfl

def PhysicalAccurate (baseCall : Oracle (Fin n)) (levelCall : Oracle (Option (Fin n)))
    (q : CombinedQuery (Fin n)) : Prop :=
  q.elim (fun q => q.Accurate baseCall) (fun q => q.Accurate levelCall)

@[simp] theorem physicalAccurate_positive (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (q : CombinedQuery (Fin n)) :
    PhysicalAccurate baseCall levelCall (positiveCombinedQuery q) ↔
      PositiveAccurate baseCall levelCall q := by
  cases q <;> rfl

@[simp] theorem queryClock_positive (q : CombinedQuery (Fin n)) :
    queryClock (positiveCombinedQuery q) = queryClock q := by
  cases q <;> rfl

theorem exact_correct (baseCall : Oracle (Fin n)) (levelCall : Oracle (Option (Fin n)))
    (edges : List (Edge n)) (source : Fin n) (exponent : ℕ)
    (hW : ∀ e ∈ edges, e.weight ≤ n ^ exponent)
    (hs : ∀ q ∈ Program.trace
      (observeQuery (preprocess (graphOfEdges edges) source (n ^ exponent)))
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges)) (exact source exponent),
      PhysicalAccurate baseCall levelCall q) :
    let result := Program.run
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges)) (exact source exponent)
    result.distances = (graphOfEdges edges).dist source ∧
      (ParentPass.graph result.parents).dist source = (graphOfEdges edges).dist source ∧
      WellFounded (fun u v => ∃ e, result.parents v = some e ∧ e.source = u) := by
  have hsuccess : ∀ q ∈ exactSSSPTrace baseCall levelCall edges source exponent,
      PositiveAccurate baseCall levelCall q := by
    intro q hq
    have hh := hs (positiveCombinedQuery q) (by
      rw [exact_trace_eq]
      exact List.mem_map.mpr ⟨q, hq, rfl⟩)
    exact (physicalAccurate_positive _ _ q).mp hh
  simpa only [exact_eq] using exactSSSP_correct baseCall levelCall edges source exponent hW hsuccess

theorem exact_call_count (baseCall : Oracle (Fin n)) (levelCall : Oracle (Option (Fin n)))
    (edges : List (Edge n)) (source : Fin n) (exponent : ℕ) :
    (Program.trace
      (observeQuery (preprocess (graphOfEdges edges) source (n ^ exponent)))
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges)) (exact source exponent)).length ≤
      2308 * (exponent + 4) ^ 2 * (n.log2 + 1) ^ 2 := by
  rw [exact_trace_eq, List.length_map]
  exact exactSSSP_call_count baseCall levelCall edges source exponent

theorem exact_fresh_clocks (baseCall : Oracle (Fin n)) (levelCall : Oracle (Option (Fin n)))
    (edges : List (Edge n)) (source : Fin n) (exponent : ℕ) :
    ((Program.trace
      (observeQuery (preprocess (graphOfEdges edges) source (n ^ exponent)))
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges)) (exact source exponent)).map queryClock).Nodup := by
  rw [exact_trace_eq, List.map_map]
  simpa only [Function.comp_def, queryClock_positive] using
    exactSSSP_fresh_clocks baseCall levelCall edges source exponent

def PhysicalBounds (denominator weight : ℕ) (q : CombinedQuery (Fin n)) : Prop :=
  q.elim
    (fun q => q.denominator ≤ denominator ∧ WeightsBounded q.graph weight ∧
      ∀ u v (w : ℕ), q.graph u v = (w : Distance) → 0 < w)
    (fun q => q.denominator ≤ denominator ∧ WeightsBounded q.graph weight ∧
      ∀ u v (w : ℕ), q.graph u v = (w : Distance) → 0 < w)

theorem exact_queries_bounded (baseCall : Oracle (Fin n))
    (levelCall : Oracle (Option (Fin n))) (edges : List (Edge n))
    (source : Fin n) (exponent : ℕ)
    (hW : ∀ e ∈ edges, e.weight ≤ n ^ exponent) :
    ∀ q ∈ Program.trace
      (observeQuery (preprocess (graphOfEdges edges) source (n ^ exponent)))
      (interpretReply (preprocess (graphOfEdges edges) source (n ^ exponent))
        baseCall levelCall (parentReplyOfEdges edges)) (exact source exponent),
      PhysicalBounds (20000000 * (exponent + 4) * (n.log2 + 1))
        ((2 * n) ^ (2000 * (exponent + 4))) q := by
  intro q hq
  rw [exact_trace_eq] at hq
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hq
  have hb := exactSSSP_query_bounds baseCall levelCall edges source exponent hW old hold
  have hp := exactSSSP_queries_positive baseCall levelCall edges source exponent old hold
  cases old <;> exact ⟨hb.1, hb.2, hp⟩

end StreamingSSSP.Exact.DescriptorProgram
