module

public import StreamingReachability.Exact.StreamingCache

@[expose] public section

namespace StreamingReachability.Exact.Implementation

open scoped Classical
open DescriptorProgram

variable {n : ℕ} {A : Type*}

def Cache.baseOracle (cache : Cache n) : Oracle (Fin n) :=
  fun _ _ _ clock v => ((tableGet clock cache.base).getD (Vector.replicate n 0)).get v

def Cache.levelOracle (cache : Cache n) : Oracle (Option (Fin n)) :=
  fun _ _ _ clock v => ((tableGet clock cache.level).getD ⟨Vector.replicate n 0, 0⟩).at v

theorem levelAnswer_of_at (answer : LevelAnswer n) : LevelAnswer.ofFn answer.at = answer := by
  cases answer with
  | mk vertices source =>
      change LevelAnswer.mk (Vector.ofFn (fun v => vertices.get v)) source = LevelAnswer.mk vertices source
      congr 1
      ext v
      simp
      rfl

theorem oracle_reply (G : Graph (Fin n)) (parent : ParentReply n) (cache : Cache n)
    (request : Request n) (answer : request.Reply) (h : Agrees parent cache request answer) :
    interpretReply G cache.baseOracle cache.levelOracle parent request = answer := by
  cases request with
  | base descriptor source denominator clock =>
      change Vector.ofFn (fun v => ((tableGet clock cache.base).getD (Vector.replicate n 0)).get v) = answer
      rw [h]
      ext v
      simp
      rfl
  | level descriptor denominator clock =>
      change LevelAnswer.ofFn ((tableGet clock cache.level).getD ⟨Vector.replicate n 0, 0⟩).at = answer
      rw [h]
      exact levelAnswer_of_at answer
  | parents source weightBound distances => exact h.symm

theorem Run.replay {parent : ParentReply n} {program : Program n A} {cache final : Cache n}
    {result : A} {trace : List (Answered n)} (h : Run parent program cache result final trace) (G : Graph (Fin n)) :
    Program.run (interpretReply G final.baseOracle final.levelOracle parent) program = result := by
  induction h with
  | pure => rfl
  | @hit request next cache final answer result trace present rest ih =>
      have ha := rest.extends.agrees parent request answer (response_agrees parent cache request answer present)
      simp only [Program.run, oracle_reply G parent final request answer ha]
      exact ih
  | @fresh request next cache final answer result trace absent parents rest ih =>
      have ha := rest.extends.agrees parent request answer (store_agrees parent cache request answer parents)
      simp only [Program.run, oracle_reply G parent final request answer ha]
      exact ih

theorem Run.replay_trace {parent : ParentReply n} {program : Program n A} {cache final : Cache n}
    {result : A} {trace : List (Answered n)} (h : Run parent program cache result final trace) (G : Graph (Fin n))
    {Event : Type*} (observe : Request n → List Event) :
    Program.trace observe (interpretReply G final.baseOracle final.levelOracle parent) program =
      trace.flatMap (fun entry => observe entry.request) := by
  induction h with
  | pure => rfl
  | @hit request next cache final answer result trace present rest ih =>
      have ha := rest.extends.agrees parent request answer (response_agrees parent cache request answer present)
      simp only [Program.trace, oracle_reply G parent final request answer ha, List.flatMap_cons]
      exact congrArg (observe request ++ ·) ih
  | @fresh request next cache final answer result trace absent parents rest ih =>
      have ha := rest.extends.agrees parent request answer (store_agrees parent cache request answer parents)
      simp only [Program.trace, oracle_reply G parent final request answer ha, List.flatMap_cons]
      exact congrArg (observe request ++ ·) ih

def traceClocks (trace : List (Answered n)) : List ℕ :=
  trace.flatMap (fun entry => entry.request.approxClocks)

theorem observe_clocks (G : Graph (Fin n)) (request : Request n) :
    (observeQuery G request).map queryClock = request.approxClocks := by
  cases request <;> rfl

theorem Run.exact_clocks {parent : ParentReply n} {source : Fin n} {exponent : ℕ}
    {cache final : Cache n} {result : Result n} {trace : List (Answered n)}
    (h : Run parent (DescriptorProgram.exact source exponent) cache result final trace) (G : Graph (Fin n)) :
    traceClocks trace =
      outerClockList (smoothingRounds (inputBits n exponent)) (inputBits n exponent + 1) := by
  change trace.flatMap (fun entry => entry.request.approxClocks) = _
  rw [← h.replay_trace G Request.approxClocks]
  exact DescriptorProgram.exact_clocks _ _ _

theorem Run.exact_fresh {source : Fin n} {exponent : ℕ}
    {cache final : Cache n} {result : Result n} {trace : List (Answered n)}
    (input : List (StoredEdges.Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) cache result final trace) :
    (traceClocks trace).Nodup := by
  let G := preprocess (StoredEdges.graphOfEdges input) source (n ^ exponent)
  have hn := DescriptorProgram.exact_fresh_clocks final.baseOracle final.levelOracle input source exponent
  rw [h.replay_trace G (observeQuery G)] at hn
  have heq : (trace.flatMap (fun entry => observeQuery G entry.request)).map queryClock = traceClocks trace := by
    rw [List.map_flatMap]
    apply congrArg (fun f => trace.flatMap f)
    funext entry
    exact observe_clocks G entry.request
  rw [heq] at hn
  exact hn

end StreamingReachability.Exact.Implementation
