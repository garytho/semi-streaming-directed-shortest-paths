module

public import StreamingSSSP.Exact.StreamingReplay

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open DescriptorProgram

variable {n : ℕ} {A : Type*}

def Cache.keys (cache : Cache n) : List ℕ :=
  cache.base.map Prod.fst ++ cache.level.map Prod.fst

theorem tableGet_key {V : Type*} (clock : ℕ) (table : List (ℕ × V)) (value : V)
    (h : tableGet clock table = some value) : clock ∈ table.map Prod.fst := by
  induction table with
  | nil => cases h
  | cons entry table ih =>
      rcases entry with ⟨key, answer⟩
      by_cases hk : clock = key
      · simp [hk]
      · simp only [tableGet, hk, ↓reduceIte] at h
        exact List.mem_cons_of_mem key (ih h)

theorem response_key (cache : Cache n) (request : Request n) (answer : request.Reply)
    (h : cache.response request = some answer) :
    ∃ clock ∈ request.approxClocks, clock ∈ cache.keys := by
  cases request with
  | base descriptor source denominator clock =>
      exact ⟨clock, by simp [Request.approxClocks],
        List.mem_append.mpr (Or.inl (tableGet_key clock cache.base answer h))⟩
  | level descriptor denominator clock =>
      exact ⟨clock, by simp [Request.approxClocks],
        List.mem_append.mpr (Or.inr (tableGet_key clock cache.level answer h))⟩
  | parents => cases h

theorem store_keys (cache : Cache n) (request : Request n) (answer : request.Reply)
    (clock : ℕ) (h : clock ∈ (cache.store request answer).keys) :
    clock ∈ cache.keys ∨ clock ∈ request.approxClocks := by
  cases request <;>
    simp only [Cache.store, Cache.keys, Request.approxClocks, List.map_cons,
      List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil] at * <;> aesop

theorem Run.all_fresh {parent : ParentReply n} {program : Program n A} {cache final : Cache n}
    {result : A} {trace : List (Answered n)} (h : Run parent program cache result final trace)
    (hkeys : ∀ clock ∈ cache.keys, clock ∉ traceClocks trace)
    (hclocks : (traceClocks trace).Nodup) :
    ∀ entry ∈ trace, entry.fresh = true := by
  induction h with
  | pure => simp
  | @hit request next cache final answer result trace present rest ih =>
      obtain ⟨clock, hc, hk⟩ := response_key cache request answer present
      exact False.elim (hkeys clock hk (List.mem_append.mpr (Or.inl hc)))
  | @fresh request next cache final answer result trace absent parents rest ih =>
      change (request.approxClocks ++ traceClocks trace).Nodup at hclocks
      have hparts := List.nodup_append.mp hclocks
      have hnext : ∀ clock ∈ (cache.store request answer).keys, clock ∉ traceClocks trace := by
        intro clock hk ht
        rcases store_keys cache request answer clock hk with hk | hc
        · exact hkeys clock hk (List.mem_append.mpr (Or.inr ht))
        · exact hparts.2.2 clock hc clock ht rfl
      have hall := ih hnext hparts.2.1
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact hall entry he

theorem requestHandler_parents (source : Fin n) (exponent confidence : ℕ) (input : List (StoredEdges.Edge n))
    (request : Request n) :
    Early.Sampling.Holds (requestHandler source exponent confidence input request)
      (ParentCorrect (parentReplyOfEdges input) request) := by
  cases request with
  | base => intro _ _; trivial
  | level => intro _ _; trivial
  | parents scanSource weightBound distances =>
      exact Early.Sampling.holds_pure _ _ rfl

theorem Run.root_fresh {source : Fin n} {exponent : ℕ} {final : Cache n} {result : Result n}
    {trace : List (Answered n)} (input : List (StoredEdges.Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) {} result final trace) :
    ∀ entry ∈ trace, entry.fresh = true := by
  apply h.all_fresh
  · simp [Cache.keys]
  · exact h.exact_fresh input

def traceParents (trace : List (Answered n)) : List Unit :=
  trace.flatMap (fun entry => entry.request.parentScans)

theorem trace_length (trace : List (Answered n)) :
    trace.length = (traceClocks trace).length + (traceParents trace).length := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      have hc : entry.request.approxClocks.length + entry.request.parentScans.length = 1 := by
        cases entry.request <;> rfl
      simp only [traceClocks, traceParents, List.flatMap_cons, List.length_append,
        List.length_cons] at *
      omega

def callCap (n exponent : ℕ) : ℕ :=
  2308 * (exponent + 4) ^ 2 * (n.log2 + 1) ^ 2 + 1

theorem Run.exact_length {parent : ParentReply n} {source : Fin n} {exponent : ℕ}
    {cache final : Cache n} {result : Result n} {trace : List (Answered n)}
    (h : Run parent (DescriptorProgram.exact source exponent) cache result final trace) (G : Graph (Fin n)) :
    trace.length ≤ callCap n exponent := by
  have hclock : (traceClocks trace).length = oracleCallCount (inputBits n exponent) := by
    rw [h.exact_clocks G, outerClockList_length]
    rfl
  have hparent : (traceParents trace).length = 1 := by
    change (trace.flatMap (fun entry => entry.request.parentScans)).length = 1
    rw [← h.replay_trace G Request.parentScans, exact_one_parent_scan]
    rfl
  have hb : oracleCallCount (inputBits n exponent) ≤
      2308 * (exponent + 4) ^ 2 * (n.log2 + 1) ^ 2 := by
    have hh := oracleCallCount_bound (inputBits n exponent)
    have hp : 0 < inputBits n exponent := by unfold inputBits; positivity
    unfold inputBits at *
    nlinarith
  rw [trace_length, hclock, hparent]
  exact Nat.add_le_add_right hb 1

end StreamingSSSP.Exact.Implementation
