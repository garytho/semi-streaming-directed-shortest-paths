module

public import StreamingSSSP.Exact.UniformBudget
public import StreamingSSSP.Exact.DescriptorWords
public import StreamingSSSP.Hopset.WordCapacity

@[expose] public section

namespace StreamingSSSP.Exact.Implementation.Measured

open scoped Classical
open DescriptorProgram

variable {n : ℕ} {A : Type*}

def ReplyOrigin (handler : (request : Request n) → Law (Work n request.Reply)) (entry : Answered n) : Prop :=
  ∃ atom ∈ (handler entry.request).atoms, atom.1.result = entry.answer

def CallOrigin (handler : (request : Request n) → Law (Work n request.Reply))
    (trace : List (Answered n)) (call : Call n) : Prop :=
  ∃ entry ∈ trace, ∃ atom ∈ (handler entry.request).atoms,
    atom.1.result = entry.answer ∧ call ∈ atom.1.calls

structure Origins (handler : (request : Request n) → Law (Work n request.Reply))
    (out : Work n (Outcome n A)) : Prop where
  replies : ∀ entry ∈ out.result.trace, entry.fresh = true → ReplyOrigin handler entry
  calls : ∀ call ∈ out.calls, CallOrigin handler out.result.trace call

theorem execute_origins (handler : (request : Request n) → Law (Work n request.Reply))
    (program : Program n A) (cache : Cache n) :
    Early.Sampling.Holds (execute handler program cache) (Origins handler) := by
  induction program generalizing cache with
  | pure value => exact Early.Sampling.holds_pure _ _ ⟨by simp, by simp⟩
  | ask request next ih =>
      cases hr : cache.response request with
      | some answer =>
          simp only [execute, hr]
          refine Early.Sampling.holds_map (ih answer cache)
            (fun out => out.map (Outcome.prepend ⟨request, answer, false⟩)) _ ?_
          intro out ho
          refine ⟨?_, ?_⟩
          · intro entry he hf
            rcases List.mem_cons.mp he with rfl | he
            · cases hf
            · exact ho.replies entry he hf
          · intro call hc
            obtain ⟨entry, he, atom, ha, hanswer, hcall⟩ := ho.calls call hc
            exact ⟨entry, List.mem_cons_of_mem _ he, atom, ha, hanswer, hcall⟩
      | none =>
          simp only [execute, hr]
          have hs : Early.Sampling.Holds (handler request)
              (fun first => ∃ weight, (first, weight) ∈ (handler request).atoms) :=
            fun atom hatom => ⟨atom.2, hatom⟩
          refine Hopset.Reference.holds_bind_on _ _ _ _ hs ?_
          intro first hf
          refine Early.Sampling.holds_map (ih first.result (cache.store request first.result))
            (fun last => first.then (last.map (Outcome.prepend ⟨request, first.result, true⟩))) _ ?_
          intro last hl
          obtain ⟨weight, hw⟩ := hf
          refine ⟨?_, ?_⟩
          · intro entry he hfresh
            rcases List.mem_cons.mp he with rfl | he
            · exact ⟨(first, weight), hw, rfl⟩
            · exact hl.replies entry he hfresh
          · intro call hc
            rcases List.mem_append.mp hc with hc | hc
            · exact ⟨⟨request, first.result, true⟩, List.mem_cons_self, (first, weight), hw, rfl, hc⟩
            · obtain ⟨entry, he, atom, ha, hanswer, hcall⟩ := hl.calls call hc
              exact ⟨entry, List.mem_cons_of_mem _ he, atom, ha, hanswer, hcall⟩

def _root_.StreamingSSSP.Exact.Implementation.Cache.cells (cache : Cache n) : ℕ :=
  (n + 1) * cache.base.length + (n + 2) * cache.level.length

theorem _root_.StreamingSSSP.Exact.Implementation.Cache.store_count
    (cache : Cache n) (request : Request n) (answer : request.Reply) :
    (cache.store request answer).base.length + (cache.store request answer).level.length ≤
      cache.base.length + cache.level.length + 1 := by
  cases request <;> simp only [Cache.store, List.length_cons] <;> omega

theorem _root_.StreamingSSSP.Exact.Implementation.Run.cache_count
    {parent : ParentReply n} {program : Program n A} {cache final : Cache n}
    {result : A} {trace : List (Answered n)} (h : Run parent program cache result final trace) :
    final.base.length + final.level.length ≤ cache.base.length + cache.level.length + trace.length := by
  induction h with
  | pure => simp
  | hit present rest ih => simpa only [List.length_cons] using ih.trans (by omega)
  | @fresh request next cache final answer result trace absent parents rest ih =>
      have hs := Cache.store_count cache request answer
      simp only [List.length_cons]
      omega

theorem _root_.StreamingSSSP.Exact.Implementation.Run.root_cache_cells
    {parent : ParentReply n} {source : Fin n} {exponent : ℕ}
    {final : Cache n} {result : Result n} {trace : List (Answered n)}
    (h : Run parent (DescriptorProgram.exact source exponent) {} result final trace) :
    final.cells ≤ (n + 2) * trace.length := by
  have hc := h.cache_count
  simp only [Cache.base, Cache.level, List.length_nil, zero_add] at hc
  unfold Cache.cells
  nlinarith

theorem _root_.StreamingSSSP.Exact.Implementation.Run.data_words
    {source : Fin n} {exponent : ℕ} {cache final : Cache n} {result : Result n}
    {trace : List (Answered n)} (input : List (StoredEdges.Edge n))
    (h : Run (parentReplyOfEdges input) (DescriptorProgram.exact source exponent) cache result final trace) :
    ∀ entry ∈ trace, entry.request.DataBound ((2 * n) ^ (2000 * (exponent + 4))) := by
  let G := StoredEdges.graphOfEdges input
  have hw := exact_data_words (interpretReply G final.baseOracle final.levelOracle (parentReplyOfEdges input)) source exponent
  intro entry he
  apply hw entry.request
  unfold requests
  rw [h.replay_trace G (fun request => [request])]
  exact List.mem_flatMap.mpr ⟨entry, he, by simp⟩

end StreamingSSSP.Exact.Implementation.Measured
