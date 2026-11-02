module

public import StreamingSSSP.Exact.StreamingOracle

@[expose] public section

namespace StreamingSSSP.Exact.Implementation

open scoped Classical
open DescriptorProgram

variable {n : ℕ} {A : Type*}

def tableGet {V : Type*} (clock : ℕ) : List (ℕ × V) → Option V
  | [] => none
  | (key, value) :: rest => if clock = key then some value else tableGet clock rest

structure Cache (n : ℕ) where
  base : List (ℕ × Labels n) := []
  level : List (ℕ × LevelAnswer n) := []

def Cache.response (cache : Cache n) : (request : Request n) → Option request.Reply
  | .base _ _ _ clock => tableGet clock cache.base
  | .level _ _ clock => tableGet clock cache.level
  | .parents .. => none

def Cache.store (cache : Cache n) : (request : Request n) → request.Reply → Cache n
  | .base _ _ _ clock, answer => { cache with base := (clock, answer) :: cache.base }
  | .level _ _ clock, answer => { cache with level := (clock, answer) :: cache.level }
  | .parents .., _ => cache

def Cache.Extends (new old : Cache n) : Prop :=
  (∀ clock answer, tableGet clock old.base = some answer → tableGet clock new.base = some answer) ∧
    (∀ clock answer, tableGet clock old.level = some answer → tableGet clock new.level = some answer)

theorem Cache.Extends.refl (cache : Cache n) : cache.Extends cache :=
  ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Cache.Extends.trans {new middle old : Cache n} (h : new.Extends middle) (g : middle.Extends old) :
    new.Extends old :=
  ⟨fun clock answer ha => h.1 clock answer (g.1 clock answer ha),
    fun clock answer ha => h.2 clock answer (g.2 clock answer ha)⟩

theorem tableGet_fresh {V : Type*} (table : List (ℕ × V)) (clock : ℕ) (answer : V)
    (hfresh : tableGet clock table = none) (key : ℕ) (value : V) (hold : tableGet key table = some value) :
    tableGet key ((clock, answer) :: table) = some value := by
  by_cases hk : key = clock
  · subst key
    rw [hfresh] at hold
    cases hold
  · simpa only [tableGet, hk, ↓reduceIte] using hold

theorem Cache.store_extends (cache : Cache n) (request : Request n) (answer : request.Reply)
    (hfresh : cache.response request = none) : (cache.store request answer).Extends cache := by
  cases request with
  | base descriptor source denominator clock =>
      exact ⟨tableGet_fresh cache.base clock answer hfresh, fun _ _ h => h⟩
  | level descriptor denominator clock =>
      exact ⟨fun _ _ h => h, tableGet_fresh cache.level clock answer hfresh⟩
  | parents => exact .refl cache

def ParentCorrect (parent : ParentReply n) : (request : Request n) → request.Reply → Prop
  | .parents source weightBound distances, answer => answer = parent source weightBound distances
  | _, _ => True

def Agrees (parent : ParentReply n) (cache : Cache n) : (request : Request n) → request.Reply → Prop
  | .base _ _ _ clock, answer => tableGet clock cache.base = some answer
  | .level _ _ clock, answer => tableGet clock cache.level = some answer
  | .parents source weightBound distances, answer => answer = parent source weightBound distances

theorem Cache.Extends.agrees {new old : Cache n} (h : new.Extends old) (parent : ParentReply n)
    (request : Request n) (answer : request.Reply) (ha : Agrees parent old request answer) :
    Agrees parent new request answer := by
  cases request with
  | base descriptor source denominator clock => exact h.1 clock answer ha
  | level descriptor denominator clock => exact h.2 clock answer ha
  | parents => exact ha

theorem response_agrees (parent : ParentReply n) (cache : Cache n) (request : Request n) (answer : request.Reply)
    (h : cache.response request = some answer) : Agrees parent cache request answer := by
  cases request with
  | base => exact h
  | level => exact h
  | parents => cases h

theorem store_agrees (parent : ParentReply n) (cache : Cache n) (request : Request n) (answer : request.Reply)
    (h : ParentCorrect parent request answer) : Agrees parent (cache.store request answer) request answer := by
  cases request with
  | base => simp only [Agrees, Cache.store, tableGet, ↓reduceIte]; rfl
  | level => simp only [Agrees, Cache.store, tableGet, ↓reduceIte]; rfl
  | parents => exact h

structure Answered (n : ℕ) where
  request : Request n
  answer : request.Reply
  fresh : Bool

structure Outcome (n : ℕ) (A : Type*) where
  result : A
  cache : Cache n
  trace : List (Answered n)

def Outcome.prepend (entry : Answered n) (out : Outcome n A) : Outcome n A :=
  { out with trace := entry :: out.trace }

noncomputable def execute (handler : (request : Request n) → Law request.Reply) :
    Program n A → Cache n → Law (Outcome n A)
  | .pure value, cache => Law.pure ⟨value, cache, []⟩
  | .ask request next, cache =>
      match cache.response request with
      | some answer =>
          (execute handler (next answer) cache).map (Outcome.prepend ⟨request, answer, false⟩)
      | none =>
          (handler request).bind fun answer =>
            (execute handler (next answer) (cache.store request answer)).map
              (Outcome.prepend ⟨request, answer, true⟩)

inductive Run (parent : ParentReply n) : Program n A → Cache n → A → Cache n → List (Answered n) → Prop
  | pure (value : A) (cache : Cache n) : Run parent (.pure value) cache value cache []
  | hit {request : Request n} {next : request.Reply → Program n A} {cache final : Cache n}
      {answer : request.Reply} {result : A} {trace : List (Answered n)}
      (present : cache.response request = some answer)
      (rest : Run parent (next answer) cache result final trace) :
      Run parent (.ask request next) cache result final (⟨request, answer, false⟩ :: trace)
  | fresh {request : Request n} {next : request.Reply → Program n A} {cache final : Cache n}
      {answer : request.Reply} {result : A} {trace : List (Answered n)}
      (absent : cache.response request = none) (parents : ParentCorrect parent request answer)
      (rest : Run parent (next answer) (cache.store request answer) result final trace) :
      Run parent (.ask request next) cache result final (⟨request, answer, true⟩ :: trace)

theorem execute_run (handler : (request : Request n) → Law request.Reply) (parent : ParentReply n)
    (hparent : ∀ request, Early.Sampling.Holds (handler request) (ParentCorrect parent request))
    (program : Program n A) (cache : Cache n) :
    Early.Sampling.Holds (execute handler program cache)
      (fun out => Run parent program cache out.result out.cache out.trace) := by
  induction program generalizing cache with
  | pure value => exact Early.Sampling.holds_pure _ _ (.pure value cache)
  | ask request next ih =>
      cases hr : cache.response request with
      | some answer =>
          simp only [execute, hr]
          refine Early.Sampling.holds_map (ih answer cache) (Outcome.prepend ⟨request, answer, false⟩) _ ?_
          intro out ho
          exact .hit hr ho
      | none =>
          simp only [execute, hr]
          refine Hopset.Reference.holds_bind_on _ _ (ParentCorrect parent request) _ (hparent request) ?_
          intro answer hp
          refine Early.Sampling.holds_map (ih answer (cache.store request answer))
            (Outcome.prepend ⟨request, answer, true⟩) _ ?_
          intro out ho
          exact .fresh hr hp ho

theorem Run.extends {parent : ParentReply n} {program : Program n A} {cache final : Cache n}
    {result : A} {trace : List (Answered n)} (h : Run parent program cache result final trace) : final.Extends cache := by
  induction h with
  | pure => exact .refl _
  | hit present rest ih => exact ih
  | fresh absent parents rest ih => exact ih.trans (Cache.store_extends _ _ _ absent)

theorem Run.agrees {parent : ParentReply n} {program : Program n A} {cache final : Cache n}
    {result : A} {trace : List (Answered n)} (h : Run parent program cache result final trace) :
    ∀ entry ∈ trace, Agrees parent final entry.request entry.answer := by
  induction h with
  | pure => simp
  | @hit request next cache final answer result trace present rest ih =>
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact rest.extends.agrees parent request answer (response_agrees parent cache request answer present)
      · exact ih entry he
  | @fresh request next cache final answer result trace absent parents rest ih =>
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact rest.extends.agrees parent request answer (store_agrees parent cache request answer parents)
      · exact ih entry he

end StreamingSSSP.Exact.Implementation
