module

public import StreamingReachability.Hopset.MeasuredProgram

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ} {A B : Type*}

def Certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) :
    Code n A → ℕ → ℕ → (A → Prop) → Prop
  | .pure value, _, _, P => P value
  | .abort, _, _, _ => True
  | .uniform bound _ next, draws, calls, P =>
      0 < draws ∧ bound ≤ word ∧ ∀ i, Certificate input Q word (next i) (draws - 1) calls P
  | .batch request allowance next, draws, calls, P =>
      0 < calls ∧ Q request allowance ∧
        Certificate input Q word (next (Core.BatchAPI.run request input).records) draws (calls - 1) P

theorem Certificate.mono (input : List (StoredEdges.Edge n)) (Q : Core.BatchAPI.Request n → ℕ → Prop)
    (word : ℕ) (program : Code n A) (draws calls : ℕ) (P T : A → Prop)
    (hc : Certificate input Q word program draws calls P) (hP : ∀ value, P value → T value) :
    Certificate input Q word program draws calls T := by
  induction program generalizing draws calls with
  | pure value => exact hP value hc
  | abort => trivial
  | uniform bound positive next ih => exact ⟨hc.1, hc.2.1, fun i => ih i _ _ (hc.2.2 i)⟩
  | batch request allowance next ih => exact ⟨hc.1, hc.2.1, ih _ _ _ hc.2.2⟩

theorem Certificate.weaken (input : List (StoredEdges.Edge n)) (Q : Core.BatchAPI.Request n → ℕ → Prop)
    (word : ℕ) (program : Code n A) (draws calls largerDraws largerCalls : ℕ) (P : A → Prop)
    (hc : Certificate input Q word program draws calls P)
    (hd : draws ≤ largerDraws) (hq : calls ≤ largerCalls) :
    Certificate input Q word program largerDraws largerCalls P := by
  induction program generalizing draws calls largerDraws largerCalls with
  | pure value => exact hc
  | abort => trivial
  | uniform bound positive next ih =>
      have hpos := hc.1
      exact ⟨by omega, hc.2.1, fun i => ih i _ _ _ _ (hc.2.2 i) (Nat.sub_le_sub_right hd 1) hq⟩
  | batch request allowance next ih =>
      have hpos := hc.1
      exact ⟨by omega, hc.2.1, ih _ _ _ _ _ hc.2.2 hd (Nat.sub_le_sub_right hq 1)⟩

theorem Certificate.bind (input : List (StoredEdges.Edge n)) (Q : Core.BatchAPI.Request n → ℕ → Prop)
    (word : ℕ) (program : Code n A) (next : A → Code n B) (draws calls extraDraws extraCalls : ℕ)
    (P : A → Prop) (T : B → Prop)
    (hc : Certificate input Q word program draws calls P)
    (hn : ∀ value, P value → Certificate input Q word (next value) extraDraws extraCalls T) :
    Certificate input Q word (program.bind next) (draws + extraDraws) (calls + extraCalls) T := by
  induction program generalizing draws calls with
  | pure value => exact (hn value hc).weaken input Q word _ _ _ _ _ T (by omega) (by omega)
  | abort => trivial
  | uniform bound positive resume ih =>
      have hpos := hc.1
      refine ⟨by omega, hc.2.1, ?_⟩
      intro i
      have h := ih i (draws - 1) calls (hc.2.2 i)
      have he : draws + extraDraws - 1 = (draws - 1) + extraDraws := by omega
      simpa only [Code.bind, he] using h
  | batch request allowance resume ih =>
      have hpos := hc.1
      refine ⟨by omega, hc.2.1, ?_⟩
      have h := ih _ draws (calls - 1) hc.2.2
      have he : calls + extraCalls - 1 = (calls - 1) + extraCalls := by omega
      simpa only [Code.bind, he] using h

theorem Certificate.map (input : List (StoredEdges.Edge n)) (Q : Core.BatchAPI.Request n → ℕ → Prop)
    (word : ℕ) (program : Code n A) (f : A → B) (draws calls : ℕ) (P : A → Prop) (T : B → Prop)
    (hc : Certificate input Q word program draws calls P) (hf : ∀ value, P value → T (f value)) :
    Certificate input Q word (program.map f) draws calls T := by
  have h := hc.bind input Q word program (fun value => .pure (f value)) draws calls 0 0 P T
    (fun value hp => hf value hp)
  simpa only [Code.map, Nat.add_zero] using h

structure Fits (Q : Core.BatchAPI.Request n → ℕ → Prop) (word draws calls : ℕ)
    (P : A → Prop) (out : Report n (Option A)) : Prop where
  calls_le : out.calls.length ≤ calls
  draws_le : out.draws.length ≤ draws
  calls_valid : ∀ call ∈ out.calls, Q call.request call.allowance
  draws_valid : ∀ draw ∈ out.draws, draw.bound ≤ word
  post : match out.result with | none => True | some value => P value

theorem Fits.draw {Q : Core.BatchAPI.Request n → ℕ → Prop} {word draws calls : ℕ} {P : A → Prop}
    {out : Report n (Option A)} (h : Fits Q word (draws - 1) calls P out)
    (hd : 0 < draws) (bound : ℕ) (value : Fin bound) (hb : bound ≤ word) :
    Fits Q word draws calls P (out.draw bound value) := by
  refine ⟨h.calls_le, ?_, h.calls_valid, ?_, h.post⟩
  · change out.draws.length + 1 ≤ draws
    have hh := h.draws_le
    omega
  · intro draw hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hb
    · exact h.draws_valid draw hm

theorem Fits.call {Q : Core.BatchAPI.Request n → ℕ → Prop} {word draws calls : ℕ} {P : A → Prop}
    {out : Report n (Option A)} (h : Fits Q word draws (calls - 1) P out)
    (hc : 0 < calls) (first : Report n B) (call : Call n)
    (hcall : first.calls = [call]) (hdraws : first.draws = [])
    (hq : Q call.request call.allowance) :
    Fits Q word draws calls P (first.then out) := by
  refine ⟨?_, ?_, ?_, ?_, h.post⟩
  · change (first.calls ++ out.calls).length ≤ calls
    rw [hcall, List.length_append]
    have hh := h.calls_le
    simp only [List.length_singleton]
    omega
  · simpa only [Report.then, hdraws, List.nil_append] using h.draws_le
  · intro c hm
    rcases List.mem_append.mp hm with hm | hm
    · rw [hcall] at hm
      have he := List.mem_singleton.mp hm
      simpa only [he] using hq
    · exact h.calls_valid c hm
  · intro draw hm
    exact h.draws_valid draw (by simpa only [Report.then, hdraws, List.nil_append] using hm)

theorem certificate_holds {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (Q : Core.BatchAPI.Request n → ℕ → Prop)
    (word : ℕ) (program : Code n A) (draws calls : ℕ) (P : A → Prop)
    (hc : Certificate (input.filterMap view ++ auxiliary) Q word program draws calls P) :
    Early.Sampling.Holds (code (auxiliaryHandler view input auxiliary) program) (Fits Q word draws calls P) := by
  induction program generalizing draws calls with
  | pure value => exact Early.Sampling.holds_pure _ _ ⟨by simp, by simp, by simp, by simp, hc⟩
  | abort => exact Early.Sampling.holds_pure _ _ ⟨by simp, by simp, by simp, by simp, trivial⟩
  | uniform bound positive next ih =>
      apply Early.Sampling.holds_bind
      intro i
      exact Early.Sampling.holds_map (ih i _ _ (hc.2.2 i)) (Report.draw bound i) _
        (fun out ho => ho.draw hc.1 bound i hc.2.1)
  | batch request allowance next ih =>
      have hpos := hc.1
      have he : (auxiliaryHandler view input auxiliary request allowance).result =
          match Core.BatchAPI.runGuarded request allowance (input.filterMap view ++ auxiliary) with
          | .error _ => none | .ok result => some result.records := by
        simp only [auxiliaryHandler, Core.BatchAPI.runGuardedMeasuredAuxiliary_eq,
          Core.BatchAPI.runGuardedMeasured_erases]
        rfl
      cases hr : Core.BatchAPI.runGuarded request allowance (input.filterMap view ++ auxiliary) with
      | error reason =>
          have hn : (auxiliaryHandler view input auxiliary request allowance).result = none := he.trans (by rw [hr])
          simp only [code, hn]
          refine Early.Sampling.holds_pure _ _ ⟨?_, ?_, ?_, ?_, trivial⟩
          · change 1 ≤ calls
            omega
          · exact Nat.zero_le _
          · intro call hm
            have hcall : call = ⟨request, allowance, (auxiliaryHandler view input auxiliary request allowance).passes⟩ :=
              List.mem_singleton.mp hm
            simpa only [hcall] using hc.2.1
          · intro draw hm; cases hm
      | ok result =>
          have hraw : result = Core.BatchAPI.run request (input.filterMap view ++ auxiliary) :=
            Core.GuardedDriver.run_erases _ _ _ _ hr
          have hn : (auxiliaryHandler view input auxiliary request allowance).result = some (Core.BatchAPI.run request
              (input.filterMap view ++ auxiliary)).records := by
            rw [hr, hraw] at he
            exact he
          simp only [code, hn]
          exact Early.Sampling.holds_map (ih _ _ _ hc.2.2) (auxiliaryHandler view input auxiliary request allowance).then _
            (fun out ho => ho.call hc.1 (auxiliaryHandler view input auxiliary request allowance)
              ⟨request, allowance, (auxiliaryHandler view input auxiliary request allowance).passes⟩ rfl rfl hc.2.1)

end StreamingReachability.Hopset.Measured
