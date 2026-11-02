module

public import StreamingReachability.Hopset.MeasuredBounds

@[expose] public section

namespace StreamingReachability.Hopset.Measured

open scoped Classical

variable {n : ℕ} {A B : Type*}

def BuilderCertificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word draws calls : ℕ) :
    Builder n A → ℕ → (A → Prop) → Prop
  | .pure value, _, P => P value
  | .trial cfg hn stored next, count, P =>
      0 < count ∧ BuilderCertificate input Q word draws calls (next none) (count - 1) P ∧
        Certificate input Q word (fixedGuess cfg hn stored) draws calls
          (fun out => BuilderCertificate input Q word draws calls (next (some out)) (count - 1) P)

theorem BuilderCertificate.mono (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word draws calls : ℕ) (program : Builder n A)
    (count : ℕ) (P T : A → Prop) (hc : BuilderCertificate input Q word draws calls program count P)
    (hP : ∀ value, P value → T value) :
    BuilderCertificate input Q word draws calls program count T := by
  induction program generalizing count with
  | pure value => exact hP value hc
  | trial cfg hn stored next ih =>
      refine ⟨hc.1, ih none _ hc.2.1, ?_⟩
      exact hc.2.2.mono input Q word _ draws calls _ _
        (fun out ho => ih (some out) _ ho)

theorem BuilderCertificate.weaken (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word draws calls : ℕ) (program : Builder n A)
    (count larger : ℕ) (P : A → Prop) (hc : BuilderCertificate input Q word draws calls program count P)
    (hcount : count ≤ larger) :
    BuilderCertificate input Q word draws calls program larger P := by
  induction program generalizing count larger with
  | pure value => exact hc
  | trial cfg hn stored next ih =>
      have hp := hc.1
      refine ⟨by omega, ih none _ _ hc.2.1 (Nat.sub_le_sub_right hcount 1), ?_⟩
      exact hc.2.2.mono input Q word _ draws calls _ _
        (fun out ho => ih (some out) _ _ ho (Nat.sub_le_sub_right hcount 1))

theorem BuilderCertificate.bind (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word draws calls : ℕ)
    (program : Builder n A) (next : A → Builder n B) (count extra : ℕ) (P : A → Prop) (T : B → Prop)
    (hc : BuilderCertificate input Q word draws calls program count P)
    (hn : ∀ value, P value → BuilderCertificate input Q word draws calls (next value) extra T) :
    BuilderCertificate input Q word draws calls (program.bind next) (count + extra) T := by
  induction program generalizing count with
  | pure value => exact (hn value hc).weaken input Q word draws calls _ _ _ T (by omega)
  | trial cfg positive stored resume ih =>
      have hp := hc.1
      have he : count + extra - 1 = (count - 1) + extra := by omega
      refine ⟨by omega, ?_, ?_⟩
      · simpa only [Builder.bind, he] using ih none (count - 1) hc.2.1
      · exact hc.2.2.mono input Q word _ draws calls _ _
          (fun out ho => by simpa only [Builder.bind, he] using ih (some out) (count - 1) ho)

structure BuilderFits (Q : Core.BatchAPI.Request n → ℕ → Prop) (word draws calls count : ℕ)
    (P : A → Prop) (out : Report n A) : Prop where
  calls_le : out.calls.length ≤ count * calls
  draws_le : out.draws.length ≤ count * draws
  calls_valid : ∀ call ∈ out.calls, Q call.request call.allowance
  draws_valid : ∀ draw ∈ out.draws, draw.bound ≤ word
  post : P out.result

theorem builder_certificate_holds {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (Q : Core.BatchAPI.Request n → ℕ → Prop)
    (word draws calls : ℕ) (program : Builder n A) (count : ℕ) (P : A → Prop)
    (hc : BuilderCertificate (input.filterMap view ++ auxiliary) Q word draws calls program count P) :
    Early.Sampling.Holds (builder (auxiliaryHandler view input auxiliary) program)
      (BuilderFits Q word draws calls count P) := by
  induction program generalizing count with
  | pure value =>
      exact Early.Sampling.holds_pure _ _ ⟨by simp, by simp, by simp, by simp, hc⟩
  | trial cfg positive stored next ih =>
      have hp := hc.1
      refine Reference.holds_bind_on _ _ (Fits Q word draws calls
        (fun out => BuilderCertificate (input.filterMap view ++ auxiliary) Q word draws calls
          (next (some out)) (count - 1) P)) _
        (certificate_holds view input auxiliary Q word (fixedGuess cfg positive stored) draws calls _ hc.2.2) ?_
      intro first hf
      have hn : BuilderCertificate (input.filterMap view ++ auxiliary) Q word draws calls
          (next first.result) (count - 1) P := by
        cases hr : first.result with
        | none => exact hc.2.1
        | some out =>
            have hpost := hf.post
            rw [hr] at hpost
            exact hpost
      refine Early.Sampling.holds_map (ih first.result _ hn) first.then _ ?_
      intro last hl
      refine ⟨?_, ?_, ?_, ?_, hl.post⟩
      · change (first.calls ++ last.calls).length ≤ count * calls
        rw [List.length_append]
        have hfirst := hf.calls_le
        have hlast := hl.calls_le
        have he : count * calls = calls + (count - 1) * calls := by
          have hn : (count - 1) + 1 = count := by omega
          nlinarith only [congrArg (fun k => k * calls) hn]
        omega
      · change (first.draws ++ last.draws).length ≤ count * draws
        rw [List.length_append]
        have hfirst := hf.draws_le
        have hlast := hl.draws_le
        have he : count * draws = draws + (count - 1) * draws := by
          have hn : (count - 1) + 1 = count := by omega
          nlinarith only [congrArg (fun k => k * draws) hn]
        omega
      · intro call hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hf.calls_valid call hm
        · exact hl.calls_valid call hm
      · intro draw hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hf.draws_valid draw hm
        · exact hl.draws_valid draw hm

end StreamingReachability.Hopset.Measured
