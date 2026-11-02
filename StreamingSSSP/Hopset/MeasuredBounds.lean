module

public import StreamingSSSP.Hopset.TrialWordBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n : ℕ} {A B : Type*}

def Actual {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (out : Report n A) : Prop :=
  out.passes = (out.calls.map Call.passes).sum ∧
    ∀ call ∈ out.calls, call.passes = (auxiliaryHandler view input auxiliary call.request call.allowance).passes

theorem Actual.then {E : Type*} {view : E → Option (StoredEdges.Edge n)} {input : List E}
    {auxiliary : List (StoredEdges.Edge n)} {first : Report n A} {last : Report n B}
    (hf : Actual view input auxiliary first) (hl : Actual view input auxiliary last) :
    Actual view input auxiliary (first.then last) := by
  refine ⟨?_, ?_⟩
  · change first.passes + last.passes = ((first.calls ++ last.calls).map Call.passes).sum
    rw [List.map_append, List.sum_append, ← hf.1, ← hl.1]
  · intro call hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.2 call hm
    · exact hl.2 call hm

theorem auxiliary_actual {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (request : Core.BatchAPI.Request n) (allowance : ℕ) :
    Actual view input auxiliary (auxiliaryHandler view input auxiliary request allowance) := by
  refine ⟨rfl, ?_⟩
  intro call hm
  have he := List.mem_singleton.mp hm
  subst call
  rfl

theorem code_actual {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (program : Code n A) :
    Early.Sampling.Holds (code (auxiliaryHandler view input auxiliary) program) (Actual view input auxiliary) := by
  induction program with
  | pure value => exact Early.Sampling.holds_pure _ _ ⟨rfl, by simp⟩
  | abort => exact Early.Sampling.holds_pure _ _ ⟨rfl, by simp⟩
  | uniform bound positive next ih =>
      apply Early.Sampling.holds_bind
      intro i
      exact Early.Sampling.holds_map (ih i) (Report.draw bound i) _ (fun out ho => ho)
  | batch request allowance next ih =>
      cases hr : (auxiliaryHandler view input auxiliary request allowance).result with
      | none =>
          simp only [code, hr]
          exact Early.Sampling.holds_pure _ _ (auxiliary_actual view input auxiliary request allowance)
      | some reply =>
          simp only [code, hr]
          exact Early.Sampling.holds_map (ih reply) (auxiliaryHandler view input auxiliary request allowance).then _
            (fun out ho => (auxiliary_actual view input auxiliary request allowance).then ho)

theorem builder_actual {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) (program : Builder n A) :
    Early.Sampling.Holds (builder (auxiliaryHandler view input auxiliary) program) (Actual view input auxiliary) := by
  induction program with
  | pure value => exact Early.Sampling.holds_pure _ _ ⟨rfl, by simp⟩
  | trial cfg hn stored next ih =>
      refine Reference.holds_bind_on _ _ (Actual view input auxiliary) _
        (code_actual view input auxiliary (fixedGuess cfg hn stored)) ?_
      intro first hf
      exact Early.Sampling.holds_map (ih first.result) first.then _ (fun out ho => hf.then ho)

theorem Fits.passes {E : Type*} (view : E → Option (StoredEdges.Edge n)) (input : List E)
    (auxiliary : List (StoredEdges.Edge n)) {x radius records catalogWords scale weight word draws calls : ℕ}
    {P : A → Prop} {out : Report n (Option A)} (hn : 0 < n)
    (h : Fits (QueryBounds x radius records catalogWords scale weight) word draws calls P out)
    (ha : Actual view input auxiliary out) (hp : ∀ e ∈ input.filterMap view ++ auxiliary, 0 < e.weight) :
    out.passes ≤ calls * passLimit n x radius records := by
  have hsum := List.sum_le_sum (l := out.calls) (f := Call.passes)
    (g := fun _ => passLimit n x radius records) (fun call hm => by
      rw [ha.2 call hm]
      exact (h.calls_valid call hm).passes hn view input auxiliary hp)
  calc
    out.passes = (out.calls.map Call.passes).sum := ha.1
    _ ≤ (out.calls.map (fun _ => passLimit n x radius records)).sum := hsum
    _ = out.calls.length * passLimit n x radius records := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ h.calls_le

end StreamingSSSP.Hopset.Measured
