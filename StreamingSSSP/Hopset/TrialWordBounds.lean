module

public import StreamingSSSP.Hopset.FixedGuessResources
public import StreamingSSSP.Hopset.TrialSound

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ} {A : Type*}

theorem Certificate.checked_strengthen (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (program : Code n A)
    (draws calls : ℕ) (P T : A → Prop)
    (hc : Certificate input Q word program draws calls P) (ht : Backend.Checked input program T) :
    Certificate input Q word program draws calls T := by
  induction program generalizing draws calls with
  | pure value => exact ht
  | abort => trivial
  | uniform bound positive next ih => exact ⟨hc.1, hc.2.1, fun i => ih i _ _ (hc.2.2 i) (ht i)⟩
  | batch request allowance next ih => exact ⟨hc.1, hc.2.1, ih _ _ _ hc.2.2 ht⟩

def StateWords (weight : ℕ) (state : State n) : Prop :=
  ∀ e ∈ state.output.explicit, e.weight ≤ weight

def OutputWords (weight : ℕ) (out : Output n) : Prop :=
  ∀ e ∈ out.explicit, e.weight ≤ weight

theorem batch_words (input : List (StoredEdges.Edge n)) (cfg : Config) (hn : 0 < n) (r : ℕ)
    (stored : Implicit.Representation n) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (state : State n) (weight : ℕ)
    (hstate : StateWords weight state) (hr : cfg.searchRadius r ≤ cfg.globalRadius)
    (hw : cfg.inputScale * cfg.globalRadius ≤ weight) :
    Backend.Checked input (batch cfg r stored sets targets state) (fun result => StateWords weight result.2) := by
  let request := Core.BatchAPI.Request.ofCatalog stored.explicit (catalog cfg r stored.blocks sets targets) cfg.blockSize
  let reply := (Core.BatchAPI.run request input).records
  have hrecords : ∀ record ∈ reply, record.distance ≤ cfg.globalRadius :=
    fun record hm => (raw_record_radius hn request input record hm).trans
      (request_radius cfg r stored.explicit stored.blocks sets targets cfg.blockSize hr)
  dsimp only [batch, Backend.Checked]
  split
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hstate e he
    · exact (emitted_weights cfg targets reply cfg.globalRadius hrecords e he).trans hw
  · trivial

theorem levels_words (input : List (StoredEdges.Edge n)) (cfg : Config) (hn : 0 < n)
    (stored : Implicit.Representation n) (rank : Vector ℕ n) (weight : ℕ)
    (hr : ∀ r, cfg.searchRadius r ≤ cfg.globalRadius) (hw : cfg.inputScale * cfg.globalRadius ≤ weight)
    (fuel r : ℕ) (queue : List (Finset (Fin n))) (state : State n) (hstate : StateWords weight state) :
    Backend.Checked input (levels cfg hn stored rank fuel r queue state) (OutputWords weight) := by
  induction fuel generalizing r queue state with
  | zero => exact hstate
  | succ fuel ih =>
      dsimp only [levels]
      split
      · apply Backend.checked_bind _ _ _ _ _
          (batch_words input cfg hn r stored _ _ state weight hstate (hr r) hw)
        intro result hresult
        apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
        intro pivots _
        split
        · exact ih _ _ _ hresult
        · trivial
      · apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
        intro targets _
        apply Backend.checked_bind _ _ _ _ _
          (batch_words input cfg hn r stored _ _ state weight hstate (hr r) hw)
        intro result hresult
        apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
        intro pivots _
        split_ifs <;> first | trivial | exact ih _ _ _ hresult

theorem fixed_guess_words (input : List (StoredEdges.Edge n)) (cfg : Config) (hn : 0 < n)
    (stored : Implicit.Representation n) (weight : ℕ)
    (hr : ∀ r, cfg.searchRadius r ≤ cfg.globalRadius) (hw : cfg.inputScale * cfg.globalRadius ≤ weight) :
    Backend.Checked input (fixedGuess cfg hn stored) (OutputWords weight) := by
  dsimp only [fixedGuess]
  split
  · apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
    intro rank _
    apply Backend.checked_bind _ _ _ _ _
      (batch_words input cfg hn 0 stored _ _ ⟨{}, n, 0⟩ weight (by simp [StateWords]) (hr 0) hw)
    intro result hresult
    exact levels_words input cfg hn stored rank weight hr hw _ _ _ _ hresult
  · trivial

end StreamingSSSP.Hopset.Measured
