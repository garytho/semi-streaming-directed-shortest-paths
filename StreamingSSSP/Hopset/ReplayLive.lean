module

public import StreamingSSSP.Hopset.ReplayProvenance

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem early_choices_shape (cfg : Config) (hn : 0 < n) (ranks : Fin n → ℕ) (r : ℕ)
    (he : r < cfg.earlyLevel) (sets : Vector (Finset (Fin n)) ns) :
    Early.Sampling.Holds (Batched.choiceRowsLaw cfg hn (Vector.ofFn ranks) r sets) (fun choices =>
      ∃ owners, choices = Batched.currentChoices cfg sets (fun v => decide (ranks v = r)) owners) := by
  simp only [Batched.choiceRowsLaw, he, ↓reduceIte]
  refine Early.Sampling.holds_map (P := fun _ => True) (by intro z hz; trivial) _ _ ?_
  intro owners _
  refine ⟨owners, ?_⟩
  simpa only [Vector.get_ofFn] using (Batched.currentChoices_decide cfg sets ranks r owners).symm

theorem control_follow_live (cfg : Config) (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ)
    (fuel r : ℕ) (st : State cfg stored input r) (hr : r ≤ cfg.earlyLevel) :
    Early.Sampling.Holds (Batched.controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel r st.queue)
      (fun trace => cfg.earlyLevel ≤ r + trace.length →
        ∃ final : State cfg stored input cfg.earlyLevel,
          followControls cfg hnum stored input ranks trace (some ⟨r, st⟩) = some ⟨cfg.earlyLevel, final⟩) := by
  induction fuel generalizing r st with
  | zero =>
      apply Early.Sampling.holds_pure
      intro hlen
      have he : r = cfg.earlyLevel := by simpa only [List.length_nil, Nat.add_zero] using hr.antisymm hlen
      subst r
      exact ⟨st, followControls_done cfg hnum stored input ranks [] _ st le_rfl⟩
  | succ fuel ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : Batched.AllGood cfg stored input r st.queue
        · simp only [Batched.controlTraceLaw, hg, ↓reduceIte]
          refine Reference.holds_bind_on _ _ _ _ (early_choices_shape cfg hn ranks r he st.queue.toArray.toVector) ?_
          intro choices hchoices
          obtain ⟨owners, rfl⟩ := hchoices
          let next := st.update hnum he (fun v => decide (ranks v = r), owners)
          refine Early.Sampling.holds_map (ih (r + 1) next (by omega)) (⟨r, st.queue,
            Batched.currentChoices cfg st.queue.toArray.toVector (fun v => decide (ranks v = r)) owners⟩ :: ·) _ ?_
          intro tail htail hlen
          have hlen' : cfg.earlyLevel ≤ (r + 1) + tail.length := by
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨final, hf⟩ := htail hlen'
          refine ⟨final, ?_⟩
          rw [followControls_head cfg hnum stored input ranks r st he owners tail]
          exact hf
        · simp only [Batched.controlTraceLaw, hg, ↓reduceIte]
          apply Early.Sampling.holds_pure
          intro hlen
          simp only [List.length_nil, Nat.add_zero] at hlen
          omega
      · have hre : r = cfg.earlyLevel := by omega
        subst r
        intro z hz hlen
        exact ⟨st, followControls_done cfg hnum stored input ranks z.1 _ st le_rfl⟩

theorem geometric_replay_live (cfg : Config) (hnum : 0 < cfg.initialNumerator) (hn : 0 < n)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (root : State cfg stored input 0) (ranks : Fin n → ℕ) (fuel : ℕ)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize) :
    (Batched.geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue).prob
      (fun trace => cfg.earlyLevel ≤ trace.length →
        ∃ st, replayEarly cfg hnum stored input root ranks (trace.map Batched.GeometricEntry.control) = some st) = 1 := by
  let P := fun trace : List (Batched.ControlEntry n cfg) => cfg.earlyLevel ≤ trace.length →
    ∃ st, replayEarly cfg hnum stored input root ranks trace = some st
  have hh : Early.Sampling.Holds
      (Batched.controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue) P := by
    refine Early.Sampling.holds_mono (control_follow_live cfg hnum hn stored input ranks fuel 0 root (Nat.zero_le _)) ?_
    intro trace ht hlen
    obtain ⟨st, he⟩ := ht (by simpa only [Nat.zero_add] using hlen)
    refine ⟨st, ?_⟩
    simp only [replayEarly, he, unpackState, ↓reduceDIte]
  have hc := probability_of_holds _ P hh
  have he := Batched.geometricTrace_control cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue hs hp hsize hnum
    (fun trace => @ite ℝ (P trace) (Classical.propDecidable _) 1 0)
  have hprob :
      (Batched.geometricTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 root.queue).prob
        (fun trace => P (trace.map Batched.GeometricEntry.control)) = 1 := he.trans hc
  simpa only [P, List.length_map] using hprob

end

end StreamingSSSP.Hopset.Following
