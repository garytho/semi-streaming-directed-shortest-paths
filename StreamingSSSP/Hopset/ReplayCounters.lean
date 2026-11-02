module

public import StreamingSSSP.Hopset.ExecutionReplay
public import StreamingSSSP.Hopset.LayerCounts

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}

theorem follow_recorded_le (hnum : 0 < cfg.initialNumerator) (ranks : Fin n → ℕ)
    (trace : List (Batched.ControlEntry n cfg)) (q : ℕ) (st : State cfg stored input q)
    (final : PackedState cfg stored input)
    (hf : followControls cfg hnum stored input ranks trace (some ⟨q, st⟩) = some final) (i : ℕ) :
    recordedCount hnum i st.layers ≤ recordedCount hnum i final.2.layers := by
  induction trace generalizing q st with
  | nil =>
      by_cases he : q < cfg.earlyLevel
      · simp only [followControls, finishPacked, he, ↓reduceIte] at hf
        cases hf
      · simp only [followControls, finishPacked, he, ↓reduceIte] at hf
        have hfinal : final = ⟨q, st⟩ := (Option.some.inj hf).symm
        subst final
        exact le_rfl
  | cons entry tail ih =>
      by_cases he : q < cfg.earlyLevel
      · by_cases hlevel : entry.level = q
        · by_cases hqueue : entry.queue = st.queue
          · simp only [followControls, he, hlevel, hqueue, ↓reduceDIte, ↓reduceIte] at hf
            let next := st.update hnum he
              (fun v => decide (ranks v = q), entryOwners st.queue entry hqueue)
            have hn : recordedCount hnum i st.layers ≤ recordedCount hnum i next.layers := by
              rw [recordedCount_update]
              exact Nat.le_add_right _ _
            exact hn.trans (ih (q + 1) next hf)
          · simp only [followControls, he, hlevel, hqueue, ↓reduceDIte, ↓reduceIte] at hf
            cases hf
        · simp only [followControls, he, hlevel, ↓reduceDIte, ↓reduceIte] at hf
          cases hf
      · simp only [followControls, he, ↓reduceDIte] at hf
        have hfinal : final = ⟨q, st⟩ := (Option.some.inj hf).symm
        subst final
        exact le_rfl

end

end StreamingSSSP.Hopset.Following
