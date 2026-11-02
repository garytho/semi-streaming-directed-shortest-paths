module

public import StreamingSSSP.Hopset.PathRuns

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n : ℕ} {cfg : Config} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}

def CallPresent (trace : List (Batched.ControlEntry n cfg)) (layer : Layer cfg stored input) : Prop :=
  ∃ entry ∈ trace, entry.level = layer.level ∧ entry.queue = layer.queue

theorem follow_layers (hnum : 0 < cfg.initialNumerator) (ranks : Fin n → ℕ)
    (trace : List (Batched.ControlEntry n cfg)) (r : ℕ) (st : State cfg stored input r)
    (final : PackedState cfg stored input)
    (hf : followControls cfg hnum stored input ranks trace (some ⟨r, st⟩) = some final) :
    ∀ layer ∈ final.2.layers, layer ∈ st.layers ∨ CallPresent trace layer := by
  induction trace generalizing r st with
  | nil =>
      simp only [followControls, finishPacked] at hf
      by_cases he : r < cfg.earlyLevel
      · simp only [he, ↓reduceIte] at hf
        cases hf
      · simp only [he, ↓reduceIte] at hf
        have hfinal : final = ⟨r, st⟩ := (Option.some.inj hf).symm
        subst final
        intro layer hl
        exact Or.inl hl
  | cons entry tail ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hlevel : entry.level = r
        · by_cases hqueue : entry.queue = st.queue
          · simp only [followControls, he, hlevel, hqueue, ↓reduceDIte, ↓reduceIte] at hf
            let next := st.update hnum he
              (fun v => decide (ranks v = r), entryOwners st.queue entry hqueue)
            intro layer hl
            rcases ih (r + 1) next hf layer hl with hold | htail
            · rcases List.mem_append.mp hold with hold | hnew
              · exact Or.inl hold
              · have hnewEq := List.mem_singleton.mp hnew
                subst layer
                exact Or.inr ⟨entry, List.mem_cons_self, hlevel, hqueue⟩
            · obtain ⟨old, ho, hl, hq⟩ := htail
              exact Or.inr ⟨old, List.mem_cons_of_mem _ ho, hl, hq⟩
          · simp only [followControls, he, hlevel, hqueue, ↓reduceDIte, ↓reduceIte] at hf
            cases hf
        · simp only [followControls, he, hlevel, ↓reduceDIte, ↓reduceIte] at hf
          cases hf
      · simp only [followControls, he, ↓reduceDIte] at hf
        have hfinal : final = ⟨r, st⟩ := (Option.some.inj hf).symm
        subst final
        intro layer hl
        exact Or.inl hl

theorem replay_layers_present (hnum : 0 < cfg.initialNumerator) (root : State cfg stored input 0)
    (hroot : root.layers = []) (ranks : Fin n → ℕ) (trace : List (Batched.ControlEntry n cfg))
    (st : State cfg stored input cfg.earlyLevel)
    (h : replayEarly cfg hnum stored input root ranks trace = some st) :
    ∀ layer ∈ st.layers, CallPresent trace layer := by
  unfold replayEarly at h
  cases hf : followControls cfg hnum stored input ranks trace (some ⟨0, root⟩) with
  | none =>
      simp only [hf, unpackState] at h
      cases h
  | some final =>
      obtain ⟨j, final⟩ := final
      by_cases hj : j = cfg.earlyLevel
      · subst j
        have he : final = st := by simpa only [hf, unpackState, ↓reduceDIte, Option.some.injEq] using h
        subst st
        intro layer hl
        rcases follow_layers hnum ranks trace 0 root ⟨cfg.earlyLevel, final⟩ hf layer hl with hold | hnew
        · simpa only [hroot, List.not_mem_nil] using hold
        · exact hnew
      · simp only [hf, unpackState, hj, ↓reduceDIte] at h
        cases h

end

end StreamingSSSP.Hopset.Following
