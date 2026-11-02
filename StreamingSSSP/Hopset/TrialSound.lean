module

public import StreamingSSSP.Hopset.NodeSound
public import StreamingSSSP.Hopset.ProgramSoundness

@[expose] public section

namespace StreamingSSSP.Hopset

open StoredEdges

variable {n : ℕ}

def Output.Sound (G : Graph (Fin n)) (out : Output n) : Prop :=
  ∀ e ∈ out.explicit, G.dist e.source e.target ≤ (e.weight : Distance) ∧ 0 < e.weight

def State.Sound (G : Graph (Fin n)) (state : State n) : Prop := state.output.Sound G

theorem batch_sound (G : Graph (Fin n)) (cfg : Config) (r : ℕ)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (state : State n) (hstate : state.Sound G) :
    Backend.Checked input (batch cfg r stored sets targets state)
      (fun result => result.2.Sound G) := by
  dsimp only [batch, Backend.Checked]
  split
  next h =>
    intro e he
    rcases List.mem_append.mp he with hold | hnew
    · exact hstate e hold
    · exact Backend.emittedStars_sound G cfg r stored input hn hs hp hsize hinput hstored hG
        sets targets e hnew
  next h => trivial

theorem levels_sound (G : Graph (Fin n)) (cfg : Config)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (rank : Vector ℕ n) (fuel r : ℕ) (queue : List (Finset (Fin n))) (state : State n)
    (hstate : state.Sound G) :
    Backend.Checked input (levels cfg hn stored rank fuel r queue state) (Output.Sound G) := by
  induction fuel generalizing r queue state with
  | zero => exact hstate
  | succ fuel ih =>
      dsimp only [levels]
      split
      next hr =>
        apply Backend.checked_bind _ _ _ _ _
          (batch_sound G cfg r stored input hn hs hp hsize hinput hstored hG _ _ state hstate)
        intro result hresult
        apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
        intro pivots _
        split_ifs
        · exact ih _ _ _ hresult
        · trivial
      next hr =>
        apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
        intro targets _
        apply Backend.checked_bind _ _ _ _ _
          (batch_sound G cfg r stored input hn hs hp hsize hinput hstored hG _ _ state hstate)
        intro result hresult
        apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
        intro pivots _
        split_ifs <;> first | trivial | exact ih _ _ _ hresult

theorem fixedGuess_sound (G : Graph (Fin n)) (cfg : Config)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v) :
    Backend.Checked input (fixedGuess cfg hn stored) (Output.Sound G) := by
  dsimp only [fixedGuess]
  split
  next h =>
    apply Backend.checked_bind _ _ _ (fun _ => True) _ (Backend.checked_true _ _)
    intro rank _
    apply Backend.checked_bind _ _ _ _ _
      (batch_sound G cfg 0 stored input hn hs hp hsize hinput hstored hG _ _ ⟨{}, n, 0⟩
        (by simp [State.Sound, Output.Sound]))
    intro result hresult
    exact levels_sound G cfg stored input hn hs hp hsize hinput hstored hG rank _ _ _ _ hresult
  next h => trivial

theorem fixedGuess_sound_probability (G : Graph (Fin n)) (cfg : Config)
    (stored : Implicit.Representation n) (input : List (Edge n)) (hn : 0 < n)
    (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight)
    (hsize : ∀ B ∈ stored.blocks, B.card ≤ cfg.blockSize)
    (hinput : Implicit.Noncontracting G (graphOfEdges input)) (hstored : stored.Sound G)
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v) :
    (Code.evaluate (Backend.guardedHandler input) (fixedGuess cfg hn stored)).prob
      (fun result => match result with | none => True | some out => out.Sound G) = 1 := by
  convert Backend.checked_guarded_probability input _ _
    (fixedGuess_sound G cfg stored input hn hs hp hsize hinput hstored hG) using 1
  apply Law.prob_congr
  intro result
  cases result <;> rfl

def commit (stored : Implicit.Representation n) (out : Output n) : Implicit.Representation n :=
  ⟨stored.explicit ++ out.explicit, stored.blocks ++ out.blocks⟩

theorem commit_sound (G : Graph (Fin n)) (stored : Implicit.Representation n)
    (out : Output n) (hs : stored.Sound G) (ho : out.Sound G) : (commit stored out).Sound G := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hs e h
  · exact (ho e h).1

theorem commit_positive (stored : Implicit.Representation n) (out : Output n)
    (G : Graph (Fin n)) (hs : ∀ e ∈ stored.explicit, 0 < e.weight) (ho : out.Sound G) :
    ∀ e ∈ (commit stored out).explicit, 0 < e.weight := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hs e h
  · exact (ho e h).2

end StreamingSSSP.Hopset
