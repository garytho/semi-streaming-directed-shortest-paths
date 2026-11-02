module

public import StreamingSSSP.Hopset.BuilderChecked
public import StreamingSSSP.Hopset.TrialBounds

@[expose] public section

namespace StreamingSSSP.Hopset

variable {n : ℕ}

structure StoredValid (G : Graph (Fin n)) (x : ℕ) (stored : Implicit.Representation n) : Prop where
  sound : stored.Sound G
  positive : ∀ e ∈ stored.explicit, 0 < e.weight
  blocks : ∀ B ∈ stored.blocks, B.card ≤ x

theorem StoredValid.commit {G : Graph (Fin n)} {x : ℕ} {stored : Implicit.Representation n}
    (h : StoredValid G x stored) (out : Output n) (ho : out.Sound G)
    (hsize : ∀ B ∈ out.blocks, B.card ≤ x) : StoredValid G x (commit stored out) :=
  ⟨commit_sound G stored out h.sound ho, commit_positive stored out G h.positive ho,
    commit_blocks_small stored out x h.blocks hsize⟩

theorem executeGuesses_valid (G : Graph (Fin n)) (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n))
    (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (frozen : Implicit.Representation n) (hfrozen : StoredValid G x frozen)
    (deltas : List {delta : ℕ // 0 < delta}) (committed : Implicit.Representation n)
    (hcommitted : StoredValid G x committed) :
    Builder.Checked input (executeGuesses hn accuracy x ha frozen deltas committed) (StoredValid G x) := by
  induction deltas generalizing committed with
  | nil => exact hcommitted
  | cons delta deltas ih =>
      let cfg := Parameters.configuration n accuracy x delta.val (volume frozen.blocks) ha delta.property
      refine ⟨ih committed hcommitted, ?_⟩
      have hs := fixedGuess_sound G cfg frozen input hn hfrozen.positive hp hfrozen.blocks hinput hfrozen.sound hG
      have hb := Code.ensures_checked input (fixedGuess cfg hn frozen) (Output.Bounded cfg)
        (fixedGuess_bounded cfg hn frozen)
      apply Backend.checked_mono _ _ _ _ (Backend.checked_and _ _ _ _ hs hb)
      intro out ho
      exact ih (commit committed out) (hcommitted.commit out ho.1 ho.2.block_size)

theorem repeatTrials_valid (G : Graph (Fin n)) (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n)) (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (frozen : Implicit.Representation n) (hfrozen : StoredValid G x frozen)
    (deltas : List {delta : ℕ // 0 < delta}) (count : ℕ) (committed : Implicit.Representation n)
    (hcommitted : StoredValid G x committed) :
    Builder.Checked input (repeatTrials hn accuracy x ha deltas frozen count committed) (StoredValid G x) := by
  induction count generalizing committed with
  | zero => exact hcommitted
  | succ count ih =>
      apply Builder.checked_bind _ _ _ _ _
        (executeGuesses_valid G hn accuracy x ha input hp hinput hG frozen hfrozen deltas committed hcommitted)
      intro next hnext
      exact ih next hnext

theorem stages_valid (G : Graph (Fin n)) (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (input : List (StoredEdges.Edge n)) (hp : ∀ e ∈ input, 0 < e.weight)
    (hinput : Implicit.Noncontracting G (StoredEdges.graphOfEdges input))
    (hG : ∀ u v, u ≠ v → (1 : Distance) ≤ G u v)
    (deltas : List {delta : ℕ // 0 < delta}) (trials count : ℕ) (stored : Implicit.Representation n)
    (hstored : StoredValid G x stored) :
    Builder.Checked input (stages hn accuracy x ha deltas trials count stored) (StoredValid G x) := by
  induction count generalizing stored with
  | zero => exact hstored
  | succ count ih =>
      apply Builder.checked_bind _ _ _ _ _
        (repeatTrials_valid G hn accuracy x ha input hp hinput hG stored hstored deltas trials stored hstored)
      intro next hnext
      exact ih next hnext

end StreamingSSSP.Hopset
