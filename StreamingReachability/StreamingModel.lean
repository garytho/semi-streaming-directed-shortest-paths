module

public import Mathlib

@[expose] public section

namespace StreamingReachability.Streaming

structure Metered (S : Type*) where
  state : S
  reads : ℕ
  peakCells : ℕ

def readEdge {E S : Type*} (step : S → E → S) (cells : S → ℕ)
    (m : Metered S) (e : E) : Metered S :=
  let state := step m.state e
  ⟨state, m.reads + 1, max m.peakCells (cells state)⟩

def readPass {E S : Type*} (step : S → E → S) (cells : S → ℕ)
    (input : List E) (initial : S) : Metered S :=
  input.foldl (readEdge step cells) ⟨initial, 0, cells initial⟩

theorem readPass_state {E S : Type*} (step : S → E → S) (cells : S → ℕ)
    (input : List E) (initial : S) :
    (readPass step cells input initial).state = input.foldl step initial := by
  have h (xs : List E) (m : Metered S) :
      (xs.foldl (readEdge step cells) m).state = xs.foldl step m.state := by
    induction xs generalizing m with
    | nil => rfl
    | cons e es ih => exact ih (readEdge step cells m e)
  exact h input _

theorem readPass_reads {E S : Type*} (step : S → E → S) (cells : S → ℕ)
    (input : List E) (initial : S) :
    (readPass step cells input initial).reads = input.length := by
  have h (xs : List E) (m : Metered S) :
      (xs.foldl (readEdge step cells) m).reads = m.reads + xs.length := by
    induction xs generalizing m with
    | nil => simp
    | cons e es ih =>
        simpa [List.foldl_cons, readEdge, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using (ih (readEdge step cells m e))
  simpa only [readPass, Nat.zero_add] using h input ⟨initial, 0, cells initial⟩

theorem readPass_bound {E S : Type*} (step : S → E → S) (cells : S → ℕ)
    (input : List E) (initial : S) (I : S → Prop) (C : ℕ)
    (hi : I initial) (hs : ∀ s e, I s → I (step s e))
    (hc : ∀ s, I s → cells s ≤ C) :
    I (readPass step cells input initial).state ∧
      (readPass step cells input initial).peakCells ≤ C := by
  have h (xs : List E) (m : Metered S) (hm : I m.state) (hp : m.peakCells ≤ C) :
      I (xs.foldl (readEdge step cells) m).state ∧
        (xs.foldl (readEdge step cells) m).peakCells ≤ C := by
    induction xs generalizing m with
    | nil => exact ⟨hm, hp⟩
    | cons e es ih =>
        have hnext := hs m.state e hm
        exact ih (readEdge step cells m e) hnext
          (max_le hp (hc _ hnext))
  exact h input ⟨initial, 0, cells initial⟩ hi (hc _ hi)

end StreamingReachability.Streaming
