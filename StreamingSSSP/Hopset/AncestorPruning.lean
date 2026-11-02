module

public import StreamingSSSP.Probability

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical BigOperators

noncomputable section

inductive PieceTree (A : Type*) where
  | bridge (value : A)
  | late (value : A)
  | marked (value : A)
  | branch (value : A) (count : ℕ) (children : Fin count → PieceTree A)

namespace PieceTree

variable {A : Type*}

def value : PieceTree A → A
  | .bridge a | .late a | .marked a | .branch a _ _ => a

def bridgeAt : PieceTree A → ℕ → Prop
  | .bridge _, 0 => True
  | .late _, _ | .marked _, _ => False
  | .branch _ _ _, 0 => False
  | .bridge _, _ + 1 => False
  | .branch _ count children, d + 1 => ∃ i : Fin count, bridgeAt (children i) d

def countAt : PieceTree A → ℕ → ℕ
  | _, 0 => 1
  | .bridge _, _ + 1 | .late _, _ + 1 | .marked _, _ + 1 => 0
  | .branch _ count children, d + 1 => ∑ i : Fin count, countAt (children i) d

def lateWeight (f : A → ℕ) : PieceTree A → ℕ
  | .bridge _ | .marked _ => 0
  | .late a => f a
  | .branch _ count children => ∑ i : Fin count, lateWeight f (children i)

def prune (L : ℕ) : PieceTree A → PieceTree A
  | .bridge a => .bridge a
  | .late a => .late a
  | .marked a => .marked a
  | .branch a count children =>
      if bridgeAt (.branch a count children) L then .marked a
      else .branch a count (fun i => prune L (children i))

theorem bridgeAt_prune (L : ℕ) (T : PieceTree A) (d : ℕ) :
    bridgeAt (T.prune L) d → bridgeAt T d := by
  induction T generalizing d with
  | bridge a => exact fun h => h
  | late a => exact fun h => h
  | marked a => exact fun h => h
  | branch a count children ih =>
      by_cases hm : bridgeAt (.branch a count children) L
      · simp only [prune, hm, ↓reduceIte, bridgeAt, false_implies]
      · cases d with
        | zero => simp only [prune, hm, ↓reduceIte, bridgeAt, imp_self]
        | succ d =>
            simp only [prune, hm, ↓reduceIte, bridgeAt]
            rintro ⟨i, hi⟩
            exact ⟨i, ih i d hi⟩

/-- Every surviving bridge is shallower than the ancestor look-back.
Consequently, a global star handles all surviving bridge leaves. -/
theorem prune_bridge_depth_lt (L : ℕ) (hL : 0 < L) (T : PieceTree A) (d : ℕ) :
    bridgeAt (T.prune L) d → d < L := by
  induction T generalizing d with
  | bridge a =>
      cases d with
      | zero => intro _; exact hL
      | succ d => simp only [prune, bridgeAt, false_implies]
  | late a => simp only [prune, bridgeAt, false_implies]
  | marked a => simp only [prune, bridgeAt, false_implies]
  | branch a count children ih =>
      by_cases hm : bridgeAt (.branch a count children) L
      · simp only [prune, hm, ↓reduceIte, bridgeAt, false_implies]
      · cases d with
        | zero => simp only [prune, hm, ↓reduceIte, bridgeAt, false_implies]
        | succ d =>
            simp only [prune, hm, ↓reduceIte, bridgeAt]
            rintro ⟨i, hi⟩
            have hd := ih i d hi
            have hOriginal := bridgeAt_prune L (children i) d hi
            by_contra hn
            have he : L = d + 1 := by omega
            apply hm
            rw [he]
            exact ⟨i, hOriginal⟩

theorem prune_no_bridge (L : ℕ) (hL : 0 < L) (T : PieceTree A)
    (hglobal : ∀ d < L, ¬ bridgeAt T d) : ∀ d, ¬ bridgeAt (T.prune L) d := by
  intro d hd
  exact hglobal d (prune_bridge_depth_lt L hL T d hd) (bridgeAt_prune L T d hd)

theorem countAt_prune_le (L : ℕ) (T : PieceTree A) (d : ℕ) : countAt (T.prune L) d ≤ countAt T d := by
  induction T generalizing d with
  | bridge a => exact le_rfl
  | late a => exact le_rfl
  | marked a => exact le_rfl
  | branch a count children ih =>
      by_cases hm : bridgeAt (.branch a count children) L
      · cases d <;> simp only [prune, hm, ↓reduceIte, countAt, le_refl, Nat.zero_le]
      · cases d with
        | zero => simp only [prune, hm, ↓reduceIte, countAt, le_refl]
        | succ d =>
            simp only [prune, hm, ↓reduceIte, countAt]
            exact Finset.sum_le_sum (fun i _ => ih i d)

theorem lateWeight_prune_le (L : ℕ) (T : PieceTree A) (f : A → ℕ) :
    lateWeight f (T.prune L) ≤ lateWeight f T := by
  induction T with
  | bridge a => exact le_rfl
  | late a => exact le_rfl
  | marked a => exact le_rfl
  | branch a count children ih =>
      by_cases hm : bridgeAt (.branch a count children) L
      · simp only [prune, hm, ↓reduceIte, lateWeight, Nat.zero_le]
      · simp only [prune, hm, ↓reduceIte, lateWeight]
        exact Finset.sum_le_sum (fun i _ => ih i)

end PieceTree

end

end StreamingSSSP.Hopset.Following
