module

public import StreamingReachability.Hopset.AncestorPruning

@[expose] public section

namespace StreamingReachability.Hopset.Following.PieceTree

open scoped Classical BigOperators

noncomputable section

variable {A : Type*}

def height : PieceTree A → ℕ
  | .bridge _ | .late _ | .marked _ => 0
  | .branch _ count children => 1 + (Finset.univ : Finset (Fin count)).sup (fun i => height (children i))

def size : PieceTree A → ℕ
  | .bridge _ | .late _ | .marked _ => 1
  | .branch _ count children => 1 + ∑ i : Fin count, size (children i)

def hopTally (bridgeHops lateHops : A → ℕ) : PieceTree A → ℕ
  | .bridge a => bridgeHops a
  | .late a => lateHops a
  | .marked _ => 2
  | .branch _ count children => 2 * count + ∑ i : Fin count, hopTally bridgeHops lateHops (children i)

def profileSum (f : ℕ → ℝ) : PieceTree A → ℕ → ℝ
  | .bridge _, q | .late _, q | .marked _, q => f q
  | .branch _ count children, q => f q + ∑ i : Fin count, profileSum f (children i) (q + 1)

def markSum (f : A → ℝ) : PieceTree A → ℝ
  | .bridge _ | .late _ => 0
  | .marked a => f a
  | .branch _ count children => ∑ i : Fin count, markSum f (children i)

def Leveled (level : A → ℕ) : PieceTree A → ℕ → Prop
  | .bridge a, q | .late a, q | .marked a, q => level a = q
  | .branch a count children, q => level a = q ∧ ∀ i : Fin count, Leveled level (children i) (q + 1)

theorem size_prune_le (T : PieceTree A) (L : ℕ) : (T.prune L).size ≤ T.size := by
  induction T with
  | bridge a => exact le_rfl
  | late a => exact le_rfl
  | marked a => exact le_rfl
  | branch a count children ih =>
      by_cases hm : (PieceTree.branch a count children).bridgeAt L
      · simp only [prune, hm, ↓reduceIte, size]
        exact Nat.le_add_right _ _
      · simp only [prune, hm, ↓reduceIte, size]
        exact Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => ih i)) 1

theorem hopTally_bound (T : PieceTree A) (bridgeHops lateHops : A → ℕ)
    (hnobridge : ∀ d, ¬ T.bridgeAt d) :
    T.hopTally bridgeHops lateHops + 2 ≤ 4 * T.size + T.lateWeight lateHops := by
  induction T with
  | bridge a => exact False.elim (hnobridge 0 trivial)
  | late a => simp only [hopTally, size, lateWeight]; omega
  | marked a => simp only [hopTally, size, lateWeight]; omega
  | branch a count children ih =>
      have hchild (i : Fin count) : ∀ d, ¬ (children i).bridgeAt d := by
        intro d hd
        exact hnobridge (d + 1) ⟨i, hd⟩
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin count))) (fun i _ => ih i (hchild i))
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_id, ← Finset.mul_sum] at hs
      simp only [hopTally, size, lateWeight]
      omega

theorem profileSum_nonneg (T : PieceTree A) (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (q : ℕ) :
    0 ≤ T.profileSum f q := by
  induction T generalizing q with
  | bridge a => exact hf q
  | late a => exact hf q
  | marked a => exact hf q
  | branch a count children ih =>
      exact add_nonneg (hf q) (Finset.sum_nonneg (fun i _ => ih i (q + 1)))

theorem markSum_prune_le_profile (T : PieceTree A) (L : ℕ) (level : A → ℕ)
    (f : ℕ → ℝ) (hf : ∀ q, 0 ≤ f q) (q : ℕ) (hl : T.Leveled level q) :
    (T.prune L).markSum (fun a => f (level a)) ≤ T.profileSum f q := by
  induction T generalizing q with
  | bridge a => simpa only [prune, markSum, profileSum] using hf q
  | late a => simpa only [prune, markSum, profileSum] using hf q
  | marked a =>
      change level a = q at hl
      simpa only [prune, markSum, profileSum, hl] using le_rfl (a := f q)
  | branch a count children ih =>
      by_cases hm : (PieceTree.branch a count children).bridgeAt L
      · simp only [prune, hm, ↓reduceIte, markSum, profileSum, hl.1]
        exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => profileSum_nonneg _ f hf (q + 1)))
      · simp only [prune, hm, ↓reduceIte, markSum, profileSum]
        exact (Finset.sum_le_sum (fun i _ => ih i (q + 1) (hl.2 i))).trans
          (le_add_of_nonneg_left (hf q))

theorem profileSum_counts (T : PieceTree A) (f : ℕ → ℝ) (q h : ℕ) (hh : T.height ≤ h) :
    T.profileSum f q = ∑ d ∈ Finset.range (h + 1), f (q + d) * (T.countAt d : ℝ) := by
  induction T generalizing q h with
  | bridge a =>
      cases h with
      | zero => simp [profileSum, countAt]
      | succ h =>
          conv_rhs => rw [Finset.sum_range_succ']
          simp only [profileSum, countAt, Nat.add_zero, Nat.cast_zero, Nat.cast_one, mul_zero,
            mul_one, Finset.sum_const_zero, zero_add]
  | late a =>
      cases h with
      | zero => simp [profileSum, countAt]
      | succ h =>
          conv_rhs => rw [Finset.sum_range_succ']
          simp only [profileSum, countAt, Nat.add_zero, Nat.cast_zero, Nat.cast_one, mul_zero,
            mul_one, Finset.sum_const_zero, zero_add]
  | marked a =>
      cases h with
      | zero => simp [profileSum, countAt]
      | succ h =>
          conv_rhs => rw [Finset.sum_range_succ']
          simp only [profileSum, countAt, Nat.add_zero, Nat.cast_zero, Nat.cast_one, mul_zero,
            mul_one, Finset.sum_const_zero, zero_add]
  | branch a count children ih =>
      cases h with
      | zero => simp only [height] at hh; omega
      | succ h =>
          have hchild (i : Fin count) : (children i).height ≤ h := by
            have hm := Finset.le_sup (s := (Finset.univ : Finset (Fin count)))
              (f := fun i => (children i).height) (Finset.mem_univ i)
            change 1 + _ ≤ h + 1 at hh
            omega
          have hs : (∑ i : Fin count, (children i).profileSum f (q + 1)) =
              ∑ i : Fin count, ∑ d ∈ Finset.range (h + 1),
                f (q + 1 + d) * ((children i).countAt d : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            exact ih i (q + 1) h (hchild i)
          rw [profileSum, hs]
          conv_rhs => rw [Finset.sum_range_succ']
          simp only [countAt, Nat.add_zero, Nat.cast_one, mul_one]
          simp_rw [Nat.cast_sum, Finset.mul_sum]
          rw [Finset.sum_comm]
          have hindex (d : ℕ) : f (q + 1 + d) = f (q + (d + 1)) := by congr 1; omega
          simp_rw [hindex]
          exact add_comm _ _

theorem size_as_profile (T : PieceTree A) (q : ℕ) :
    (T.size : ℝ) = T.profileSum (fun _ => 1) q := by
  induction T generalizing q with
  | bridge a => simp only [size, profileSum, Nat.cast_one]
  | late a => simp only [size, profileSum, Nat.cast_one]
  | marked a => simp only [size, profileSum, Nat.cast_one]
  | branch a count children ih =>
      simp only [size, profileSum, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => ih i (q + 1))

theorem size_counts (T : PieceTree A) (h : ℕ) (hh : T.height ≤ h) :
    (T.size : ℝ) = ∑ d ∈ Finset.range (h + 1), (T.countAt d : ℝ) := by
  rw [size_as_profile T 0, profileSum_counts T (fun _ => 1) 0 h hh]
  simp only [one_mul]

end

end StreamingReachability.Hopset.Following.PieceTree
