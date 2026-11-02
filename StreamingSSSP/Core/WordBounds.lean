module

public import StreamingSSSP.Core.BatchSearch

@[expose] public section

namespace StreamingSSSP.Core.WordBounds

open StoredEdges

def Bounded (K : ℕ) (d : Distance) : Prop := d = ⊤ ∨ d ≤ (K : Distance)

theorem min_bounded {K : ℕ} {a b : Distance} (ha : Bounded K a) (hb : Bounded K b) :
    Bounded K (min a b) := by
  by_cases hab : a ≤ b
  · simpa only [min_eq_left hab] using ha
  · simpa only [min_eq_right (le_of_not_ge hab)] using hb

theorem bounded_mono {K L : ℕ} (h : K ≤ L) {d : Distance} (hd : Bounded K d) :
    Bounded L d := by
  rcases hd with ht | hle
  · exact Or.inl ht
  · exact Or.inr (hle.trans (WithTop.coe_le_coe.mpr h))

theorem add_bounded {L W w : ℕ} {d : Distance} (hd : Bounded L d) (hw : w ≤ W) :
    Bounded (L + W) (d + (w : Distance)) := by
  rcases hd with ht | hle
  · exact Or.inl (by simp [ht])
  · right
    change d + (w : Distance) ≤ (L : Distance) + (W : Distance)
    exact add_le_add hle (WithTop.coe_le_coe.mpr hw)

variable {n : ℕ}

theorem relax_bounded (edges : List (Edge n)) (old next : DistanceArray n) (L W : ℕ)
    (ho : ∀ v, Bounded L (old.get v))
    (hn : ∀ v, Bounded (L + W) (next.get v))
    (hw : ∀ e ∈ edges, e.weight ≤ W) :
    ∀ v, Bounded (L + W) ((relaxEdges edges old next).get v) := by
  induction edges generalizing next with
  | nil => exact hn
  | cons e edges ih =>
      apply ih (relaxEdge old next e)
      · intro v
        rw [relaxEdge_get]
        split_ifs
        · exact min_bounded (hn v) (add_bounded (ho e.source) (hw e (by simp)))
        · exact hn v
      · intro f hf
        exact hw f (by simp [hf])

theorem rounds_bounded (edges : List (Edge n)) (initial : DistanceArray n) (L W k : ℕ)
    (hi : ∀ v, Bounded L (initial.get v))
    (hw : ∀ e ∈ edges, e.weight ≤ W) :
    ∀ v, Bounded (L + k * W) ((runRounds edges k initial).get v) := by
  induction k with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero, runRounds] using hi
  | succ k ih =>
      rw [runRounds_succ]
      have h := relax_bounded edges (runRounds edges k initial) (runRounds edges k initial)
        (L + k * W) W ih
        (fun v => bounded_mono (Nat.le_add_right _ _) (ih v)) hw
      simpa only [Nat.succ_mul, Nat.add_assoc, relaxRound] using h

theorem skeleton_weights (hn : 0 < n) (B known : Finset (Fin n)) (τ W : ℕ)
    (input : List (Edge n)) (hw : ∀ e ∈ input, e.weight ≤ W) :
    ∀ e ∈ Skeleton.build hn B known τ input, e.weight ≤ W := by
  intro e he
  exact hw e (Skeleton.retained hn B known τ input he).1

theorem block_labels (hn : 0 < n) (B known : Finset (Fin n)) (τ A R W : ℕ)
    (input : List (Edge n)) (initial : DistanceArray n)
    (hi : ∀ v, Bounded (A * R) (initial.get v))
    (hw : ∀ e ∈ input, e.weight ≤ W) (v : Fin n) :
    Bounded (A * R + n * W) ((BlockSearch.labels hn B known τ initial input).get v) := by
  have h := rounds_bounded (Skeleton.build hn B known τ input) initial (A * R) W
    (n - 1) hi (skeleton_weights hn B known τ W input hw) v
  exact bounded_mono (Nat.add_le_add_left (Nat.mul_le_mul_right W (Nat.sub_le n 1)) _) h

theorem skeleton_keys (_hn : 0 < n) (B known : Finset (Fin n)) (τ W : ℕ)
    (input : List (Edge n)) (hw : ∀ e ∈ input, e.weight ≤ W)
    {a : Fin n} {k : ℕ} (hk : k ∈ TopRows.build n τ (Skeleton.keys B known a input)) :
    k < n * W + n := by
  have hs := (TopRows.build_valid n τ (Skeleton.keys B known a input)).retained hk
  obtain ⟨e, he, _, hkey⟩ :=
    (Skeleton.mem_keys B known a input k).mp (List.mem_toFinset.mp hs)
  have hwe := Nat.mul_le_mul_right n (hw e he)
  rw [← hkey, Skeleton.key]
  nlinarith only [hwe, e.target.isLt]

def bitLength (w : ℕ) : ℕ := Nat.log 2 (w + 1) + 1

theorem bitLength_mono {u v : ℕ} (h : u ≤ v) : bitLength u ≤ bitLength v := by
  apply Nat.add_le_add_right
  exact Nat.log_mono_right (Nat.add_le_add_right h 1)

theorem finite_label_bits (A R n W : ℕ) {d : Distance} (hd : Bounded (A * R + n * W) d)
    (hfinite : d ≠ ⊤) :
    bitLength (d.untopD 0) ≤ bitLength (n + A * R + n * W) := by
  rcases hd with ht | hle
  · exact False.elim (hfinite ht)
  apply bitLength_mono
  have hnat : d.untopD 0 ≤ A * R + n * W := by
    induction d using WithTop.recTopCoe with
    | top => contradiction
    | coe k => exact WithTop.coe_le_coe.mp hle
  omega

end StreamingSSSP.Core.WordBounds
