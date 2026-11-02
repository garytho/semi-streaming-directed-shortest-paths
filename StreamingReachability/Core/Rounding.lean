module

public import StreamingReachability.Core.BlockSearch

@[expose] public section

namespace StreamingReachability.Core

def ceilNat (A w : ℕ) : ℕ := (w + A - 1) / A

def roundDistance (A : ℕ) : Distance → Distance := WithTop.map (ceilNat A)

theorem ceilNat_le_iff {A w r : ℕ} (hA : 0 < A) :
    ceilNat A w ≤ r ↔ w ≤ A * r := by
  rw [ceilNat, Nat.div_le_iff_le_mul hA, Nat.mul_comm r A]
  omega

@[simp] theorem ceilNat_zero {A : ℕ} (hA : 0 < A) : ceilNat A 0 = 0 := by
  exact Nat.eq_zero_of_le_zero ((ceilNat_le_iff hA).mpr (by simp))

theorem ceilNat_mono {A : ℕ} (hA : 0 < A) {u v : ℕ} (huv : u ≤ v) :
    ceilNat A u ≤ ceilNat A v := by
  apply (ceilNat_le_iff hA).mpr
  exact huv.trans ((ceilNat_le_iff hA).mp le_rfl)

theorem ceilNat_add_multiple {A : ℕ} (hA : 0 < A) (d w : ℕ) :
    ceilNat A (A * d + w) = d + ceilNat A w := by
  have he : A * d + w + A - 1 = (w + A - 1) + A * d := by omega
  rw [ceilNat, he, Nat.add_mul_div_left _ d hA]
  exact Nat.add_comm _ _

@[simp] theorem roundDistance_top (A : ℕ) : roundDistance A ⊤ = ⊤ := rfl

@[simp] theorem roundDistance_coe (A w : ℕ) :
    roundDistance A (w : Distance) = (ceilNat A w : Distance) := rfl

theorem roundDistance_le_iff {A r : ℕ} (hA : 0 < A) (w : Distance) :
    roundDistance A w ≤ (r : Distance) ↔ w ≤ ((A * r : ℕ) : Distance) := by
  induction w using WithTop.recTopCoe with
  | top =>
      change (⊤ : Distance) ≤ (r : Distance) ↔ (⊤ : Distance) ≤ ((A * r : ℕ) : Distance)
      simp only [top_le_iff, WithTop.natCast_ne_top]
  | coe w =>
      change (ceilNat A w : WithTop ℕ) ≤ (r : WithTop ℕ) ↔
        (w : WithTop ℕ) ≤ ((A * r : ℕ) : WithTop ℕ)
      norm_cast
      exact ceilNat_le_iff hA

theorem roundDistance_mono {A : ℕ} (hA : 0 < A) :
    Monotone (roundDistance A) := by
  intro u v huv
  induction u using WithTop.recTopCoe with
  | top =>
      have hv : v = ⊤ := top_le_iff.mp huv
      simp [hv]
  | coe u =>
      induction v using WithTop.recTopCoe with
      | top => exact le_top
      | coe v => exact WithTop.coe_le_coe.mpr (ceilNat_mono hA (WithTop.coe_le_coe.mp huv))

theorem roundDistance_add_multiple {A : ℕ} (hA : 0 < A) (d : ℕ) (w : Distance) :
    roundDistance A (((A * d : ℕ) : Distance) + w) =
      (d : Distance) + roundDistance A w := by
  induction w using WithTop.recTopCoe with
  | top => simp
  | coe w =>
      change (ceilNat A (A * d + w) : WithTop ℕ) =
        ((d + ceilNat A w : ℕ) : WithTop ℕ)
      exact congrArg (fun k : ℕ => (k : Distance)) (ceilNat_add_multiple hA d w)

theorem roundDistance_inf {V : Type*} (A : ℕ) (hA : 0 < A)
    (S : Finset V) (f : V → Distance) :
    roundDistance A (S.inf f) = S.inf (fun v => roundDistance A (f v)) := by
  by_cases hs : S.Nonempty
  · obtain ⟨v, hv, he⟩ := Finset.exists_mem_eq_inf S hs f
    apply le_antisymm
    · apply Finset.le_inf
      intro u hu
      exact roundDistance_mono hA (Finset.inf_le hu)
    · rw [he]
      exact Finset.inf_le hv
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

noncomputable def queryGraph {n : ℕ} (edges : List (StoredEdges.Edge n))
    (blocks : List (Finset (Fin n))) (A : ℕ) : Graph (Fin n) :=
  fun u v => min (roundDistance A (StoredEdges.graphOfEdges edges u v))
    (blocks.toFinset.inf fun B =>
      if u ∈ B ∧ v ∈ B ∧ u ≠ v
      then roundDistance A ((BlockSearch.blockGraph edges B).dist u v) else ⊤)

end StreamingReachability.Core
