module

public import StreamingReachability.Exact.Paths

@[expose] public section

namespace StreamingReachability.Exact

def binIndex (width shift value : ℕ) : ℕ := (value + shift) / width

def binBase (width shift value : ℕ) : ℤ :=
  (binIndex width shift value * width : ℕ) - (shift : ℤ)

def residue (width shift value : ℕ) : ℕ := (value + shift) % width

theorem bin_decomposition (width shift value : ℕ) :
    binBase width shift value + residue width shift value = value := by
  have h := Nat.mod_add_div (value + shift) width
  have h' : (((value + shift) % width : ℕ) : ℤ) +
      ((width * ((value + shift) / width) : ℕ) : ℤ) = (value : ℤ) + shift := by
    exact_mod_cast h
  unfold binBase binIndex residue
  rw [Nat.mul_comm] at h'
  nlinarith [h']

theorem residue_lt {width : ℕ} (hw : 0 < width) (shift value : ℕ) :
    residue width shift value < width := Nat.mod_lt _ hw

theorem binBase_eq {width shift x y : ℕ}
    (h : binIndex width shift x = binIndex width shift y) :
    binBase width shift x = binBase width shift y := by
  simp only [binBase, h]

/-- Two half-width shifted partitions cover every short interval. -/
theorem two_shift_cover (center K : ℕ) (hK : 0 < K) :
    ∃ shift : ℕ, (shift = 0 ∨ shift = 4 * K) ∧
      ∀ x : ℕ, (center : ℤ) - K ≤ x → (x : ℤ) ≤ center + K →
        binIndex (8 * K) shift x = binIndex (8 * K) shift center := by
  let q := center / (8 * K)
  let r := center % (8 * K)
  have hr : r < 8 * K := Nat.mod_lt _ (by omega)
  have he : r + (8 * K) * q = center := Nat.mod_add_div _ _
  have hdiv (x sh j : ℕ)
      (hl : (8 * K) * j ≤ x + sh)
      (hu : x + sh < (8 * K) * (j + 1)) :
      binIndex (8 * K) sh x = j := by
    unfold binIndex
    apply Nat.le_antisymm
    · apply Nat.lt_succ_iff.mp
      apply (Nat.div_lt_iff_lt_mul (by omega)).2
      nlinarith
    · apply (Nat.le_div_iff_mul_le (by omega)).2
      nlinarith
  by_cases hlo : r < 2 * K
  · refine ⟨4 * K, Or.inr rfl, ?_⟩
    intro x hxl hxu
    have hxl' : center ≤ x + K := by omega
    have hxu' : x ≤ center + K := by omega
    rw [hdiv x (4 * K) q (by nlinarith) (by nlinarith),
      hdiv center (4 * K) q (by nlinarith) (by nlinarith)]
  · by_cases hhi : 6 * K ≤ r
    · refine ⟨4 * K, Or.inr rfl, ?_⟩
      intro x hxl hxu
      have hxl' : center ≤ x + K := by omega
      have hxu' : x ≤ center + K := by omega
      rw [hdiv x (4 * K) (q + 1) (by nlinarith) (by nlinarith),
        hdiv center (4 * K) (q + 1) (by nlinarith) (by nlinarith)]
    · refine ⟨0, Or.inl rfl, ?_⟩
      intro x hxl hxu
      have hxl' : center ≤ x + K := by omega
      have hxu' : x ≤ center + K := by omega
      rw [hdiv x 0 q (by nlinarith) (by nlinarith),
        hdiv center 0 q (by nlinarith) (by nlinarith)]

end StreamingReachability.Exact
