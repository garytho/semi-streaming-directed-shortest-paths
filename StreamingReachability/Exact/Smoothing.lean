module

public import StreamingReachability.Exact.LevelGraph

@[expose] public section

namespace StreamingReachability.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

/-- Accuracy of an actual integer-valued oracle answer. The relative error is
`1 / denominator`. Flooring a real-valued approximation has this property. -/
def IntegerApprox (G : Graph V) (source : V) (denominator : ℕ)
    (answer : V → ℕ) : Prop :=
  ∀ v (d : ℕ), G.dist source v = d →
    d ≤ answer v ∧ denominator * answer v ≤ (denominator + 1) * d

def floorAnswers (answer : V → ℚ) : V → ℕ := fun v => ⌊answer v⌋₊

theorem floor_preserves_accuracy (G : Graph V) (source : V) (denominator : ℕ)
    (answer : V → ℚ)
    (hanswer : ∀ v (d : ℕ), G.dist source v = d →
      (d : ℚ) ≤ answer v ∧ (denominator : ℚ) * answer v ≤ (denominator + 1 : ℚ) * d) :
    IntegerApprox G source denominator (floorAnswers answer) := by
  intro v d hd
  have ha := hanswer v d hd
  have hn : 0 ≤ answer v := (Nat.cast_nonneg d).trans ha.1
  refine ⟨Nat.le_floor ha.1, ?_⟩
  have hf := Nat.floor_le hn
  have hm := mul_le_mul_of_nonneg_left hf (show (0 : ℚ) ≤ denominator by positivity)
  have hh : (denominator : ℚ) * ⌊answer v⌋₊ ≤ (denominator + 1 : ℚ) * d :=
    hm.trans ha.2
  exact_mod_cast hh

def partialLabels (labels : V → ℕ) (K : ℕ) (answer₀ answer₁ : Option V → ℕ) :
    V → ℕ :=
  fun v => min (labels v)
    (min (binBase (8 * K) 0 (labels v) + answer₀ (some v)).toNat
      (binBase (8 * K) (4 * K) (labels v) + answer₁ (some v)).toNat)

theorem partialLabels_le (labels : V → ℕ) (K : ℕ)
    (answer₀ answer₁ : Option V → ℕ) (v : V) :
    partialLabels labels K answer₀ answer₁ v ≤ labels v := min_le_left _ _

theorem partialLabels_source (labels : V → ℕ) (K : ℕ)
    (answer₀ answer₁ : Option V → ℕ) {s : V} (hs : labels s = 0) :
    partialLabels labels K answer₀ answer₁ s = 0 :=
  Nat.eq_zero_of_le_zero (hs ▸ partialLabels_le labels K answer₀ answer₁ s)

theorem partialLabels_envelope_lower (G : Graph V) (labels : V → ℕ)
    (slope K denominator : ℕ) (answer₀ answer₁ : Option V → ℕ)
    (h₀ : IntegerApprox (levelGraph G labels slope (8 * K) 0) none denominator answer₀)
    (h₁ : IntegerApprox (levelGraph G labels slope (8 * K) (4 * K))
      none denominator answer₁) (v : V) :
    envelope G labels slope v ≤ partialLabels labels K answer₀ answer₁ v := by
  have hl (shift : ℕ) (answer : Option V → ℕ)
      (h : IntegerApprox (levelGraph G labels slope (8 * K) shift) none denominator answer) :
      envelope G labels slope v ≤
        (binBase (8 * K) shift (labels v) + answer (some v)).toNat := by
    obtain ⟨d, hd⟩ := level_dist_finite G labels slope (8 * K) shift v
    have he := envelope_le_level G labels slope (8 * K) shift hd
    have ha := (h (some v) d hd).1
    have hn : (envelope G labels slope v : ℤ) ≤
        binBase (8 * K) shift (labels v) + answer (some v) := by omega
    simpa using Int.toNat_le_toNat hn
  exact le_min (envelope_le_label G labels slope v)
    (le_min (hl 0 answer₀ h₀) (hl (4 * K) answer₁ h₁))

theorem smoothing_witness_cover (G : Graph V) (labels : V → ℕ)
    (slope error M : ℕ) (herror : 0 < error) (hM : slope + 1 ≤ M)
    (hsmooth : AdditivelySmooth G labels slope (2 * error))
    {u v : V} {d : ℕ} (hd : G.dist u v = d)
    (he : envelope G labels (slope + 1) v = labels u + (slope + 1) * d) :
    d ≤ 2 * error ∧
      ∃ shift : ℕ, (shift = 0 ∨ shift = 4 * (M * (2 * error))) ∧
        ∀ x ∈ (shortestRoute G hd).vertices,
          binIndex (8 * (M * (2 * error))) shift (labels x) =
            binIndex (8 * (M * (2 * error))) shift (labels u) := by
  have henv := envelope_le_label G labels (slope + 1) v
  have hold := hsmooth u v d hd
  push_cast at hold
  have hdle : d ≤ 2 * error := by
    have hh : labels u + (slope + 1) * d ≤ labels v := he ▸ henv
    have hh' : (labels u : ℤ) + (slope + 1 : ℤ) * d ≤ labels v := by
      exact_mod_cast hh
    have hdn : (d : ℤ) ≤ 2 * error := by nlinarith
    exact_mod_cast hdn
  refine ⟨hdle, ?_⟩
  let K := M * (2 * error)
  have hK : 0 < K := Nat.mul_pos (by omega) (by omega)
  obtain ⟨shift, hs, hcover⟩ := two_shift_cover (labels u) K hK
  refine ⟨shift, hs, ?_⟩
  intro x hx
  obtain ⟨a, b, ha, hb, hac, hbc⟩ := route_vertex_bounds (shortestRoute G hd) hx
  obtain ⟨j, hj, hjle⟩ := finite_of_le ha
  obtain ⟨k, hk, hkle⟩ := finite_of_le hb
  have hux := hsmooth u x j hj
  have hxv := hsmooth x v k hk
  have haj : j ≤ d := hjle.trans hac
  have hbk : k ≤ d := hkle.trans hbc
  have hbase : labels u ≤ labels v := by
    have hh : labels u + (slope + 1) * d ≤ labels v := he ▸ henv
    omega
  have hgap : slope * d + 2 * error ≤ K := by
    dsimp [K]
    nlinarith [Nat.mul_le_mul_left slope hdle, Nat.mul_le_mul_right (2 * error) hM]
  have hpj : (slope : ℤ) * j ≤ slope * d := by
    exact_mod_cast Nat.mul_le_mul_left slope haj
  have hpk : (slope : ℤ) * k ≤ slope * d := by
    exact_mod_cast Nat.mul_le_mul_left slope hbk
  have hgap' : (slope : ℤ) * d + 2 * error ≤ K := by exact_mod_cast hgap
  apply hcover (labels x) <;> omega

theorem partialLabels_envelope_upper (G : Graph V) (labels : V → ℕ)
    (slope error M : ℕ) (herror : 0 < error) (hM : slope + 1 ≤ M)
    (hsmooth : AdditivelySmooth G labels slope (2 * error))
    (answer₀ answer₁ : Option V → ℕ)
    (h₀ : IntegerApprox (levelGraph G labels (slope + 1) (8 * (M * (2 * error))) 0)
      none (100 * M) answer₀)
    (h₁ : IntegerApprox
      (levelGraph G labels (slope + 1) (8 * (M * (2 * error))) (4 * (M * (2 * error))))
      none (100 * M) answer₁) (v : V) :
    partialLabels labels (M * (2 * error)) answer₀ answer₁ v ≤
      envelope G labels (slope + 1) v + error := by
  have hMpos : 0 < M := by omega
  have hKpos : 0 < M * (2 * error) := by positivity
  obtain ⟨u, d, hd, he⟩ := envelope_witness G labels (slope + 1) v
  obtain ⟨hdle, shift, hs, hcover⟩ :=
    smoothing_witness_cover G labels slope error M herror hM hsmooth hd he
  let K := M * (2 * error)
  let answer := if shift = 0 then answer₀ else answer₁
  have haccurate : IntegerApprox (levelGraph G labels (slope + 1) (8 * K) shift)
      none (100 * M) answer := by
    rcases hs with hs | hs
    · subst shift
      simpa [answer] using h₀
    · have hne : shift ≠ 0 := by
        rw [hs]
        positivity
      dsimp only [answer]
      rw [if_neg hne, hs]
      exact h₁
  have hdistle := level_path_upper G labels (slope + 1) (8 * K) shift
    (binIndex (8 * K) shift (labels u)) (shortestRoute G hd) hcover
  obtain ⟨j, hj, hjle⟩ := finite_of_le hdistle
  have hacc := (haccurate (some v) j hj).2
  have hres : residue (8 * K) shift (labels u) < 8 * K :=
    residue_lt (by dsimp [K]; positivity) _ _
  have hvmem := List.mem_of_getLast? (shortestRoute G hd).endpoints.2
  have hbin := hcover v hvmem
  have hbase := binBase_eq hbin
  have hdecomp := bin_decomposition (8 * K) shift (labels u)
  have hpath : (slope + 1) * d ≤ M * (2 * error) :=
    (Nat.mul_le_mul_right d hM).trans (Nat.mul_le_mul_left M hdle)
  have hcost : residue (8 * K) shift (labels u) + (slope + 1) * d ≤ 9 * K := by
    dsimp [K] at *
    omega
  have hacc' : (100 * M : ℤ) * answer (some v) ≤ (100 * M + 1 : ℤ) * j := by
    exact_mod_cast hacc
  have hjle' : (j : ℤ) ≤ residue (8 * K) shift (labels u) + (slope + 1 : ℤ) * d := by
    exact_mod_cast hjle
  have hcost' : (residue (8 * K) shift (labels u) : ℤ) +
      (slope + 1 : ℤ) * d ≤ 9 * K := by exact_mod_cast hcost
  have he' : (envelope G labels (slope + 1) v : ℤ) =
      labels u + (slope + 1 : ℤ) * d := by exact_mod_cast he
  have hK' : (K : ℤ) = M * (2 * error) := by dsimp [K]
  have hraw : binBase (8 * K) shift (labels v) + answer (some v) ≤
      (envelope G labels (slope + 1) v : ℤ) + error := by
    rw [hbase]
    have hmult : (100 * M : ℤ) *
        (answer (some v) -
          (residue (8 * K) shift (labels u) + (slope + 1 : ℤ) * d)) ≤
        residue (8 * K) shift (labels u) + (slope + 1 : ℤ) * d := by
      nlinarith
    nlinarith
  have hnat : (binBase (8 * K) shift (labels v) + answer (some v)).toNat ≤
      envelope G labels (slope + 1) v + error := by
    apply Int.toNat_le.mpr
    simpa using hraw
  rcases hs with hs | hs
  · subst shift
    exact (le_trans (min_le_right _ _) (min_le_left _ _)).trans (by
      simpa [answer] using hnat)
  · have hne : shift ≠ 0 := by rw [hs]; positivity
    simp only [answer, if_neg hne, hs] at hnat
    exact (le_trans (min_le_right _ _) (min_le_right _ _)).trans (by
      exact hnat)

/-- A complete partial-smoothing round: the only correctness assumptions are the
two actual approximation answers, not a smoothness certificate. -/
theorem partial_smoothing (G : Graph V) (labels : V → ℕ)
    (slope error M : ℕ) (herror : 0 < error) (hM : slope + 1 ≤ M)
    (hsmooth : AdditivelySmooth G labels slope (2 * error))
    (answer₀ answer₁ : Option V → ℕ)
    (h₀ : IntegerApprox (levelGraph G labels (slope + 1) (8 * (M * (2 * error))) 0)
      none (100 * M) answer₀)
    (h₁ : IntegerApprox
      (levelGraph G labels (slope + 1) (8 * (M * (2 * error))) (4 * (M * (2 * error))))
      none (100 * M) answer₁) :
    AdditivelySmooth G (partialLabels labels (M * (2 * error)) answer₀ answer₁)
      (slope + 1) error := by
  intro u v d hd
  have hupper := partialLabels_envelope_upper G labels slope error M
    herror hM hsmooth answer₀ answer₁ h₀ h₁ v
  have hlower := partialLabels_envelope_lower G labels (slope + 1) (M * (2 * error))
    (100 * M) answer₀ answer₁ h₀ h₁ u
  have hs := envelope_smooth G labels (slope + 1) hd
  have hout : partialLabels labels (M * (2 * error)) answer₀ answer₁ v ≤
      partialLabels labels (M * (2 * error)) answer₀ answer₁ u + (slope + 1) * d + error := by
    omega
  exact_mod_cast hout

end StreamingReachability.Exact
