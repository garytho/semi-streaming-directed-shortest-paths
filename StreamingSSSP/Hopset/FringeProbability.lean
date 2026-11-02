module

public import StreamingSSSP.Shifts
public import StreamingSSSP.Early.Stars
public import StreamingSSSP.Early.Knockout

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical BigOperators

theorem pair_owner_expectation (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (f : Fin M × Fin N → ℝ) :
    (Law.uniformPair M N hM hN).expect f = (Early.ownerLaw M N hM hN).expect f := by
  rw [Law.expect_uniformPair, Early.expect_owner]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem fringe_window {V : Type*} [Fintype V] (G : Graph V) (p v : V)
    (d : ℕ) (hd : min (G.dist p v) (G.dist v p) = (d : Distance))
    (rho D : ℝ) (hv : v ∈ Early.fringe G p rho D) :
    (d : ℝ) - D ≤ rho ∧ rho ≤ d + D := by
  have h : (d : ℝ) ≤ rho + D ∧ ¬ (d : ℝ) ≤ rho - D := by
    simpa only [Early.fringe, Finset.mem_sdiff, Early.mem_bothBall, Early.Within,
      ← Early.bounded_min_iff, hd, Early.bounded_nat_iff] using hv
  constructor <;> linarith

theorem fringe_probability {V : Type*} [Fintype V] (G : Graph V) (p v : V)
    (width M N : ℕ) (hw : 0 < width) (hM : 0 < M) (hN : 0 < N)
    (candidate : Fin M → Fin N → Fin width) (base D : ℝ) (hD : 0 < D) :
    (Law.uniformPair M N hM hN).prob (fun z =>
      v ∈ Early.fringe G p
        (base + (D / N) * Shifts.pointIndex width M N candidate z.1 z.2) D) ≤
      4 / M := by
  let mu := Law.uniformPair M N hM hN
  by_cases htop : min (G.dist p v) (G.dist v p) = ⊤
  · have hz : mu.prob (fun z =>
        v ∈ Early.fringe G p
          (base + (D / N) * Shifts.pointIndex width M N candidate z.1 z.2) D) = 0 := by
      apply (Law.prob_congr mu _ (fun _ => False) ?_).trans (Law.prob_false _)
      intro z
      constructor
      · intro hz
        have houter := (Finset.mem_sdiff.mp hz).1
        have hwithin := (Early.mem_bothBall G p v _).mp houter
        have hb := (Early.bounded_min_iff (G.dist p v) (G.dist v p) _).mpr hwithin
        rw [htop] at hb
        obtain ⟨w, hw, _⟩ := hb
        exact WithTop.natCast_ne_top w hw.symm
      · exact False.elim
    rw [hz]
    positivity
  · lift min (G.dist p v) (G.dist v p) to ℕ using htop with d hd
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hND : D / N ≤ D := div_le_self hD.le hNreal
    have hwide : D / N ≤ ((d : ℝ) + D) - (d - D) := by linarith
    have hwindows := Shifts.window_charge width M N hw hM hN candidate base D
      ((d : ℝ) - D) (d + D) hD hwide
    have hmono : mu.prob (fun z =>
          v ∈ Early.fringe G p
            (base + (D / N) * Shifts.pointIndex width M N candidate z.1 z.2) D) ≤
        mu.prob (fun z =>
          (d : ℝ) - D ≤ base + (D / N) * Shifts.pointIndex width M N candidate z.1 z.2 ∧
            base + (D / N) * Shifts.pointIndex width M N candidate z.1 z.2 ≤ d + D) :=
      Law.prob_mono mu (fun z hz => fringe_window G p v d hd.symm _ D hz)
    apply (hmono.trans hwindows).trans_eq
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
    field_simp [hMR, ne_of_gt hD]
    ring

end StreamingSSSP.Hopset
