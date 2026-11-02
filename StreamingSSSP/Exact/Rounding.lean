module

public import StreamingSSSP.Exact.SmoothingLoop

@[expose] public section

namespace StreamingSSSP.Exact

variable {V : Type*} [Fintype V]

def inflation (n : ℕ) : ℕ := 64 * (n + 1)

def shiftCandidate (n C index : ℕ) : ℕ :=
  C * inflation n + 4 * C * index

def roundingDenominator (n C : ℕ) : ℕ := 2 * C * inflation n

theorem shiftCandidate_bounds (n C index : ℕ) (hC : 0 < C) (hi : index ≤ n) :
    C * inflation n ≤ shiftCandidate n C index ∧
      shiftCandidate n C index < roundingDenominator n C := by
  dsimp [shiftCandidate, roundingDenominator, inflation]
  constructor
  · omega
  · nlinarith [Nat.mul_le_mul_left (4 * C) hi]

theorem bad_candidates_unique (n C label i j : ℕ) (hC : 0 < C)
    (hi : i ≤ n) (hj : j ≤ n)
    (hbad_i : roundingDenominator n C - 2 * C <
      (label + shiftCandidate n C i) % roundingDenominator n C)
    (hbad_j : roundingDenominator n C - 2 * C <
      (label + shiftCandidate n C j) % roundingDenominator n C) : i = j := by
  let Q := roundingDenominator n C
  have hQ : 0 < Q := by dsimp [Q, roundingDenominator, inflation]; positivity
  have hmargin : 2 * C ≤ Q := by dsimp [Q, roundingDenominator, inflation]; nlinarith
  have hspan : 4 * C * n + 2 * C < Q := by
    dsimp [Q, roundingDenominator, inflation]
    nlinarith
  have hstrict (i j : ℕ) (hij : i < j) (hj : j ≤ n)
      (hbi : Q - 2 * C < (label + shiftCandidate n C i) % Q)
      (hbj : Q - 2 * C < (label + shiftCandidate n C j) % Q) : False := by
    let ri := (label + shiftCandidate n C i) % Q
    let rj := (label + shiftCandidate n C j) % Q
    let qi := (label + shiftCandidate n C i) / Q
    let qj := (label + shiftCandidate n C j) / Q
    have hri : ri < Q := Nat.mod_lt _ hQ
    have hrj : rj < Q := Nat.mod_lt _ hQ
    have hei : ri + Q * qi = label + C * inflation n + 4 * C * i := by
      simpa [ri, qi, shiftCandidate, Nat.add_assoc] using
        Nat.mod_add_div (label + shiftCandidate n C i) Q
    have hej : rj + Q * qj = label + C * inflation n + 4 * C * j := by
      simpa [rj, qj, shiftCandidate, Nat.add_assoc] using
        Nat.mod_add_div (label + shiftCandidate n C j) Q
    have hstep : 4 * C * i + 4 * C ≤ 4 * C * j := by
      nlinarith [Nat.mul_le_mul_left (4 * C) (show i + 1 ≤ j by omega)]
    have hmax : 4 * C * j ≤ 4 * C * n := Nat.mul_le_mul_left _ hj
    by_cases hq : qj ≤ qi
    · have hp := Nat.mul_le_mul_left Q hq
      change Q - 2 * C < ri at hbi
      omega
    · have hp := Nat.mul_le_mul_left Q (show qi + 1 ≤ qj by omega)
      change Q - 2 * C < rj at hbj
      have hbj' : Q < rj + 2 * C := by omega
      nlinarith
  rcases lt_trichotomy i j with hij | hij | hij
  · exact (hstrict i j hij hj hbad_i hbad_j).elim
  · exact hij
  · exact (hstrict j i hij hi hbad_j hbad_i).elim

def SafeShiftIndex (labels : V → ℕ) (C : ℕ)
    (index : Fin (Fintype.card V + 1)) : Prop :=
  ∀ v, (labels v + shiftCandidate (Fintype.card V) C index) %
    roundingDenominator (Fintype.card V) C ≤ roundingDenominator (Fintype.card V) C - 2 * C

theorem safe_shift_exists (labels : V → ℕ) (C : ℕ) (hC : 0 < C) :
    ∃ index : Fin (Fintype.card V + 1), SafeShiftIndex labels C index := by
  classical
  by_contra hn
  have hbad : ∀ index : Fin (Fintype.card V + 1), ∃ v,
      roundingDenominator (Fintype.card V) C - 2 * C <
        (labels v + shiftCandidate (Fintype.card V) C index) %
          roundingDenominator (Fintype.card V) C := by
    simpa only [SafeShiftIndex, not_exists, not_forall, not_le] using hn
  let f : Fin (Fintype.card V + 1) → V := fun i => Classical.choose (hbad i)
  have hf (i : Fin (Fintype.card V + 1)) :
      roundingDenominator (Fintype.card V) C - 2 * C <
        (labels (f i) + shiftCandidate (Fintype.card V) C i) %
          roundingDenominator (Fintype.card V) C := Classical.choose_spec (hbad i)
  have hinj : Function.Injective f := by
    intro i j hij
    have hi := hf i
    rw [hij] at hi
    exact Fin.ext (bad_candidates_unique (Fintype.card V) C (labels (f j))
      i j hC (by omega) (by omega) hi (hf j))
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega

def safeShiftIndex (labels : V → ℕ) (C : ℕ) (hC : 0 < C) :
    Fin (Fintype.card V + 1) := by
  letI : DecidablePred (SafeShiftIndex labels C) := fun index => by
    unfold SafeShiftIndex
    exact Fintype.decidableForallFintype
  exact (Finset.univ.filter (SafeShiftIndex labels C)).min' (by
      obtain ⟨index, hindex⟩ := safe_shift_exists labels C hC
      exact ⟨index, by simp [hindex]⟩)

theorem safeShiftIndex_safe (labels : V → ℕ) (C : ℕ) (hC : 0 < C) :
    SafeShiftIndex labels C (safeShiftIndex labels C hC) := by
  letI : DecidablePred (SafeShiftIndex labels C) := fun index => by
    unfold SafeShiftIndex
    exact Fintype.decidableForallFintype
  have h := Finset.min'_mem (Finset.univ.filter (SafeShiftIndex labels C))
    (by obtain ⟨index, hindex⟩ := safe_shift_exists labels C hC
        exact ⟨index, by simp [hindex]⟩)
  exact (Finset.mem_filter.mp h).2

/-- A finite minimum over the stored labels chooses one common shift. No graph
access occurs in the selection or in the coordinatewise division below. -/
def roundedUpdate (labels : V → ℕ) (C : ℕ) (hC : 0 < C) : V → ℕ :=
  fun v => (labels v + shiftCandidate (Fintype.card V) C (safeShiftIndex labels C hC)) /
    roundingDenominator (Fintype.card V) C

theorem roundedUpdate_source (labels : V → ℕ) (C : ℕ) (hC : 0 < C)
    {s : V} (hs : labels s = 0) : roundedUpdate labels C hC s = 0 := by
  unfold roundedUpdate
  rw [hs, zero_add]
  exact Nat.div_eq_of_lt (shiftCandidate_bounds _ _ _ hC (by
    have hi := (safeShiftIndex labels C hC).isLt
    omega)).2

theorem safe_rounding_edge (n C a b shift w : ℕ) (hC : 0 < C)
    (hsafe : (a + shift) % roundingDenominator n C ≤ roundingDenominator n C - 2 * C)
    (hsmooth : 2 * (b : ℤ) ≤ 2 * a + 3 * C * (inflation n * w + 1)) :
    (b + shift) / roundingDenominator n C ≤
      (a + shift) / roundingDenominator n C + w := by
  let Q := roundingDenominator n C
  have hQ : 0 < Q := by dsimp [Q, roundingDenominator, inflation]; positivity
  have hm : 2 * C ≤ Q := by dsimp [Q, roundingDenominator, inflation]; nlinarith
  let qa := (a + shift) / Q
  let qb := (b + shift) / Q
  let ra := (a + shift) % Q
  let rb := (b + shift) % Q
  have hea : ra + Q * qa = a + shift := Nat.mod_add_div _ _
  have heb : rb + Q * qb = b + shift := Nat.mod_add_div _ _
  have hP : (3 : ℤ) ≤ inflation n := by dsimp [inflation]; omega
  have hs : (b : ℤ) - a < (Q : ℤ) * w + 2 * C := by
    have hQ' : (Q : ℤ) = 2 * C * inflation n := by dsimp [Q, roundingDenominator]
    have hnon : (0 : ℤ) ≤ (inflation n - 3 : ℤ) * w := by positivity
    nlinarith
  have hs' : b < a + Q * w + 2 * C := by
    exact_mod_cast (show (b : ℤ) < a + (Q : ℤ) * w + 2 * C by omega)
  by_contra hn
  change ¬qb ≤ qa + w at hn
  have hprod := Nat.mul_le_mul_left Q (show qa + w + 1 ≤ qb by omega)
  change ra ≤ Q - 2 * C at hsafe
  have hsafe' : ra + 2 * C ≤ Q := by omega
  nlinarith

theorem roundedUpdate_feasible (G : Graph V) (labels : V → ℕ) (C : ℕ) (hC : 0 < C)
    (hsmooth : ∀ u v (w : ℕ), G u v = w →
      2 * (labels v : ℤ) ≤ 2 * labels u + 3 * C * (inflation (Fintype.card V) * w + 1)) :
    ∀ u v (w : ℕ), G u v = w →
      roundedUpdate labels C hC v ≤ roundedUpdate labels C hC u + w := by
  intro u v w hw
  exact safe_rounding_edge _ C (labels u) (labels v) _ w hC
    (safeShiftIndex_safe labels C hC u) (hsmooth u v w hw)

theorem roundedUpdate_halves (labels : V → ℕ) (C : ℕ) (hC : 0 < C)
    {v : V} {d : ℕ} (hlower : C * inflation (Fintype.card V) * d ≤ labels v) :
    d ≤ 2 * roundedUpdate labels C hC v := by
  let n := Fintype.card V
  let shift := shiftCandidate n C (safeShiftIndex labels C hC)
  let Q := roundingDenominator n C
  have hshift : C * inflation n ≤ shift := (shiftCandidate_bounds n C _ hC (by
    have hi := (safeShiftIndex labels C hC).isLt
    omega)).1
  have hQ : 0 < Q := by dsimp [Q, roundingDenominator, inflation]; positivity
  have hmod : (labels v + shift) % Q < Q := Nat.mod_lt _ hQ
  have he := Nat.mod_add_div (labels v + shift) Q
  have hQeq : Q = 2 * C * inflation n := rfl
  change d ≤ 2 * ((labels v + shift) / Q)
  by_contra hn
  have hd : 2 * ((labels v + shift) / Q) + 1 ≤ d := by omega
  have hp := Nat.mul_le_mul_left (C * inflation n) hd
  nlinarith

end StreamingSSSP.Exact
