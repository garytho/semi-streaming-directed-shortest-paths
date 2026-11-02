module

public import StreamingSSSP.Exact.PositiveOracle

@[expose] public section

namespace StreamingSSSP.Exact

open scoped Classical

variable {V : Type*} [Fintype V]

/-- The clock distinguishes repeated identical queries. Thus an arbitrary
successful sequence of fresh randomized answers can instantiate this interface. -/
abbrev Oracle (U : Type*) := Graph U → U → ℕ → ℕ → U → ℕ

def offsetOracle {U : Type*} (offset : ℕ) (call : Oracle U) : Oracle U :=
  fun G source denominator clock => call G source denominator (offset + clock)

/-- This recursion stores only the current label vector. `G` is an edge-local
input descriptor, not a stored adjacency table. -/
def smoothFrom (call : Oracle (Option V)) (G : Graph V)
    (M : ℕ) : ℕ → ℕ → (V → ℕ) → V → ℕ
  | 0, _, labels => labels
  | rounds + 1, slope, labels =>
      let K := M * (2 * 2 ^ rounds)
      let answer₀ := call (levelGraph G labels (slope + 1) (8 * K) 0) none (100 * M) (2 * rounds + 1)
      let answer₁ := call (levelGraph G labels (slope + 1) (8 * K) (4 * K)) none (100 * M) (2 * rounds + 2)
      smoothFrom call G M rounds (slope + 1) (partialLabels labels K answer₀ answer₁)

/-- Success is checked against precisely the adaptively generated queries. -/
def SmoothingSuccess (call : Oracle (Option V)) (G : Graph V)
    (M : ℕ) : ℕ → ℕ → (V → ℕ) → Prop
  | 0, _, _ => True
  | rounds + 1, slope, labels =>
      let K := M * (2 * 2 ^ rounds)
      let H₀ := levelGraph G labels (slope + 1) (8 * K) 0
      let H₁ := levelGraph G labels (slope + 1) (8 * K) (4 * K)
      let answer₀ := call H₀ none (100 * M) (2 * rounds + 1)
      let answer₁ := call H₁ none (100 * M) (2 * rounds + 2)
      IntegerApprox H₀ none (100 * M) answer₀ ∧
      IntegerApprox H₁ none (100 * M) answer₁ ∧
      SmoothingSuccess call G M rounds (slope + 1) (partialLabels labels K answer₀ answer₁)

theorem smoothFrom_correct (call : Oracle (Option V)) (G : Graph V)
    (s : V) (scale M rounds slope : ℕ) (labels : V → ℕ)
    (hreach : ∀ v, G.dist s v ≠ ⊤)
    (hslope : scale ≤ slope) (hM : slope + rounds ≤ M)
    (hzero : labels s = 0)
    (hnon : Noncontracting G s scale labels)
    (hsmooth : AdditivelySmooth G labels slope (2 ^ rounds))
    (hsuccess : SmoothingSuccess call G M rounds slope labels) :
    let out := smoothFrom call G M rounds slope labels
    out s = 0 ∧ Noncontracting G s scale out ∧
      AdditivelySmooth G out (slope + rounds) 1 ∧ ∀ v, out v ≤ labels v := by
  induction rounds generalizing slope labels with
  | zero =>
      exact ⟨hzero, hnon, by simpa [smoothFrom] using hsmooth, fun _ => le_rfl⟩
  | succ rounds ih =>
      let K := M * (2 * 2 ^ rounds)
      let H₀ := levelGraph G labels (slope + 1) (8 * K) 0
      let H₁ := levelGraph G labels (slope + 1) (8 * K) (4 * K)
      let answer₀ := call H₀ none (100 * M) (2 * rounds + 1)
      let answer₁ := call H₁ none (100 * M) (2 * rounds + 2)
      let next := partialLabels labels K answer₀ answer₁
      rcases hsuccess with ⟨h₀, h₁, hrest⟩
      have hnextsmooth : AdditivelySmooth G next (slope + 1) (2 ^ rounds) := by
        apply partial_smoothing G labels slope (2 ^ rounds) M (by positivity) (by omega)
          _ answer₀ answer₁ h₀ h₁
        simpa [pow_succ, Nat.mul_comm] using hsmooth
      have henv := envelope_noncontracting G s scale (slope + 1) labels
        (by omega) hreach hnon
      have hnextnon : Noncontracting G s scale next := by
        intro v d hd
        exact (henv v d hd).trans
          (partialLabels_envelope_lower G labels (slope + 1) K (100 * M)
            answer₀ answer₁ h₀ h₁ v)
      have hnextzero : next s = 0 := partialLabels_source labels K answer₀ answer₁ hzero
      have hi := ih (slope + 1) next (by omega) (by omega) hnextzero
        hnextnon hnextsmooth hrest
      refine ⟨hi.1, hi.2.1, ?_, ?_⟩
      · change AdditivelySmooth G (smoothFrom call G M rounds (slope + 1) next)
          (slope + (rounds + 1)) 1
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi.2.2.1
      · intro v
        exact (hi.2.2.2 v).trans (partialLabels_le labels K answer₀ answer₁ v)

def smoothingScale (rounds : ℕ) : ℕ := 100 * (rounds + 1)

def smoothing (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) : V → ℕ :=
  let C := smoothingScale rounds
  let initial := fun v => C * baseCall G s 1 0 v
  smoothFrom levelCall G (C + rounds) rounds C initial

def FullSmoothingSuccess (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds : ℕ) : Prop :=
  let C := smoothingScale rounds
  IntegerApprox G s 1 (baseCall G s 1 0) ∧
    SmoothingSuccess levelCall G (C + rounds) rounds C (fun v => C * baseCall G s 1 0 v)

theorem smoothing_correct (baseCall : Oracle V) (levelCall : Oracle (Option V))
    (G : Graph V) (s : V) (rounds bound : ℕ)
    (hreach : ∀ v, ∃ d : ℕ, G.dist s v = d ∧ d ≤ bound)
    (hbudget : 2 * smoothingScale rounds * bound ≤ 2 ^ rounds)
    (hsuccess : FullSmoothingSuccess baseCall levelCall G s rounds) :
    let C := smoothingScale rounds
    let out := smoothing baseCall levelCall G s rounds
    out s = 0 ∧ Noncontracting G s C out ∧
      (∀ u v (w : ℕ), G u v = w → 0 < w →
        2 * (out v : ℤ) ≤ 2 * out u + 3 * C * w) ∧
      (∀ v, out v ≤ 2 * C * bound) := by
  let C := smoothingScale rounds
  let initial := fun v => C * baseCall G s 1 0 v
  rcases hsuccess with ⟨hbase, hlevels⟩
  have hinitial : ∀ v, initial v ≤ 2 * C * bound := by
    intro v
    obtain ⟨d, hd, hdb⟩ := hreach v
    have ha := (hbase v d hd).2
    dsimp [initial]
    nlinarith [Nat.mul_le_mul_left C ha, Nat.mul_le_mul_left (2 * C) hdb]
  have hnon : Noncontracting G s C initial := by
    intro v d hd
    exact Nat.mul_le_mul_left C (hbase v d hd).1
  have hzero : initial s = 0 := by
    have hh := (hbase s 0 (G.dist_self s)).2
    simp only [Nat.add_zero, Nat.mul_zero, one_mul] at hh
    simp [initial, Nat.eq_zero_of_le_zero hh]
  have hi := smoothFrom_correct levelCall G s C (C + rounds) rounds C initial
    (by intro v; obtain ⟨d, hd, _⟩ := hreach v; simp [hd])
    le_rfl le_rfl hzero hnon
    (bounded_labels_smooth G initial C (2 ^ rounds) (fun v => (hinitial v).trans hbudget))
    hlevels
  refine ⟨hi.1, hi.2.1, ?_, fun v => (hi.2.2.2 v).trans (hinitial v)⟩
  intro u v w hw hwpos
  obtain ⟨d, hd, hdw⟩ := finite_of_le (hw ▸ G.dist_le_edge u v)
  have hs := hi.2.2.1 u v d hd
  have hcw : (C + rounds : ℤ) * d ≤ (C + rounds : ℤ) * w := by
    exact_mod_cast Nat.mul_le_mul_left (C + rounds) hdw
  have hC : (C : ℤ) = 100 * (rounds + 1 : ℤ) := by
    dsimp [C, smoothingScale]
  change 2 * (smoothFrom levelCall G (C + rounds) rounds C initial v : ℤ) ≤
    2 * smoothFrom levelCall G (C + rounds) rounds C initial u + 3 * C * w
  push_cast at hs
  nlinarith

end StreamingSSSP.Exact
