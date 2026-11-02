module

public import StreamingSSSP.Hopset.Rank
public import StreamingSSSP.Probability.Family

@[expose] public section

namespace StreamingSSSP.CopyHistory

open scoped Classical BigOperators

inductive Observation (n : ℕ) where
  | fringe (level : ℕ) (pivot : Fin n)
  | core (level : ℕ) (vertices pivots : Finset (Fin n))

namespace Observation

variable {n : ℕ}

def level : Observation n → ℕ
  | .fringe r _ => r
  | .core r _ _ => r

def coreLevel : Observation n → Option ℕ
  | .fringe _ _ => none
  | .core r _ _ => some r

def allows : Observation n → Fin n → ℕ → Prop
  | .fringe r p, v, j => v = p → j = r
  | .core r S P, v, j => v ∈ S → (j = r ↔ v ∈ P)

def keeps : Observation n → Finset (Fin n) → Prop
  | .fringe _ p, S => p ∉ S
  | .core _ S P, T => T ⊆ S ∧ Disjoint T P

end Observation

variable {n : ℕ}

def allowed (history : List (Observation n)) (v : Fin n) (j : ℕ) : Prop :=
  ∀ o ∈ history, o.allows v j

def compatible (history : List (Observation n)) (S : Finset (Fin n)) : Prop :=
  ∀ o ∈ history, o.keeps S

def past (history : List (Observation n)) (r : ℕ) : Prop :=
  ∀ o ∈ history, o.level < r

def coreLevels (history : List (Observation n)) : Finset ℕ :=
  (history.filterMap Observation.coreLevel).toFinset

theorem coreLevels_past (history : List (Observation n)) (r : ℕ)
    (h : past history r) : ∀ q ∈ coreLevels history, q < r := by
  intro q hq
  simp only [coreLevels, List.mem_toFinset, List.mem_filterMap] at hq
  obtain ⟨o, ho, he⟩ := hq
  cases o with
  | fringe s p => simp [Observation.coreLevel] at he
  | core s S P =>
      have hs : s = q := by simpa [Observation.coreLevel] using he
      subst s
      exact h _ ho

theorem active_allowed (history : List (Observation n)) (S : Finset (Fin n))
    (h : compatible history S) {v : Fin n} (hv : v ∈ S) (j : ℕ) :
    allowed history v j ↔ j ∉ coreLevels history := by
  induction history with
  | nil => simp [allowed, coreLevels]
  | cons o history ih =>
      have ht : compatible history S := fun p hp => h p (by simp [hp])
      have hh := h o (by simp)
      cases o with
      | fringe r p =>
          have hne : v ≠ p := by
            intro he
            exact hh (he ▸ hv)
          simpa [allowed, coreLevels, Observation.allows, Observation.coreLevel, hne]
            using ih ht
      | core r T P =>
          have hvT : v ∈ T := hh.1 hv
          have hvP : v ∉ P := fun hvp => (Finset.disjoint_left.mp hh.2) hv hvp
          have hi := ih ht
          simpa [allowed, coreLevels, Observation.allows, Observation.coreLevel, hvT, hvP,
            not_or] using and_congr_left (fun _ => hi)

noncomputable def law (ps : List Rate) (history : List (Observation n)) :
    Law (Fin n → ℕ) :=
  Law.family n fun v => (Ranks.firstHit ps).given (allowed history v)

noncomputable def mass (ps : List Rate) (history : List (Observation n)) : ℝ :=
  ∏ v : Fin n, (Ranks.firstHit ps).prob (allowed history v)

theorem mass_nonneg (ps : List Rate) (history : List (Observation n)) :
    0 ≤ mass ps history :=
  Finset.prod_nonneg fun v _ => (Ranks.firstHit ps).prob_nonneg (allowed history v)

theorem history_factor (ps : List Rate) (history : List (Observation n))
    (Q : (Fin n → ℕ) → Prop) :
    (Law.family n (fun _ : Fin n => Ranks.firstHit ps)).prob
        (fun ranks => (∀ v, allowed history v (ranks v)) ∧ Q ranks) =
      mass ps history * (law ps history).prob Q :=
  Law.family_mask_probability n (fun _ => Ranks.firstHit ps) (allowed history) Q

theorem active_rate_bounds (ps : List Rate) (history : List (Observation n))
    (S : Finset (Fin n)) (r : ℕ) (hr : r < ps.length)
    (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    {v : Fin n} (hv : v ∈ S) :
    (Ranks.rate ps r).value / 2 ≤
        ((Ranks.firstHit ps).given (allowed history v)).prob (· = r) ∧
      ((Ranks.firstHit ps).given (allowed history v)).prob (· = r) ≤
        (Ranks.rate ps r).value := by
  have he : allowed history v = fun j => j ∉ coreLevels history :=
    funext fun j => propext (active_allowed history S hc hv j)
  rw [he]
  exact Ranks.censored_pivot_bounds ps r hr (coreLevels history)
    (coreLevels_past history r hp) hs

theorem active_future_upper (ps : List Rate) (history : List (Observation n))
    (S : Finset (Fin n)) (r j : ℕ) (hrj : r ≤ j) (hj : j < ps.length)
    (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    {v : Fin n} (hv : v ∈ S) :
    ((Ranks.firstHit ps).given (allowed history v)).prob (· = j) ≤
      (Ranks.rate ps j).value := by
  have he : allowed history v = fun t => t ∉ coreLevels history :=
    funext fun t => propext (active_allowed history S hc hv t)
  rw [he]
  exact Ranks.censored_future_upper ps r j hrj hj (coreLevels history)
    (coreLevels_past history r hp) hs

theorem compatible_mono (history : List (Observation n)) {S T : Finset (Fin n)}
    (h : compatible history S) (hTS : T ⊆ S) : compatible history T := by
  intro o ho
  have hh := h o ho
  cases o with
  | fringe r p => exact fun hp => hh (hTS hp)
  | core r U P =>
      refine ⟨hTS.trans hh.1, ?_⟩
      exact Finset.disjoint_left.mpr fun v hv hvP =>
        (Finset.disjoint_left.mp hh.2) (hTS hv) hvP

theorem compatible_append (history : List (Observation n)) (o : Observation n)
    {S T : Finset (Fin n)} (h : compatible history S) (hTS : T ⊆ S) (ho : o.keeps T) :
    compatible (history ++ [o]) T := by
  intro a ha
  rcases List.mem_append.mp ha with hh | hh
  · exact compatible_mono history h hTS a hh
  · have he : a = o := List.mem_singleton.mp hh
    simpa only [he] using ho

theorem past_append (history : List (Observation n)) (o : Observation n) (r : ℕ)
    (h : past history r) (ho : o.level = r) :
    past (history ++ [o]) (r + 1) := by
  intro a ha
  rcases List.mem_append.mp ha with hh | hh
  · exact Nat.lt_succ_of_lt (h a hh)
  · have he : a = o := List.mem_singleton.mp hh
    simpa only [he, ho] using Nat.lt_succ_self r

theorem no_pivot_bound (ps : List Rate) (history : List (Observation n))
    (S T : Finset (Fin n)) (hT : T ⊆ S) (r : ℕ) (hr : r < ps.length)
    (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (law ps history).prob (fun ranks => ∀ v ∈ T, ranks v ≠ r) ≤
      Real.exp (-((Ranks.rate ps r).value / 2) * T.card) := by
  apply Law.family_avoid_exp n
    (fun v => (Ranks.firstHit ps).given (allowed history v)) T (fun _ j => j = r)
    ((Ranks.rate ps r).value / 2)
  intro v hv
  exact (active_rate_bounds ps history S r hr hc hp hs (hT hv)).1

theorem joint_no_pivot_bound (ps : List Rate) (history : List (Observation n))
    (S T : Finset (Fin n)) (hT : T ⊆ S) (r : ℕ) (hr : r < ps.length)
    (hc : compatible history S) (hp : past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2) :
    (Law.family n (fun _ : Fin n => Ranks.firstHit ps)).prob
        (fun ranks => (∀ v, allowed history v (ranks v)) ∧ ∀ v ∈ T, ranks v ≠ r) ≤
      mass ps history * Real.exp (-((Ranks.rate ps r).value / 2) * T.card) := by
  rw [history_factor]
  exact mul_le_mul_of_nonneg_left
    (no_pivot_bound ps history S T hT r hr hc hp hs) (mass_nonneg ps history)

end StreamingSSSP.CopyHistory
