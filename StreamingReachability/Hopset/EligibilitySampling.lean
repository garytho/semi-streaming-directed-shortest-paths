module

public import StreamingReachability.Hopset.Eligibility
public import StreamingReachability.Hopset.ReferenceFacts
public import StreamingReachability.Early.MarkedFamily

@[expose] public section

namespace StreamingReachability.RankPrefix

open scoped Classical

noncomputable section

variable {n : ℕ}

def eligible (r : ℕ) (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) : Finset (Fin n) :=
  S.filter fun v => known v = none

theorem current_old_false (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r)) :
    Early.Sampling.Holds (Law.family n (fun v => currentLaw ps r (known v)))
      (fun coins => ∀ v, known v ≠ none → coins v = false) := by
  apply Hopset.Reference.family_holds n (fun v => currentLaw ps r (known v))
    (fun v b => known v ≠ none → b = false)
  intro v
  cases hk : known v with
  | none =>
      intro z hz h
      exact False.elim (h rfl)
  | some old =>
      simp only [currentLaw, hk]
      exact Early.Sampling.holds_pure false _ (by intro h; rfl)

theorem current_eligible_eq (r : ℕ) (known : Fin n → Option (Fin r)) (S : Finset (Fin n))
    (coins : Fin n → Bool) (h : ∀ v, known v ≠ none → coins v = false) :
    (S.filter fun v => coins v = true) = (eligible r known S).filter fun v => coins v = true := by
  ext v
  simp only [eligible, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hb⟩
    have hk : known v = none := by
      by_contra hn
      have hf := h v hn
      rw [hf] at hb
      contradiction
    exact ⟨⟨hv, hk⟩, hb⟩
  · rintro ⟨⟨hv, _⟩, hb⟩
    exact ⟨hv, hb⟩

theorem coins_as_marked {O : Type*} [Fintype O] (ps : List Rate) (r : ℕ)
    (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) (owner : Fin n → Law O)
    (fallback : O) (f : Finset (Fin n) → (Fin n → O) → ℝ)
    (hdepends : ∀ P left right, (∀ v ∈ P, left v = right v) → f P left = f P right) :
    (Law.family n (fun v => currentLaw ps r (known v))).expect (fun coins =>
        (Law.family n owner).expect (fun owners => f (S.filter fun v => coins v = true) owners)) =
      (Early.Sampling.marked owner (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
        (Ranks.rate ps r).value_le_one (eligible r known S).toList).expect
        (fun xs => f (Early.Sampling.pivots xs) (Early.Sampling.ownerFor fallback xs)) := by
  let E := eligible r known S
  let mu := Law.family n (fun v => currentLaw ps r (known v))
  let nu := Law.family n owner
  let F := fun xs : List (Fin n × O) =>
    f (Early.Sampling.pivots xs) (Early.Sampling.ownerFor fallback xs)
  calc
    _ = mu.expect (fun coins => nu.expect (fun owners =>
        F (Early.Sampling.ownedSubset E.toList coins owners))) := by
      apply Hopset.Reference.expect_congr_on
      refine Early.Sampling.holds_mono (current_old_false ps r known) ?_
      intro coins hold
      apply congrArg nu.expect
      funext owners
      have hpivots : (S.filter fun v => coins v = true) =
          Early.Sampling.pivots (Early.Sampling.ownedSubset E.toList coins owners) := by
        rw [Early.Sampling.ownedSubset_pivots]
        simpa using current_eligible_eq r known S coins hold
      rw [hpivots]
      apply hdepends
      intro v hv
      exact (Early.Sampling.ownedSubset_owner E.toList (Finset.nodup_toList E)
        coins owners fallback v hv).symm
    _ = _ := by
      apply Early.Sampling.family_ownedSubset
      · exact Finset.nodup_toList E
      · intro v hv
        have he : v ∈ eligible r known S := Finset.mem_toList.mp hv
        have hk := (Finset.mem_filter.mp he).2
        rw [hk]
        rfl

theorem choice_as_marked {O : Type*} [Fintype O] (ps : List Rate) (r : ℕ) (hr : r < ps.length)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (known : Fin n → Option (Fin r)) (S : Finset (Fin n)) (owner : Fin n → Law O)
    (fallback : O) (f : Finset (Fin n) → (Fin n → O) → ℝ)
    (hdepends : ∀ P left right, (∀ v ∈ P, left v = right v) → f P left = f P right) :
    (law ps r known).expect (fun ranks =>
        (Law.family n owner).expect (fun owners => f (CopyHistory.pivots S r ranks) owners)) =
      (Early.Sampling.marked owner (Ranks.rate ps r).value (Ranks.rate ps r).value_nonneg
        (Ranks.rate ps r).value_le_one (eligible r known S).toList).expect
        (fun xs => f (Early.Sampling.pivots xs) (Early.Sampling.ownerFor fallback xs)) := by
  have h := current_family ps r hr hs known
    (fun coins => (Law.family n owner).expect (fun owners => f (S.filter fun v => coins v = true) owners))
  calc
    _ = (Law.family n (fun v => currentLaw ps r (known v))).expect (fun coins =>
        (Law.family n owner).expect (fun owners => f (S.filter fun v => coins v = true) owners)) := by
      simpa only [CopyHistory.pivots, decide_eq_true_eq] using h
    _ = _ := coins_as_marked ps r known S owner fallback f hdepends

end

end StreamingReachability.RankPrefix
