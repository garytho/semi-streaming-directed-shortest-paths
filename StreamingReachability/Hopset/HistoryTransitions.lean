module

public import StreamingReachability.Hopset.CopyMoments
public import StreamingReachability.Probability.ConditionalFamily

@[expose] public section

namespace StreamingReachability.CopyHistory

open scoped Classical BigOperators

variable {n : ℕ}

def event (history : List (Observation n)) (ranks : Fin n → ℕ) : Prop :=
  ∀ v, allowed history v (ranks v)

theorem moment (ps : List Rate) (history : List (Observation n))
    (f : (Fin n → ℕ) → ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect (Law.masked (event history) f) =
      mass ps history * (law ps history).expect f :=
  Law.family_mask_factor n (fun _ => Ranks.firstHit ps) (allowed history) f

theorem probability (ps : List Rate) (history : List (Observation n)) :
    (Law.family n (fun _ => Ranks.firstHit ps)).prob (event history) = mass ps history :=
  Law.family_probability n (fun _ => Ranks.firstHit ps) (allowed history)

theorem event_append (history : List (Observation n)) (o : Observation n)
    (ranks : Fin n → ℕ) :
    event (history ++ [o]) ranks ↔ event history ranks ∧ ∀ v, o.allows v (ranks v) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro v a ha
      exact h v a (List.mem_append_left _ ha)
    · intro v
      exact h v o (by simp)
  · rintro ⟨hold, hnew⟩ v a ha
    rcases List.mem_append.mp ha with h | h
    · exact hold v a h
    · have he : a = o := List.mem_singleton.mp h
      simpa only [he] using hnew v

theorem event_fringe (history : List (Observation n)) (r : ℕ) (p : Fin n)
    (ranks : Fin n → ℕ) :
    event (history ++ [.fringe r p]) ranks ↔ event history ranks ∧ ranks p = r := by
  rw [event_append]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact h p rfl
  · intro h v hv
    simpa only [hv] using h

def pivots (S : Finset (Fin n)) (r : ℕ) (ranks : Fin n → ℕ) : Finset (Fin n) :=
  S.filter fun v => ranks v = r

theorem event_core (history : List (Observation n)) (r : ℕ)
    (S P : Finset (Fin n)) (hP : P ⊆ S) (ranks : Fin n → ℕ) :
    event (history ++ [.core r S P]) ranks ↔ event history ranks ∧ pivots S r ranks = P := by
  rw [event_append]
  apply and_congr_right
  intro _
  constructor
  · intro h
    ext v
    constructor
    · intro hv
      obtain ⟨hvS, hvr⟩ := Finset.mem_filter.mp hv
      exact (h v hvS).mp hvr
    · intro hvP
      exact Finset.mem_filter.mpr ⟨hP hvP, (h v (hP hvP)).mpr hvP⟩
  · intro h v hvS
    constructor
    · intro hvr
      rw [← h]
      exact Finset.mem_filter.mpr ⟨hvS, hvr⟩
    · intro hvP
      have hv : v ∈ pivots S r ranks := h.symm ▸ hvP
      exact (Finset.mem_filter.mp hv).2

theorem fringe_moment (ps : List Rate) (history : List (Observation n)) (r : ℕ) (p : Fin n)
    (f : (Fin n → ℕ) → ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (event history) (Law.masked (fun ranks => ranks p = r) f)) =
      mass ps (history ++ [.fringe r p]) *
        (law ps (history ++ [.fringe r p])).expect f := by
  rw [Law.masked_mask]
  have he : (fun ranks => event history ranks ∧ ranks p = r) =
      event (history ++ [.fringe r p]) :=
    funext fun ranks => propext (event_fringe history r p ranks).symm
  rw [he]
  exact moment ps _ f

theorem fringe_mass (ps : List Rate) (history : List (Observation n)) (r : ℕ) (p : Fin n) :
    mass ps (history ++ [.fringe r p]) =
      mass ps history * (law ps history).prob (fun ranks => ranks p = r) := by
  rw [← probability]
  have he : (event (history ++ [.fringe r p])) =
      fun ranks => event history ranks ∧ ranks p = r :=
    funext fun ranks => propext (event_fringe history r p ranks)
  rw [he]
  exact history_factor ps history (fun ranks => ranks p = r)

theorem core_disintegration (ps : List Rate) (history : List (Observation n))
    (r : ℕ) (S : Finset (Fin n)) (f : Finset (Fin n) → (Fin n → ℕ) → ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (event history) (fun ranks => f (pivots S r ranks) ranks)) =
      ∑ P ∈ S.powerset, mass ps (history ++ [.core r S P]) *
        (law ps (history ++ [.core r S P])).expect (f P) := by
  have hkey (ranks : Fin n → ℕ) : pivots S r ranks ∈ S.powerset :=
    Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hpart := Law.expect_partition (Law.family n (fun _ => Ranks.firstHit ps))
    S.powerset (pivots S r) hkey (fun P => Law.masked (event history) (f P))
  have he :
      (fun ranks => Law.masked (event history) (f (pivots S r ranks)) ranks) =
        Law.masked (event history) (fun ranks => f (pivots S r ranks) ranks) := by
    funext ranks
    rfl
  rw [he] at hpart
  rw [hpart]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Law.masked_mask]
  have hPS : P ⊆ S := Finset.mem_powerset.mp hP
  have hevent : (fun ranks => pivots S r ranks = P ∧ event history ranks) =
      event (history ++ [.core r S P]) := by
    funext ranks
    apply propext
    simpa only [and_comm] using (event_core history r S P hPS ranks).symm
  rw [hevent]
  exact moment ps _ (f P)

theorem core_mass_sum (ps : List Rate) (history : List (Observation n))
    (r : ℕ) (S : Finset (Fin n)) :
    (∑ P ∈ S.powerset, mass ps (history ++ [.core r S P])) = mass ps history := by
  have h := core_disintegration ps history r S (fun _ _ => 1)
  have hm := moment ps history (fun _ => 1)
  simp only [Law.expect_const, mul_one] at h hm
  exact h.symm.trans hm

end StreamingReachability.CopyHistory
