module

public import StreamingSSSP.Hopset.ReferenceMoments
public import StreamingSSSP.Probability.Branching

@[expose] public section

namespace StreamingSSSP.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

def futureMoment (ps : List Rate) (history : List (CopyHistory.Observation n))
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ) (S : Finset (Fin n)) : ℝ :=
  (Law.family n (fun _ => Ranks.firstHit ps)).expect (Law.masked (CopyHistory.event history) (f S))

theorem core_future_bound (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (rho : Fin n → ℝ) (r : ℕ)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hrho : ∀ p, 0 ≤ rho p) (v : Fin n) (B : ℝ) (hB : 0 ≤ B)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ)
    (hfuture : ∀ history T, CopyHistory.compatible history T →
      CopyHistory.past history (r + 1) →
        futureMoment ps history f T ≤ CopyHistory.mass ps history * B *
          if v ∈ T then 1 else 0) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (fun ranks =>
          ((Geometry.core G S (CopyHistory.pivots S r ranks) rho).map
            fun T => f T ranks).sum)) ≤
      CopyHistory.mass ps history * B := by
  rw [CopyHistory.core_disintegration ps history r S
    (fun P ranks => ((Geometry.core G S P rho).map fun T => f T ranks).sum)]
  calc
    _ ≤ ∑ P ∈ S.powerset, CopyHistory.mass ps (history ++ [.core r S P]) * B := by
      apply Finset.sum_le_sum
      intro P hP
      let next := history ++ [.core r S P]
      let xs := Geometry.core G S P rho
      have hnextPast : CopyHistory.past next (r + 1) :=
        CopyHistory.past_append history (.core r S P) r hp rfl
      have hIH (T : Finset (Fin n)) (hT : T ∈ xs) :
          futureMoment ps next f T ≤ CopyHistory.mass ps next * B *
            if v ∈ T then 1 else 0 :=
        hfuture next T (Geometry.core_history G S P rho history hc r
          (fun p _ => hrho p) T hT) hnextPast
      have hmB : 0 ≤ CopyHistory.mass ps next * B :=
        mul_nonneg (CopyHistory.mass_nonneg ps next) hB
      calc
        _ = (xs.map fun T => futureMoment ps next f T).sum := by
          rw [Branching.expect_list_sum, Branching.sum_scale]
          congr 1
          apply List.map_congr_left
          intro T _
          exact (CopyHistory.moment ps next (f T)).symm
        _ ≤ (xs.map fun T => CopyHistory.mass ps next * B *
              if v ∈ T then 1 else 0).sum :=
          List.sum_le_sum hIH
        _ = (CopyHistory.mass ps next * B) *
            (xs.map fun T => if v ∈ T then (1 : ℝ) else 0).sum :=
          (Branching.sum_scale xs _ _).symm
        _ ≤ CopyHistory.mass ps next * B :=
          mul_le_of_le_one_right hmB (Geometry.core_count_at G S P rho v)
    _ = _ := by rw [← Finset.sum_mul, CopyHistory.core_mass_sum]

theorem fringe_future_bound (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (p v : Fin n) (B : ℝ) (hB : 0 ≤ B)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ)
    (hfuture : ∀ history T, CopyHistory.compatible history T →
      CopyHistory.past history (r + 1) →
        futureMoment ps history f T ≤ CopyHistory.mass ps history * B *
          if v ∈ T then 1 else 0) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (Law.masked (fun ranks => ranks p = r)
          (fun ranks => (ownerLaw n cfg).expect (fun owners =>
            f (S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ranks)))) ≤
      CopyHistory.mass ps (history ++ [.fringe r p]) * B *
        (ownerLaw n cfg).prob (fun owners =>
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) := by
  let next := history ++ [.fringe r p]
  let T := fun owners : Owners n cfg =>
    S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
  have hevent : (fun ranks => CopyHistory.event history ranks ∧ ranks p = r) =
      CopyHistory.event next :=
    funext fun ranks => propext (CopyHistory.event_fringe history r p ranks).symm
  rw [Law.masked_mask, Law.expect_mask_comm, hevent]
  have hnextPast : CopyHistory.past next (r + 1) :=
    CopyHistory.past_append history (.fringe r p) r hp rfl
  have hmB : 0 ≤ CopyHistory.mass ps next * B :=
    mul_nonneg (CopyHistory.mass_nonneg ps next) hB
  calc
    _ ≤ (ownerLaw n cfg).expect (fun owners =>
        CopyHistory.mass ps next * B * if v ∈ T owners then (1 : ℝ) else 0) := by
      apply Law.expect_mono
      intro owners
      exact hfuture next (T owners)
        (Geometry.fringe_history G S (radii cfg r G owners) history hc r (distanceScale cfg r)
          p (radii_lower_scale cfg hnum r G owners p)) hnextPast
    _ = CopyHistory.mass ps next * B *
        (ownerLaw n cfg).prob (fun owners => v ∈ T owners) := by
      rw [Law.expect_mul, Law.expect_indicator]

theorem fringes_future_sum (G : Graph (Fin n)) (cfg : Config) (r : ℕ)
    (S : Finset (Fin n)) (ranks : Fin n → ℕ) (owners : Owners n cfg)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ) :
    ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
        (distanceScale cfg r)).map fun T => f T ranks).sum =
      ∑ p ∈ S, Law.masked (fun ranks => ranks p = r)
        (fun ranks => f (S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ranks)
        ranks := by
  let P := CopyHistory.pivots S r ranks
  let g := fun p => f (S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ranks
  have hsum : ((members P).map g).sum = ∑ p ∈ P, g p := by
    have h := List.sum_toFinset g (members_nodup P)
    rw [members_toFinset] at h
    exact h.symm
  dsimp only [Geometry.fringes]
  simp only [List.map_map, Function.comp_def]
  change ((members P).map g).sum = _
  rw [hsum]
  dsimp only [P, CopyHistory.pivots]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : ranks p = r <;> simp [g, Law.masked, hp]

set_option maxHeartbeats 600000 in
theorem fringes_future_total (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (v : Fin n) (B : ℝ) (hB : 0 ≤ B)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ)
    (hfuture : ∀ history T, CopyHistory.compatible history T →
      CopyHistory.past history (r + 1) →
        futureMoment ps history f T ≤ CopyHistory.mass ps history * B *
          if v ∈ T then 1 else 0) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (fun ranks =>
          (ownerLaw n cfg).expect (fun owners =>
            ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
              (distanceScale cfg r)).map fun T => f T ranks).sum))) ≤
      CopyHistory.mass ps history * B *
        (CopyHistory.law ps history).expect
          (fun ranks => (ownerLaw n cfg).expect (fringeCount G cfg r S v ranks)) := by
  let mu := Law.family n (fun _ => Ranks.firstHit ps)
  let nu := ownerLaw n cfg
  have he (ranks : Fin n → ℕ) :
      nu.expect (fun owners =>
          ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
            (distanceScale cfg r)).map fun T => f T ranks).sum) =
        ∑ p ∈ S, Law.masked (fun ranks => ranks p = r) (fun ranks =>
          nu.expect (fun owners =>
            f (S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ranks)) ranks := by
    have hfn :
        (fun owners : Owners n cfg =>
          ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
            (distanceScale cfg r)).map fun T => f T ranks).sum) =
          fun owners => ∑ p ∈ S, Law.masked (fun ranks => ranks p = r)
            (fun ranks => f (S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) ranks)
            ranks := funext (fun owners => fringes_future_sum G cfg r S ranks owners f)
    rw [hfn, Law.expect_finset_sum]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : ranks p = r <;> simp [Law.masked, hp]
  change mu.expect (Law.masked (CopyHistory.event history) (fun ranks =>
    nu.expect (fun owners =>
      ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
        (distanceScale cfg r)).map fun T => f T ranks).sum))) ≤ _
  simp_rw [he]
  rw [Law.expect_mask_finset_sum]
  calc
    _ ≤ ∑ p ∈ S, CopyHistory.mass ps (history ++ [.fringe r p]) * B *
        nu.prob (fun owners =>
          v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)) := by
      apply Finset.sum_le_sum
      intro p _
      exact fringe_future_bound ps history S G cfg hnum r hc hp p v B hB f hfuture
    _ = CopyHistory.mass ps history * B *
        ∑ p ∈ S, ((CopyHistory.law ps history).bind fun ranks =>
          nu.map fun owners =>
            if ranks p = r ∧
              v ∈ S ∩ Early.fringe G p (radii cfg r G owners p) (distanceScale cfg r)
            then (1 : ℝ) else 0).expect id := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [CopyHistory.fringe_mass, Law.independent_indicator]
      ring
    _ = _ := by rw [fringeCount_mixed_mean]

theorem early_future_step (ps : List Rate) (history : List (CopyHistory.Observation n))
    (S : Finset (Fin n)) (G : Graph (Fin n)) (cfg : Config) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (hr : r < ps.length)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hs : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (v : Fin n) (b : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hin : (Early.searchIn G v
      (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b)
    (hout : (Early.searchOut G v
      (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ)
    (hfuture : ∀ history T, CopyHistory.compatible history T →
      CopyHistory.past history (r + 1) →
        futureMoment ps history f T ≤ CopyHistory.mass ps history * B *
          if v ∈ T then 1 else 0) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (fun ranks =>
          (ownerLaw n cfg).expect (fun owners =>
            ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
                (distanceScale cfg r) ++
              Geometry.core G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)).map
                fun T => f T ranks).sum))) ≤
      CopyHistory.mass ps history * B *
        (1 + 8 * (b : ℝ) * (Ranks.rate ps r).value / cfg.groups) := by
  have hmB : 0 ≤ CopyHistory.mass ps history * B :=
    mul_nonneg (CopyHistory.mass_nonneg ps history) hB
  have hfringe := (fringes_future_total ps history S G cfg hnum r hc hp v B hB f hfuture).trans
    (mul_le_mul_of_nonneg_left
      (expected_fringe_count ps history S G cfg hnum r hr hc hp hs v b hin hout) hmB)
  have hcore :
      (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (fun ranks =>
          (ownerLaw n cfg).expect (fun owners =>
            ((Geometry.core G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)).map
              fun T => f T ranks).sum))) ≤ CopyHistory.mass ps history * B := by
    rw [Law.expect_mask_comm]
    apply (Law.expect_mono _ ?_).trans_eq (Law.expect_const _ _)
    intro owners
    exact core_future_bound ps history S G (radii cfg r G owners) r hc hp
      (radii_nonneg cfg hnum r G owners) v B hB f hfuture
  have he :
      (fun ranks : Fin n → ℕ => (ownerLaw n cfg).expect (fun owners =>
        ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
            (distanceScale cfg r) ++
          Geometry.core G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)).map
            fun T => f T ranks).sum)) =
        fun ranks =>
          (ownerLaw n cfg).expect (fun owners =>
            ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
              (distanceScale cfg r)).map fun T => f T ranks).sum) +
          (ownerLaw n cfg).expect (fun owners =>
            ((Geometry.core G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)).map
              fun T => f T ranks).sum) := by
    funext ranks
    simp only [List.map_append, List.sum_append, Law.expect_add]
  rw [he, Law.expect_mask_add]
  exact (add_le_add hfringe hcore).trans_eq (by ring)

theorem single_child_future {I : Type*} (mu : Law I)
    (ps : List Rate) (history : List (CopyHistory.Observation n)) (S : Finset (Fin n)) (r : ℕ)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (child : I → Finset (Fin n)) (hchild : ∀ i, child i ⊆ S)
    (v : Fin n) (B : ℝ) (hB : 0 ≤ B)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ)
    (hfuture : ∀ history T, CopyHistory.compatible history T →
      CopyHistory.past history (r + 1) →
        futureMoment ps history f T ≤ CopyHistory.mass ps history * B *
          if v ∈ T then 1 else 0) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (fun ranks =>
          mu.expect (fun i => f (child i) ranks))) ≤ CopyHistory.mass ps history * B := by
  have hnextPast : CopyHistory.past history (r + 1) := by
    intro o ho
    exact Nat.lt_succ_of_lt (hp o ho)
  have hmB : 0 ≤ CopyHistory.mass ps history * B :=
    mul_nonneg (CopyHistory.mass_nonneg ps history) hB
  rw [Law.expect_mask_comm]
  apply (Law.expect_mono _ ?_).trans_eq (Law.expect_const _ _)
  intro i
  have h := hfuture history (child i) (CopyHistory.compatible_mono history hc (hchild i)) hnextPast
  apply h.trans
  by_cases hv : v ∈ child i
  · simpa only [hv, ↓reduceIte, mul_one] using
      (le_rfl : CopyHistory.mass ps history * B ≤ CopyHistory.mass ps history * B)
  · simpa only [hv, ↓reduceIte, mul_zero] using hmB

theorem kernel_future_bound (ps : List Rate) (history : List (CopyHistory.Observation n))
    (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (hnum : 0 < cfg.initialNumerator)
    (r : ℕ) (S : Finset (Fin n)) (v : Fin n) (b : ℕ) (B growth : ℝ)
    (hB : 0 ≤ B) (hgrowth : 0 ≤ growth)
    (hc : CopyHistory.compatible history S) (hp : CopyHistory.past history r)
    (hearly : r < cfg.earlyLevel → r < ps.length ∧
      ((ps.take r).map Rate.value).sum ≤ 1 / 2 ∧
        8 * (b : ℝ) * (Ranks.rate ps r).value / cfg.groups ≤ growth)
    (hin : (Early.searchIn (Backend.roundedRestricted stored input S cfg.inputScale)
      v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b)
    (hout : (Early.searchOut (Backend.roundedRestricted stored input S cfg.inputScale)
      v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤ b)
    (f : Finset (Fin n) → (Fin n → ℕ) → ℝ)
    (hfuture : ∀ history T, CopyHistory.compatible history T →
      CopyHistory.past history (r + 1) →
        futureMoment ps history f T ≤ CopyHistory.mass ps history * B *
          if v ∈ T then 1 else 0) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect
        (Law.masked (CopyHistory.event history) (fun ranks =>
          (kernel cfg hn stored input ranks r S).expect (fun step =>
            (step.children.map fun T => f T ranks).sum))) ≤
      CopyHistory.mass ps history * B * (1 + growth) := by
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  have hmB : 0 ≤ CopyHistory.mass ps history * B :=
    mul_nonneg (CopyHistory.mass_nonneg ps history) hB
  by_cases he : r < cfg.earlyLevel
  · have hh := hearly he
    have hkernel (ranks : Fin n → ℕ) :
        (kernel cfg hn stored input ranks r S).expect (fun step =>
          (step.children.map fun T => f T ranks).sum) =
          (ownerLaw n cfg).expect (fun owners =>
            ((Geometry.fringes G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)
                (distanceScale cfg r) ++
              Geometry.core G S (CopyHistory.pivots S r ranks) (radii cfg r G owners)).map
                fun T => f T ranks).sum) := by
      simp only [kernel, choices, pivotLaw, he, ↓reduceIte, Law.expect_map,
        Law.expect_bind, Law.expect_pure, children]
      rfl
    simp_rw [hkernel]
    exact (early_future_step ps history S G cfg hnum r hh.1 hc hp hh.2.1 v b B hB
      hin hout f hfuture).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hh.2.2) hmB)
  · let mu := choices cfg hn r S (fun _ => 0)
    have hchoices (ranks : Fin n → ℕ) : choices cfg hn r S ranks = mu := by
      dsimp only [mu, choices, pivotLaw]
      simp only [he, ↓reduceIte]
    by_cases hl : r < cfg.maximumLevel
    · let child := fun choice : Choice n cfg =>
        lateChild G S choice.pivots (radii cfg r G choice.owners)
      have hkernel (ranks : Fin n → ℕ) :
          (kernel cfg hn stored input ranks r S).expect (fun step =>
            (step.children.map fun T => f T ranks).sum) =
            mu.expect (fun choice => f (child choice) ranks) := by
        simp only [kernel, Law.expect_map, hchoices, children, he, hl, ↓reduceIte,
          List.map_singleton, List.sum_singleton]
        rfl
      simp_rw [hkernel]
      have h := single_child_future mu ps history S r hc hp child
        (fun choice => lateChild_subset G S choice.pivots _) v B hB f hfuture
      exact h.trans (le_mul_of_one_le_right hmB (by linarith))
    · have hkernel (ranks : Fin n → ℕ) :
          (kernel cfg hn stored input ranks r S).expect (fun step =>
            (step.children.map fun T => f T ranks).sum) = 0 := by
        simp only [kernel, Law.expect_map, children, he, hl, ↓reduceIte,
          List.map_nil, List.sum_nil, Law.expect_const]
      have hfn :
          (fun ranks : Fin n → ℕ => (kernel cfg hn stored input ranks r S).expect
            (fun step => (step.children.map fun T => f T ranks).sum)) = fun _ => 0 :=
        funext hkernel
      rw [hfn]
      have hz := CopyHistory.moment ps history (fun _ => 0)
      simp only [Law.expect_const, mul_zero] at hz
      rw [hz]
      positivity

end

end StreamingSSSP.Hopset.Reference
