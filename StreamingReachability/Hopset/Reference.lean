module

public import StreamingReachability.Hopset.NodeGeometry
public import StreamingReachability.Hopset.BallProfile
public import StreamingReachability.Hopset.HistoryTransitions
public import StreamingReachability.Probability.Branching
public import StreamingReachability.Early.Sampling

@[expose] public section

namespace StreamingReachability.Hopset.Reference

open scoped Classical BigOperators

noncomputable section

variable {n : ℕ}

abbrev Owners (n : ℕ) (cfg : Config) := Fin n → Fin cfg.groups × Fin cfg.shifts

structure Choice (n : ℕ) (cfg : Config) where
  pivots : Finset (Fin n)
  owners : Owners n cfg

def ownerLaw (n : ℕ) (cfg : Config) : Law (Owners n cfg) :=
  Law.family n fun _ => Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos

def distanceScale (cfg : Config) (r : ℕ) : ℝ :=
  (cfg.initialNumerator : ℝ) / cfg.denominatorAt r

def radii (cfg : Config) (r : ℕ) (G : Graph (Fin n)) (owners : Owners n cfg) : Fin n → ℝ :=
  fun p => Late.radius G (distanceScale cfg r) cfg.k cfg.groups cfg.shifts cfg.k_pos p (owners p)

def pivotLaw (cfg : Config) (hn : 0 < n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) : Law (Finset (Fin n)) :=
  if r < cfg.earlyLevel then Law.pure (CopyHistory.pivots S r ranks)
  else if r < cfg.maximumLevel then
    Law.subset (fun _ : Fin n => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value)
      (fun _ => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_nonneg)
      (fun _ => (PivotProfile.rate n hn cfg.k cfg.logarithm r).value_le_one) (members S)
  else Law.pure S

def choices (cfg : Config) (hn : 0 < n) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) : Law (Choice n cfg) :=
  (pivotLaw cfg hn r S ranks).bind fun P =>
    (ownerLaw n cfg).map fun owners => ⟨P, owners⟩

def lateChild (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) :
    Finset (Fin n) :=
  S.filter fun v => Geometry.labels G P rho v = []

def children (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) :
    List (Finset (Fin n)) :=
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  let rho := radii cfg r G choice.owners
  if r < cfg.earlyLevel then
    Geometry.fringes G S choice.pivots rho (distanceScale cfg r) ++
      Geometry.core G S choice.pivots rho
  else if r < cfg.maximumLevel then [lateChild G S choice.pivots rho] else []

def blocks (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) :
    List (Finset (Fin n)) :=
  if r < cfg.earlyLevel then [] else
    let G := Backend.roundedRestricted stored input S cfg.inputScale
    let rho := radii cfg r G choice.owners
    (members choice.pivots).map fun p =>
      S ∩ Early.bothBall G p (rho p + distanceScale cfg r)

def kernel (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) (r : ℕ) (S : Finset (Fin n)) :
    Law (Branching.Step (Finset (Fin n)) (Choice n cfg)) :=
  (choices cfg hn r S ranks).map fun choice =>
    ⟨choice, children cfg stored input r S choice⟩

def vertexWeight (stored : Implicit.Representation n) (v : Fin n) : ℕ :=
  1 + (stored.blocks.filter fun B => decide (v ∈ B)).length

def searchRecords (stored : Implicit.Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (p : Fin n) (radius : ℕ) : ℕ :=
  ∑ v ∈ S, ((if G.dist p v ≤ (radius : Distance) then vertexWeight stored v else 0) +
    if G.dist v p ≤ (radius : Distance) then vertexWeight stored v else 0)

def advancePivots (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (ranks : Fin n → ℕ) : Finset (Fin n) :=
  S.filter fun v => advanceWanted cfg r (ranks v) = true

def nodeRecords (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ)
    (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) : ℕ :=
  let G := Backend.roundedRestricted stored input S cfg.inputScale
  (choice.pivots.sum fun p => searchRecords stored G S p (cfg.searchRadius r)) +
    if r < cfg.earlyLevel then
      (advancePivots cfg r S ranks).sum fun p => searchRecords stored G S p (cfg.searchRadius r)
    else 0

def globalRecords (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (ranks : Fin n → ℕ) : ℕ :=
  let G := Backend.roundedRestricted stored input Finset.univ cfg.inputScale
  (Finset.univ.filter fun p => globalWanted cfg (ranks p) = true).sum fun p =>
    searchRecords stored G Finset.univ p cfg.globalRadius

def BallsGood (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) : Prop :=
  ∀ v ∈ S,
    (Early.searchIn (Backend.roundedRestricted stored input S cfg.inputScale)
      v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤
        Parameters.ballSize n r ∧
    (Early.searchOut (Backend.roundedRestricted stored input S cfg.inputScale)
      v (Early.searchRadius cfg.k cfg.groups (distanceScale cfg r))).card ≤
        Parameters.ballSize n r

theorem children_subset (cfg : Config) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (r : ℕ) (S : Finset (Fin n)) (choice : Choice n cfg) :
    ∀ T ∈ children cfg stored input r S choice, T ⊆ S := by
  dsimp only [children]
  split_ifs with he hl
  · intro T hT
    rcases List.mem_append.mp hT with h | h
    · exact Geometry.fringe_subset _ S _ _ _ T h
    · exact Geometry.core_subset _ S _ _ T h
  · intro T hT
    have h := List.mem_singleton.mp hT
    subst T
    exact Finset.filter_subset _ _
  · simp

theorem lateChild_subset (G : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ) :
    lateChild G S P rho ⊆ S := Finset.filter_subset _ _

end

end StreamingReachability.Hopset.Reference
