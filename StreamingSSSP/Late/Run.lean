module

public import StreamingSSSP.Late.Plan

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

/-- Remaining depth indexes the rates backwards. Depth zero is the final,
all-vertices-pivot level, not another Bernoulli trial. -/
structure Config where
  A : ℕ
  positive_rounding : 0 < A
  k : ℕ
  M : ℕ
  N : ℕ
  positive_k : 0 < k
  positive_groups : 0 < M
  positive_shifts : 0 < N
  rate : ℕ → ℝ
  rate_nonneg : ∀ r, 0 ≤ rate r
  rate_le_one : ∀ r, rate r ≤ 1
  ballBound : ℕ → ℕ

namespace Config

variable {n : ℕ}

abbrev Stage (C : Config) (n : ℕ) := List (Fin n × (Fin C.M × Fin C.N))

def owner (C : Config) : Law (Fin C.M × Fin C.N) :=
  Law.uniformPair C.M C.N C.positive_groups C.positive_shifts

def fallback (C : Config) : Fin C.M × Fin C.N :=
  (⟨0, C.positive_groups⟩, ⟨0, C.positive_shifts⟩)

def radii (C : Config) (H : Graph (Fin n)) (D : ℝ) (xs : C.Stage n) : Fin n → ℝ :=
  radiusFor (radius H D C.k C.M C.N C.positive_k) C.fallback xs

def search (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) : Graph (Fin n) :=
  rounded C.A (R.restricted G S)

def child (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) : Finset (Fin n) :=
  emptyChild (C.search R G S) S (Sampling.pivots xs) (C.radii (C.search R G S) D xs)

def stageBlocks (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) : List (Finset (Fin n)) :=
  (Sampling.pivots xs).toList.map fun p =>
    block (C.search R G S) S p (C.radii (C.search R G S) D xs p) D

def stageGraph (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) : Graph (Fin n) :=
  closures (R.base G) (R.blocks ++ C.stageBlocks R G S D xs)

def blocks (C : Config) (R : Representation n) (G : Graph (Fin n)) :
    Finset (Fin n) → ℝ → List (C.Stage n) → List (Finset (Fin n))
  | _, _, [] => []
  | S, D, xs :: ys =>
      C.stageBlocks R G S D xs ++ C.blocks R G (C.child R G S D xs) (D / 4) ys

def graph (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n)) : Graph (Fin n) :=
  closures (R.base G) (R.blocks ++ C.blocks R G S D run)

theorem stage_le_original (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) (u v : Fin n) :
    C.stageGraph R G S D xs u v ≤ R.graph G u v :=
  closures_mono R.blocks _ (fun _ _ => le_rfl) (fun _ h => List.mem_append_left _ h) u v

theorem graph_le_original (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n)) (u v : Fin n) :
    C.graph R G S D run u v ≤ R.graph G u v :=
  closures_mono R.blocks _ (fun _ _ => le_rfl) (fun _ h => List.mem_append_left _ h) u v

theorem stage_le_block (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) {p : Fin n}
    (hp : p ∈ Sampling.pivots xs) (u v : Fin n) :
    C.stageGraph R G S D xs u v ≤ closure (R.base G)
      (block (C.search R G S) S p (C.radii (C.search R G S) D xs p) D) u v := by
  apply closures_le_member
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hp, rfl⟩

theorem graph_cons_le_stage (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) (ys : List (C.Stage n)) (u v : Fin n) :
    C.graph R G S D (xs :: ys) u v ≤ C.stageGraph R G S D xs u v := by
  apply closures_mono _ _ (fun _ _ => le_rfl)
  intro B hB
  rcases List.mem_append.mp hB with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_left _ h)

theorem graph_cons_le_child (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (xs : C.Stage n) (ys : List (C.Stage n)) (u v : Fin n) :
    C.graph R G S D (xs :: ys) u v ≤
      C.graph R G (C.child R G S D xs) (D / 4) ys u v := by
  apply closures_mono _ _ (fun _ _ => le_rfl)
  intro B hB
  rcases List.mem_append.mp hB with h | h
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ (List.mem_append_right _ h)

def fresh (C : Config) (S : Finset (Fin n)) (r : ℕ) : Law (C.Stage n) :=
  Sampling.marked (fun _ : Fin n => C.owner) (C.rate r)
    (C.rate_nonneg r) (C.rate_le_one r) S.toList

def allOwners (C : Config) : List (Fin n) → Law (C.Stage n)
  | [] => Law.pure []
  | v :: vs => C.owner.bind fun o => (C.allOwners vs).map ((v, o) :: ·)

theorem allOwners_keys (C : Config) (vs : List (Fin n)) :
    Sampling.Holds (C.allOwners vs) (fun xs => xs.map Prod.fst = vs) := by
  induction vs with
  | nil => exact Sampling.holds_pure [] _ rfl
  | cons v vs ih =>
      apply Sampling.holds_bind
      intro o
      exact Sampling.holds_map ih ((v, o) :: ·) _
        (fun xs h => by simpa only [List.map_cons] using congrArg (v :: ·) h)

theorem allOwners_pivots (C : Config) (S : Finset (Fin n)) :
    Sampling.Holds (C.allOwners S.toList) (fun xs => Sampling.pivots xs = S) :=
  Sampling.holds_mono (C.allOwners_keys S.toList) (fun xs h => by
    simp [Sampling.pivots, h])

/-- One actual recursion chain: fresh independent late pivots, the unchanged
minimum-shell group/shift rule, one empty-label child, and scale division by 4. -/
def law (C : Config) (R : Representation n) (G : Graph (Fin n)) :
    ℕ → Finset (Fin n) → ℝ → Law (List (C.Stage n))
  | 0, S, _ => (C.allOwners S.toList).map (fun xs => [xs])
  | r + 1, S, D => (C.fresh S (r + 1)).bind fun xs =>
      (C.law R G r (C.child R G S D xs) (D / 4)).map (xs :: ·)

def BallsGood (C : Config) (R : Representation n) (G : Graph (Fin n))
    (r : ℕ) (S : Finset (Fin n)) (D : ℝ) : Prop :=
  ∀ v ∈ S,
    (searchIn (C.search R G S) v (searchRadius C.k C.M D)).card ≤ C.ballBound r ∧
    (searchOut (C.search R G S) v (searchRadius C.k C.M D)).card ≤ C.ballBound r

def Good (C : Config) (R : Representation n) (G : Graph (Fin n)) :
    ℕ → Finset (Fin n) → ℝ → List (C.Stage n) → Prop
  | 0, _, _, run => run.length = 1
  | _ + 1, _, _, [] => False
  | r + 1, S, D, xs :: ys =>
      C.BallsGood R G (r + 1) S D ∧ C.Good R G r (C.child R G S D xs) (D / 4) ys

def path (C : Config) (R : Representation n) (G : Graph (Fin n))
    {s t : Fin n} (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (run : List (C.Stage n)) : Route (C.graph R G S D run) s t Q.micro :=
  Route.best _ (Q.originalRoute _ (C.graph_le_original R G S D run))

theorem path_simple (C : Config) (R : Representation n) (G : Graph (Fin n))
    {s t : Fin n} (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (run : List (C.Stage n)) : (C.path R G Q S D run).vertices.Nodup :=
  Route.best_nodup _ _

def stoppedHops (C : Config) (R : Representation n) (G : Graph (Fin n))
    {s t : Fin n} (Q : Path R G s t) (r : ℕ) (S : Finset (Fin n)) (D : ℝ)
    (run : List (C.Stage n)) : ℝ :=
  if C.Good R G r S D run then ((C.path R G Q S D run).hops : ℝ) else 0

theorem stoppedHops_nonneg (C : Config) (R : Representation n) (G : Graph (Fin n))
    {s t : Fin n} (Q : Path R G s t) (r : ℕ) (S : Finset (Fin n)) (D : ℝ)
    (run : List (C.Stage n)) : 0 ≤ C.stoppedHops R G Q r S D run := by
  unfold stoppedHops
  split_ifs <;> positivity

theorem radii_nonneg (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (hD : 0 < D) (xs : C.Stage n) (p : Fin n) :
    0 ≤ C.radii (C.search R G S) D xs p := by
  have h := (radius_bounds (C.search R G S) D C.k C.M C.N C.positive_k hD p
    (Sampling.ownerFor C.fallback xs p)).1
  have hl : 0 ≤ lambda C.k C.M * D := by unfold lambda; positivity
  exact hl.trans h

end Config

end

end StreamingSSSP.Late
