module

public import StreamingReachability.Hopset.Type2Plans
public import StreamingReachability.Hopset.DeferredControl

@[expose] public section

namespace StreamingReachability.Hopset.Following

open scoped Classical

noncomputable section

variable {n ns : ℕ}

structure TrackedPath (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (sets : Vector (Finset (Fin n)) ns) where
  node : Fin ns
  source : Fin n
  target : Fin n
  path : Late.Path stored (StoredEdges.graphOfEdges input) source target
  inside : path.Inside (sets.get node)

namespace TrackedPath

variable {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

def ofChild (i : Fin ns) {A : ℕ} {D : ℝ}
    (C : Late.ChildPiece stored (StoredEdges.graphOfEdges input) (sets.get i) A D) :
    TrackedPath stored input sets :=
  ⟨i, C.source, C.target, C.path, C.inside⟩

def type2Plan (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) :
    Late.Partition stored (StoredEdges.graphOfEdges input) (sets.get P.node) cfg.inputScale
      (Reference.distanceScale cfg r) P.path :=
  Classical.choose (Late.Partition.exists_greedy P.path (sets.get P.node) cfg.inputScale
    (Reference.distanceScale cfg r) (Reference.distanceScale_pos cfg hnum r).le
    (P.path.vertices_inside P.inside))

theorem type2Plan_greedy (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) : (P.type2Plan cfg r hnum).Greedy :=
  Classical.choose_spec (Late.Partition.exists_greedy P.path (sets.get P.node) cfg.inputScale
    (Reference.distanceScale cfg r) (Reference.distanceScale_pos cfg hnum r).le
    (P.path.vertices_inside P.inside))

def split (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) : List (TrackedPath stored input sets) :=
  (P.type2Plan cfg r hnum).pieces.map (ofChild P.node)

theorem split_length (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) :
    (P.split cfg r hnum).length = (P.type2Plan cfg r hnum).type2 + 1 := by
  rw [split, List.length_map]
  exact type2_piece_count _ P.inside

theorem split_short (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P Q : TrackedPath stored input sets) (hQ : Q ∈ P.split cfg r hnum) :
    (Q.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hQ
  exact C.short

theorem split_weight (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) :
    ((P.split cfg r hnum).map fun Q => Q.path.searchWeight cfg.inputScale).sum ≤
      P.path.searchWeight cfg.inputScale := by
  simpa only [split, List.map_map, Function.comp_def, ofChild] using
    (P.type2Plan cfg r hnum).pieces_search_sum_le

theorem split_credit (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (P : TrackedPath stored input sets) :
    ((P.type2Plan cfg r hnum).type2 : ℝ) * Reference.distanceScale cfg r ≤
      P.path.searchWeight cfg.inputScale :=
  type2_credit _ (P.type2Plan_greedy cfg r hnum) (Reference.distanceScale_pos cfg hnum r).le

end TrackedPath

variable {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

def weight (A : ℕ) (paths : List (TrackedPath stored input sets)) : ℕ :=
  (paths.map fun P => P.path.searchWeight A).sum

def related (cfg : Config) (r : ℕ) (known : Fin n → Option (Fin r))
    (paths : List (TrackedPath stored input sets)) : ℕ :=
  (paths.map fun P =>
    (relatedVertices (Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale) P.path.vertices
      (RankPrefix.eligible r known (sets.get P.node))
      (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card).sum

def splitAll (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (paths : List (TrackedPath stored input sets)) : List (TrackedPath stored input sets) :=
  paths.flatMap (fun P => P.split cfg r hnum)

def splits (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (paths : List (TrackedPath stored input sets)) : ℕ :=
  (paths.map fun P => (P.type2Plan cfg r hnum).type2).sum

theorem splitAll_length (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (paths : List (TrackedPath stored input sets)) :
    (splitAll cfg r hnum paths).length = paths.length + splits cfg r hnum paths := by
  induction paths with
  | nil => simp [splitAll, splits]
  | cons P paths ih =>
      simp only [splitAll, List.flatMap_cons, List.length_append, TrackedPath.split_length,
        List.length_cons, splits, List.map_cons, List.sum_cons] at *
      omega

theorem splitAll_short (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (paths : List (TrackedPath stored input sets)) :
    ∀ Q ∈ splitAll cfg r hnum paths,
      (Q.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r := by
  intro Q hQ
  obtain ⟨P, hP, hQ⟩ := List.mem_flatMap.mp hQ
  exact P.split_short cfg r hnum Q hQ

theorem splitAll_weight (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (paths : List (TrackedPath stored input sets)) :
    weight cfg.inputScale (splitAll cfg r hnum paths) ≤ weight cfg.inputScale paths := by
  induction paths with
  | nil => simp [splitAll, weight]
  | cons P paths ih =>
      simp only [weight, splitAll, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons] at *
      exact Nat.add_le_add (P.split_weight cfg r hnum) ih

theorem splits_credit (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (paths : List (TrackedPath stored input sets)) :
    (splits cfg r hnum paths : ℝ) * Reference.distanceScale cfg r ≤ weight cfg.inputScale paths := by
  induction paths with
  | nil => simp [splits, weight]
  | cons P paths ih =>
      simp only [splits, weight, List.map_cons, List.sum_cons, Nat.cast_add, add_mul] at *
      exact add_le_add (P.split_credit cfg r hnum) ih

theorem splitAll_related (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator)
    (known : Fin n → Option (Fin r)) (paths : List (TrackedPath stored input sets)) (b : ℕ)
    (hin : ∀ i v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ i v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b) :
    related cfg r known (splitAll cfg r hnum paths) ≤
      related cfg r known paths + 2 * b * splits cfg r hnum paths := by
  have hpoint (P : TrackedPath stored input sets) :
      related cfg r known (P.split cfg r hnum) ≤
        related cfg r known [P] + 2 * b * (P.type2Plan cfg r hnum).type2 := by
    have hs := type2_related_le (P.type2Plan cfg r hnum) P.inside cfg.inputScale_pos
      (Reference.distanceScale_pos cfg hnum r).le (RankPrefix.eligible r known (sets.get P.node))
      cfg.k cfg.groups b (hin P.node) (hout P.node)
    have hround : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node)) =
        Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale := rfl
    rw [hround] at hs
    simpa only [related, TrackedPath.split, List.map_map, Function.comp_def, TrackedPath.ofChild,
      List.map_singleton, List.sum_singleton] using hs
  induction paths with
  | nil => simp [splitAll, related, splits]
  | cons P paths ih =>
      simp only [splitAll, related, splits, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Nat.add_zero, Nat.mul_add] at *
      have hp := hpoint P
      omega

end

end StreamingReachability.Hopset.Following
