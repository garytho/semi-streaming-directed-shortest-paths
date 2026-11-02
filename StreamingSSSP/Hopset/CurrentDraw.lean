module

public import StreamingSSSP.Hopset.TrackedEarlyRelated
public import StreamingSSSP.Hopset.CurrentPathBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n ns : ℕ}

def currentDraw (cfg : Config) (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r)) (ns : ℕ) :
    Law ((Fin n → Bool) × (Fin ns → Reference.Owners n cfg)) :=
  (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).bind fun coins =>
    (Law.family ns (fun _ => Reference.ownerLaw n cfg)).map (fun owners => (coins, owners))

theorem currentDraw_local (cfg : Config) (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r))
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns)
    (f : Finset (Fin n) → Reference.Owners n cfg → ℝ) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      let choice := Batched.currentChoices cfg sets sample.1 sample.2 i
      f choice.pivots choice.owners) =
    (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
      (Reference.ownerLaw n cfg).expect (fun owners => f ((sets.get i).filter fun v => coins v = true) owners)) := by
  simp only [currentDraw, Law.expect_bind, Law.expect_map]
  apply congrArg (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect
  funext coins
  exact Law.family_marginal ns (fun _ => Reference.ownerLaw n cfg) i
    (fun owners => f ((sets.get i).filter fun v => coins v = true) owners)

namespace TrackedPath

variable {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

theorem localRadii_model (cfg : Config) (r : ℕ) (P : TrackedPath stored input sets)
    (choice : Reference.Choice n cfg) :
    P.localRadii cfg r choice =
      Reference.radii cfg r (Late.rounded cfg.inputScale
        (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node))) choice.owners := rfl

theorem localView_near (cfg : Config) (r : ℕ) (known : Fin n → Option (Fin r))
    (P : TrackedPath stored input sets)
    (hshort : (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    (Early.nearPivots (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
      (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card =
      Following.related cfg r known [P] := by
  have h := relatedVertices_shortPath (P.localView cfg r hshort) (RankPrefix.eligible r known (sets.get P.node))
    (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))
  have hround : Late.rounded cfg.inputScale (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node)) =
      Backend.roundedRestricted stored input (sets.get P.node) cfg.inputScale := rfl
  have he := congrArg (fun H => relatedVertices H P.path.vertices (RankPrefix.eligible r known (sets.get P.node))
    (Early.nearRadius cfg.k cfg.groups (Reference.distanceScale cfg r))) hround
  have hset := h.symm.trans he
  simpa only [Following.related, List.map_singleton, List.sum_singleton] using congrArg Finset.card hset

theorem currentDraw_path_local (cfg : Config) (ps : List Rate) (r : ℕ) (known : Fin n → Option (Fin r))
    (P : TrackedPath stored input sets) (f : Finset (Fin n) → (Fin n → ℝ) → ℝ) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      let choice := Batched.currentChoices cfg sets sample.1 sample.2 P.node
      f choice.pivots (P.localRadii cfg r choice)) =
    (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
      (Reference.ownerLaw n cfg).expect (fun owners =>
        f ((sets.get P.node).filter fun v => coins v = true)
          (Reference.radii cfg r (Late.rounded cfg.inputScale
            (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node))) owners))) := by
  simp_rw [localRadii_model]
  exact currentDraw_local cfg ps r known sets P.node (fun pivots owners =>
    f pivots (Reference.radii cfg r (Late.rounded cfg.inputScale
      (stored.restricted (StoredEdges.graphOfEdges input) (sets.get P.node))) owners))

end TrackedPath

end

end StreamingSSSP.Hopset.Following
