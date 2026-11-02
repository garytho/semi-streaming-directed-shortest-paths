module

public import StreamingReachability.Hopset.ControlTrace

@[expose] public section

namespace StreamingReachability.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

theorem frame_node_choice (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (rank : Vector ℕ n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (f : Reference.Choice n cfg → ℝ) :
    (frameLaw cfg hn stored input rank r sets).expect (fun frame => f (frame.choices i)) =
      (Reference.choices cfg hn r (sets.get i) (fun v => rank.get v)).expect f := by
  rw [frameLaw_choices cfg hn stored input rank r sets (fun choices => f (choices i))]
  by_cases he : r < cfg.earlyLevel
  · simp only [choiceRowsLaw, Reference.choices, Reference.pivotLaw, he, ↓reduceIte,
      Law.expect_bind, Law.expect_map, Law.expect_pure]
    exact Law.family_marginal ns (fun _ => Reference.ownerLaw n cfg) i
      (fun owners => f ⟨CopyHistory.pivots (sets.get i) r (fun v => rank.get v), owners⟩)
  · simp only [choiceRowsLaw, he, ↓reduceIte, Law.expect_bind, Law.expect_map]
    have howner (P : Fin ns → Finset (Fin n)) :
        (Law.family ns (fun _ => Reference.ownerLaw n cfg)).expect (fun rows => f ⟨P i, rows i⟩) =
          (Reference.ownerLaw n cfg).expect (fun owners => f ⟨P i, owners⟩) :=
      Law.family_marginal ns (fun _ => Reference.ownerLaw n cfg) i (fun owners => f ⟨P i, owners⟩)
    simp_rw [howner]
    rw [Law.family_marginal ns (lateDraw cfg hn r sets) i
      (fun P => (Reference.ownerLaw n cfg).expect (fun owners => f ⟨P, owners⟩)),
      lateDraw_pivotLaw cfg hn r sets i (fun v => rank.get v) he]
    simp only [Reference.choices, Law.expect_bind, Law.expect_map]

end

end StreamingReachability.Hopset.Batched
