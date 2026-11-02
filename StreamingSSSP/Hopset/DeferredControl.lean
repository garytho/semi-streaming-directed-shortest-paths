module

public import StreamingSSSP.Hopset.ControlTrace
public import StreamingSSSP.Hopset.StoppedBounds

@[expose] public section

namespace StreamingSSSP.Hopset.Batched

open scoped Classical

noncomputable section

variable {n ns : ℕ}

def currentChoices (cfg : Config) (sets : Vector (Finset (Fin n)) ns) (coins : Fin n → Bool)
    (owners : Fin ns → Reference.Owners n cfg) : Fin ns → Reference.Choice n cfg :=
  fun i => ⟨(sets.get i).filter (fun v => coins v = true), owners i⟩

theorem currentChoices_decide (cfg : Config) (sets : Vector (Finset (Fin n)) ns)
    (ranks : Fin n → ℕ) (r : ℕ) (owners : Fin ns → Reference.Owners n cfg) :
    currentChoices cfg sets (fun v => decide (ranks v = r)) owners =
      fun i => ⟨CopyHistory.pivots (sets.get i) r ranks, owners i⟩ := by
  funext i
  change Reference.Choice.mk ((sets.get i).filter (fun v => decide (ranks v = r) = true)) (owners i) = _
  congr 1

theorem control_rank_irrelevant (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (input : List (StoredEdges.Edge n)) (left right : Vector ℕ n) (fuel r : ℕ)
    (queue : List (Finset (Fin n))) (hr : cfg.earlyLevel ≤ r) (f : List (ControlEntry n cfg) → ℝ) :
    (controlTraceLaw cfg hn stored input left fuel r queue).expect f =
      (controlTraceLaw cfg hn stored input right fuel r queue).expect f := by
  induction fuel generalizing r queue f with
  | zero => rfl
  | succ fuel ih =>
      have he : ¬ r < cfg.earlyLevel := by omega
      have hc : choiceRowsLaw cfg hn left r queue.toArray.toVector =
          choiceRowsLaw cfg hn right r queue.toArray.toVector := by
        simp only [choiceRowsLaw, he, ↓reduceIte]
      by_cases hg : AllGood cfg stored input r queue
      · simp only [controlTraceLaw, hg, ↓reduceIte, Law.expect_bind, Law.expect_map]
        rw [hc]
        apply congrArg (choiceRowsLaw cfg hn right r queue.toArray.toVector).expect
        funext choices
        exact ih (r + 1) _ (by omega) (fun tail => f (⟨r, queue, choices⟩ :: tail))
      · simp only [controlTraceLaw, hg, ↓reduceIte]

def deferredControlLaw (cfg : Config) (hn : 0 < n) (ps : List Rate)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n)) :
    ℕ → (r : ℕ) → (Fin n → Option (Fin r)) → List (Finset (Fin n)) → Law (List (ControlEntry n cfg))
  | 0, _, _, _ => Law.pure []
  | fuel + 1, r, known, queue =>
      if r < cfg.earlyLevel then
        if AllGood cfg stored input r queue then
          (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).bind fun coins =>
            (Law.family queue.toArray.size (fun _ => Reference.ownerLaw n cfg)).bind fun owners =>
              let choices := currentChoices cfg queue.toArray.toVector coins owners
              let next := geometricChildren cfg r stored input queue.toArray.toVector choices
              (deferredControlLaw cfg hn ps stored input fuel (r + 1)
                (fun v => RankPrefix.nextKnown r (known v) (coins v)) next).map
                  (⟨r, queue, choices⟩ :: ·)
        else Law.pure []
      else controlTraceLaw cfg hn stored input (Vector.replicate n 0) (fuel + 1) r queue

theorem deferred_control_equiv (cfg : Config) (hn : 0 < n) (ps : List Rate)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hprefix : ∀ r < cfg.earlyLevel, r < ps.length ∧ ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (fuel r : ℕ) (known : Fin n → Option (Fin r)) (queue : List (Finset (Fin n)))
    (f : List (ControlEntry n cfg) → ℝ) :
    (RankPrefix.law ps r known).expect (fun ranks =>
        (controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel r queue).expect f) =
      (deferredControlLaw cfg hn ps stored input fuel r known queue).expect f := by
  induction fuel generalizing r known queue f with
  | zero => simp [controlTraceLaw, deferredControlLaw]
  | succ fuel ih =>
      by_cases he : r < cfg.earlyLevel
      · by_cases hg : AllGood cfg stored input r queue
        · let sets := queue.toArray.toVector
          let ownersLaw := Law.family queue.toArray.size (fun _ => Reference.ownerLaw n cfg)
          let choices := fun coins owners => currentChoices cfg sets coins owners
          let next := fun coins owners => geometricChildren cfg r stored input sets (choices coins owners)
          let F := fun (coins : Fin n → Bool) (ranks : Fin n → ℕ) =>
            ownersLaw.expect (fun owners =>
              (controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel (r + 1) (next coins owners)).expect
                (fun tail => f (⟨r, queue, choices coins owners⟩ :: tail)))
          have hobs := RankPrefix.next_observed ps r (hprefix r he).1 (hprefix r he).2 known F
          dsimp only [F, next, choices] at hobs
          simp_rw [currentChoices_decide] at hobs
          calc
            _ = (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect (fun coins =>
                (RankPrefix.law ps (r + 1) (fun v => RankPrefix.nextKnown r (known v) (coins v))).expect
                  (F coins)) := by
              simpa only [controlTraceLaw, hg, ↓reduceIte, choiceRowsLaw, he, Law.expect_bind,
                Law.expect_map, F, next, choices, Vector.get_ofFn,
                CopyHistory.pivots, decide_eq_true_eq, sets, ownersLaw] using hobs
            _ = _ := by
              simp only [deferredControlLaw, he, hg, ↓reduceIte, Law.expect_bind, Law.expect_map]
              apply congrArg (Law.family n (fun v => RankPrefix.currentLaw ps r (known v))).expect
              funext coins
              dsimp only [F]
              rw [Law.expect_comm
                (RankPrefix.law ps (r + 1) (fun v => RankPrefix.nextKnown r (known v) (coins v))) ownersLaw]
              apply congrArg ownersLaw.expect
              funext owners
              exact ih (r + 1) (fun v => RankPrefix.nextKnown r (known v) (coins v))
                (next coins owners) (fun tail => f (⟨r, queue, choices coins owners⟩ :: tail))
        · simp only [deferredControlLaw, controlTraceLaw, he, hg, ↓reduceIte, Law.expect_pure, Law.expect_const]
      · simp only [deferredControlLaw, he, ↓reduceIte]
        calc
          _ = (RankPrefix.law ps r known).expect (fun _ =>
              (controlTraceLaw cfg hn stored input (Vector.replicate n 0) (fuel + 1) r queue).expect f) := by
            apply congrArg (RankPrefix.law ps r known).expect
            funext ranks
            exact control_rank_irrelevant cfg hn stored input _ _ _ _ _ (by omega) f
          _ = _ := Law.expect_const _ _

theorem initial_deferred_equiv (cfg : Config) (hn : 0 < n) (ps : List Rate)
    (stored : Implicit.Representation n) (input : List (StoredEdges.Edge n))
    (hprefix : ∀ r < cfg.earlyLevel, r < ps.length ∧ ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (fuel : ℕ) (f : List (ControlEntry n cfg) → ℝ) :
    (Law.family n (fun _ => Ranks.firstHit ps)).expect (fun ranks =>
        (controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 [Finset.univ]).expect f) =
      (deferredControlLaw cfg hn ps stored input fuel 0 (fun _ => none) [Finset.univ]).expect f := by
  rw [← RankPrefix.zero_expect ps
    (fun ranks => (controlTraceLaw cfg hn stored input (Vector.ofFn ranks) fuel 0 [Finset.univ]).expect f)]
  exact deferred_control_equiv cfg hn ps stored input hprefix fuel 0 (fun _ => none) [Finset.univ] f

end

end StreamingSSSP.Hopset.Batched
