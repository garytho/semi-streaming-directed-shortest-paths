module

public import StreamingSSSP.Hopset.TrackedEarlyMoments

@[expose] public section

namespace StreamingSSSP.Hopset.Following

open scoped Classical

noncomputable section

variable {n ns : ℕ} {stored : Implicit.Representation n} {input : List (StoredEdges.Edge n)}
    {sets : Vector (Finset (Fin n)) ns}

theorem weight_append (A : ℕ) (left right : List (TrackedPath stored input sets)) :
    weight A (left ++ right) = weight A left + weight A right := by
  simp only [weight, List.map_append, List.sum_append]

theorem related_append (cfg : Config) (r : ℕ) (known : Fin n → Option (Fin r))
    (left right : List (TrackedPath stored input sets)) :
    related cfg r known (left ++ right) = related cfg r known left + related cfg r known right := by
  simp only [related, List.map_append, List.sum_append]

def advanceAll (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) :
    (paths : List (TrackedPath stored input sets)) →
    (∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) →
    List (TrackedPath stored input (Batched.geometricChildren cfg r stored input sets choices).toArray.toVector)
  | [], _ => []
  | P :: paths, hshort =>
      P.advance cfg r hnum he choices (hshort P (by simp)) ++
        advanceAll cfg r hnum he choices paths
          (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))

theorem advanceAll_weight (cfg : Config) (r : ℕ) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (choices : Fin ns → Reference.Choice n cfg) (paths : List (TrackedPath stored input sets))
    (hshort : ∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) :
    weight cfg.inputScale (advanceAll cfg r hnum he choices paths hshort) ≤ weight cfg.inputScale paths := by
  induction paths with
  | nil => simp [advanceAll, weight]
  | cons P paths ih =>
      simp only [advanceAll, weight_append]
      have hp := P.advance_weight cfg r hnum he choices (hshort P (by simp))
      have ht := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      exact Nat.add_le_add hp ht

theorem expected_advanceAll_count (cfg : Config) (ps : List Rate) (r : ℕ)
    (known : Fin n → Option (Fin r)) (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (paths : List (TrackedPath stored input sets))
    (hshort : ∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts)
    (hin : ∀ i v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ i v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hcut : 48 * b * (Ranks.rate ps r).value / cfg.groups ≤ 1) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      ((advanceAll cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) paths hshort).length : ℝ)) ≤
      2 * paths.length + 2 * (Ranks.rate ps r).value * related cfg r known paths := by
  induction paths with
  | nil => simp [advanceAll, related]
  | cons P paths ih =>
      simp only [advanceAll, List.length_append, Nat.cast_add, Law.expect_add]
      have hp := P.expected_advance_count cfg ps r known hnum he (hshort P (by simp)) b hgrid
        (hin P.node) (hout P.node)
      have ht := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      have hrel := related_append cfg r known [P] paths
      change related cfg r known (P :: paths) = _ at hrel
      rw [hrel]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, Nat.cast_add]
      linarith

theorem expected_advanceAll_related (cfg : Config) (ps : List Rate) (r : ℕ)
    (known : Fin n → Option (Fin r)) (hr : r < ps.length)
    (hprefix : ((ps.take r).map Rate.value).sum ≤ 1 / 2)
    (hnum : 0 < cfg.initialNumerator) (he : r < cfg.earlyLevel)
    (paths : List (TrackedPath stored input sets))
    (hshort : ∀ P ∈ paths, (P.path.searchWeight cfg.inputScale : ℝ) ≤ Reference.distanceScale cfg r) (b : ℕ)
    (hgrid : Reference.distanceScale cfg r ≤ cfg.shifts) (hM : 2 ≤ cfg.groups) (hp : 0 < (Ranks.rate ps r).value)
    (hin : ∀ i v, (Early.searchIn (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hout : ∀ i v, (Early.searchOut (Backend.roundedRestricted stored input (sets.get i) cfg.inputScale) v
      (Early.searchRadius cfg.k cfg.groups (Reference.distanceScale cfg r))).card ≤ b)
    (hbudget : 96 * (b : ℝ) ^ 2 * (Ranks.rate ps r).value ^ 2 ≤ cfg.groups) :
    (currentDraw cfg ps r known ns).expect (fun sample =>
      (related cfg (r + 1) (fun v => RankPrefix.nextKnown r (known v) (sample.1 v))
        (advanceAll cfg r hnum he (Batched.currentChoices cfg sets sample.1 sample.2) paths hshort) : ℝ)) ≤
      18 / (Ranks.rate ps r).value * paths.length := by
  induction paths with
  | nil => simp [advanceAll, related]
  | cons P paths ih =>
      simp only [advanceAll, related_append, Nat.cast_add, Law.expect_add]
      have hhead := P.expected_advance_related_le cfg ps r known hr hprefix hnum he
        (hshort P (by simp)) b hgrid hM hp (hin P.node) (hout P.node) hbudget
      have ht := ih (fun Q hQ => hshort Q (List.mem_cons_of_mem _ hQ))
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

end

end StreamingSSSP.Hopset.Following
