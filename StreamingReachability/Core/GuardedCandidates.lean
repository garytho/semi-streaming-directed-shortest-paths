module

public import StreamingReachability.Core.RegisteredSpace
public import StreamingReachability.Core.GuardedCoverage

@[expose] public section

namespace StreamingReachability.Core.GuardedDriver

open StoredEdges

variable {n nb ns nq : ℕ}

def CandidatesCovered (registry : RecordGuard.Registry n nq) (C : Vector (Finset (Fin n)) nq) : Prop :=
  ∀ j, ∀ v ∈ C.get j, (j, v) ∈ registry.seen

theorem ordinaryOne_cover (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (j : Fin nq)
    (before after : RecordGuard.Registry n nq) (C D : Vector (Finset (Fin n)) nq)
    (hc : CandidatesCovered before C)
    (h : ordinaryOne c budget r old raw j before C = .ok (after, D)) : CandidatesCovered after D := by
  unfold ordinaryOne at h
  cases he : ordinaryTarget c r old raw j with
  | none =>
      simp only [he] at h
      cases h
      exact hc
  | some v =>
      simp only [he] at h
      cases hr : RecordGuard.reserve c budget (j, v) before with
      | error reason => simp [hr] at h
      | ok next =>
          simp only [hr] at h
          have hreg := congrArg Prod.fst (Except.ok.inj h)
          have hC := congrArg Prod.snd (Except.ok.inj h)
          dsimp only at hreg hC
          rw [← hreg, ← hC]
          have hm := reserve_mono c budget (j, v) before next hr
          intro k w hw
          rw [VectorStore.get_set] at hw
          by_cases hk : k = j
          · subst k
            rw [ite_eq_left rfl] at hw
            rcases Finset.mem_insert.mp hw with hw | hw
            · subst w
              rw [RecordGuard.reserve_seen c budget (j, v) before next hr]
              exact Finset.mem_insert_self _ _
            · exact hm (hc j w hw)
          · rw [ite_eq_right hk] at hw
            exact hm (hc k w hw)

theorem ordinaryQueries_cover (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (raw : Edge n) (indices : List (Fin nq))
    (before after : RecordGuard.Registry n nq) (C D : Vector (Finset (Fin n)) nq)
    (hc : CandidatesCovered before C)
    (h : ordinaryQueries c budget r old raw indices before C = .ok (after, D)) :
    CandidatesCovered after D := by
  induction indices generalizing before C with
  | nil => cases h; exact hc
  | cons j js ih =>
      rw [ordinaryQueries] at h
      cases ho : ordinaryOne c budget r old raw j before C with
      | error reason => simp [ho] at h
      | ok pair =>
          obtain ⟨next, E⟩ := pair
          simp only [ho] at h
          exact ih next E (ordinaryOne_cover c budget r old raw j before next C E hc ho) h

theorem ordinaryScan_cover (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (edges : List (Edge n))
    (before after : RecordGuard.Registry n nq) (C D : Vector (Finset (Fin n)) nq)
    (hc : CandidatesCovered before C)
    (h : ordinaryScan c budget r old edges before C = .ok (after, D)) : CandidatesCovered after D := by
  induction edges generalizing before C with
  | nil => cases h; exact hc
  | cons raw edges ih =>
      rw [ordinaryScan] at h
      cases ho : ordinaryQueries c budget r old raw (List.finRange nq) before C with
      | error reason => simp [ho] at h
      | ok pair =>
          obtain ⟨next, E⟩ := pair
          simp only [ho] at h
          exact ih next E (ordinaryQueries_cover c budget r old raw _ before next C E hc ho) h

theorem ordinary_cover (c : Shared.Catalog n nb ns nq) (budget r : ℕ)
    (old : BatchDriver.States n nb nq) (stored input : List (Edge n))
    (before after : RecordGuard.Registry n nq) (C : Vector (Finset (Fin n)) nq)
    (h : ordinary c budget r old stored input before = .ok (after, C)) : CandidatesCovered after C := by
  unfold ordinary at h
  cases hs : ordinaryScan c budget r old stored before (Vector.replicate nq ∅) with
  | error reason => simp [hs] at h
  | ok pair =>
      obtain ⟨next, E⟩ := pair
      simp only [hs] at h
      have hfirst := ordinaryScan_cover c budget r old stored before next _ E
        (by intro j v hv; simp at hv) hs
      exact ordinaryScan_cover c budget r old input next after E C hfirst h

theorem candidate_cells (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : RecordGuard.Registry n nq) (C : Vector (Finset (Fin n)) nq)
    (hv : RecordGuard.Valid c budget registry) (hc : CandidatesCovered registry C) (hq : nq ≤ budget) :
    BatchDriver.ordinaryCells C ≤ 4 * budget := by
  have hcard : (∑ j : Fin nq, (C.get j).card) ≤ RecordGuard.weight c registry.seen := by
    rw [RecordGuard.weight_sections]
    apply Finset.sum_le_sum
    intro j _
    apply (Finset.card_le_card ?_).trans (Nat.le_add_right _ _)
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc j v hv⟩
  have hweight : RecordGuard.weight c registry.seen ≤ budget := hv.1 ▸ hv.2
  unfold BatchDriver.ordinaryCells
  omega

end StreamingReachability.Core.GuardedDriver
