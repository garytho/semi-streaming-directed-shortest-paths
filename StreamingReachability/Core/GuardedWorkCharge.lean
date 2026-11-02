module

public import StreamingReachability.Core.TaskPosts
public import StreamingReachability.Core.ExecutionSpace

@[expose] public section

namespace StreamingReachability.Core.GuardedEngine

open StoredEdges

variable {n nb ns nq N : ℕ}

def incidenceKeys (c : Shared.Catalog n nb ns nq) (keys : Finset (RecordGuard.Key n nq))
    (origin : Fin nq × Fin nb) : Finset (Fin n) :=
  RecordGuard.verticesAt keys origin.1 ∩ c.blocks.get origin.2

def Charged (c : Shared.Catalog n nb ns nq) (x : ℕ) (keys : Finset (RecordGuard.Key n nq))
    (origin : Fin nq × Fin nb) : Shared.Engine.Task n nb nq → Prop
  | .active job =>
      let b := (Shared.block c job.searchId job.blockId).card
      b ≤ x ∧ job.spentReservations + b = b * job.threshold ∧
        job.threshold ≤ 2 * (incidenceKeys c keys origin).card
  | .finished out => out.reservations ≤ 4 * x * (incidenceKeys c keys origin).card

theorem incidenceKeys_mono (c : Shared.Catalog n nb ns nq)
    {before after : Finset (RecordGuard.Key n nq)} (hm : before ⊆ after)
    (origin : Fin nq × Fin nb) : incidenceKeys c before origin ⊆ incidenceKeys c after origin := by
  intro v hv
  obtain ⟨hk, hb⟩ := Finset.mem_inter.mp hv
  exact Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm (Finset.mem_filter.mp hk).2⟩, hb⟩

theorem charged_mono (c : Shared.Catalog n nb ns nq) (x : ℕ)
    {before after : Finset (RecordGuard.Key n nq)} (hm : before ⊆ after)
    (origin : Fin nq × Fin nb) (task : Shared.Engine.Task n nb nq)
    (h : Charged c x before origin task) : Charged c x after origin task := by
  have hc := Finset.card_le_card (incidenceKeys_mono c hm origin)
  cases task with
  | active job => exact ⟨h.1, h.2.1, h.2.2.trans (Nat.mul_le_mul_left 2 hc)⟩
  | finished out => exact h.trans (Nat.mul_le_mul_left (4 * x) hc)

theorem evaluate_charged (c : Shared.Catalog n nb ns nq) (budget r x : ℕ)
    (origin : Fin nq × Fin nb) (job : Shared.Job n nb nq) (f : DistanceArray n)
    (old next : RecordGuard.Registry n nq) (task : Shared.Engine.Task n nb nq)
    (hreg : Registered c old.seen origin (.active job))
    (hcharge : Charged c x old.seen origin (.active job))
    (h : evaluate c budget r job f old = .ok (next, task)) : Charged c x next.seen origin task := by
  let U := found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r)
  unfold evaluate at h
  cases he : reserveFound c budget job.searchId U old with
  | error reason =>
      dsimp only [U] at he
      simp only [he] at h
      cases h
  | ok middle =>
      have he' : reserveFound c budget job.searchId
          (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources) f.get (c.scale * r))
          old = .ok middle := he
      simp only [he'] at h
      have hm := RecordGuard.reserveMany_mono c budget _ old middle he
      have hmiddle := charged_mono c x hm origin (.active job) hcharge
      by_cases hs : U.card < job.threshold
      · have hs' : (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources)
            f.get (c.scale * r)).card < job.threshold := hs
        rw [ite_eq_left hs'] at h
        cases h
        change job.spentReservations + (Shared.block c job.searchId job.blockId).card * job.threshold ≤ _
        have hmul := Nat.mul_le_mul hmiddle.1 hmiddle.2.2
        have hbalance := hmiddle.2.1
        nlinarith only [hmul, hbalance]
      · have hs' : ¬ (found (Shared.block c job.searchId job.blockId) (SparseLabels.support job.sources)
            f.get (c.scale * r)).card < job.threshold := hs
        rw [ite_eq_right hs'] at h
        cases h
        have hU : U ⊆ incidenceKeys c next.seen origin := by
          intro v hv
          have hk := RecordGuard.reserveMany_contains c budget _ old next he (job.searchId, v)
            (List.mem_map.mpr ⟨v, (Finset.mem_sort _).mpr hv, rfl⟩)
          have hb := Finset.inter_subset_left (Finset.mem_filter.mp hv).1
          obtain ⟨hj, hi⟩ := hreg.1
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj ▸ hk⟩, hi ▸ hb⟩
        have hcard := Finset.card_le_card hU
        have hbalance := hcharge.2.1
        refine ⟨hcharge.1, ?_, ?_⟩
        · change job.spentReservations + (Shared.block c job.searchId job.blockId).card * job.threshold +
              (Shared.block c job.searchId job.blockId).card =
            (Shared.block c job.searchId job.blockId).card * (2 * job.threshold)
          nlinarith only [hbalance]
        · change 2 * job.threshold ≤ _
          omega

theorem charged_work (c : Shared.Catalog n nb ns nq) (x : ℕ)
    (keys : Finset (RecordGuard.Key n nq)) (origin : Fin nq × Fin nb) (task : Shared.Engine.Task n nb nq)
    (h : Charged c x keys origin task) :
    Shared.Engine.taskWork task ≤ 4 * x * (incidenceKeys c keys origin).card := by
  cases task with
  | active job =>
      have hm := Nat.mul_le_mul h.1 h.2.2
      have hb := h.2.1
      change job.spentReservations ≤ _
      nlinarith only [hm, hb]
  | finished out => exact h

theorem charged_capacity (c : Shared.Catalog n nb ns nq) (x : ℕ)
    (keys : Finset (RecordGuard.Key n nq)) (origin : Fin nq × Fin nb) (task : Shared.Engine.Task n nb nq)
    (h : Charged c x keys origin task) :
    Shared.Engine.taskCapacity c task ≤ 2 * x * (incidenceKeys c keys origin).card := by
  cases task with
  | active job =>
      have hm := Nat.mul_le_mul h.1 h.2.2
      change (Shared.block c job.searchId job.blockId).card * job.threshold ≤ _
      nlinarith only [hm]
  | finished out => exact Nat.zero_le _

theorem incidence_sum (c : Shared.Catalog n nb ns nq) (keys : Finset (RecordGuard.Key n nq))
    (origin : Fin N → Fin nq × Fin nb) (hi : Function.Injective origin) :
    (∑ i : Fin N, (incidenceKeys c keys (origin i)).card) ≤ RecordGuard.weight c keys := by
  have h : (∑ i : Fin N, (incidenceKeys c keys (origin i)).card) ≤
      ∑ k : Fin nq × Fin nb, (incidenceKeys c keys k).card := by
    apply Finset.sum_le_sum_of_injOn origin
    · intro i _ j _ he
      exact hi he
    · exact Finset.subset_univ _
    · intro _ _; exact Nat.le_refl _
    · intro _ _ _; exact Nat.zero_le _
  apply h.trans
  rw [Fintype.sum_prod_type, RecordGuard.weight_sections]
  exact Finset.sum_le_sum (fun j _ => Nat.le_add_left _ _)

theorem workSum_budget (c : Shared.Catalog n nb ns nq) (x budget : ℕ)
    (registry : RecordGuard.Registry n nq) (hv : RecordGuard.Valid c budget registry)
    (origin : Fin N → Fin nq × Fin nb) (hi : Function.Injective origin)
    (tasks : Vector (Shared.Engine.Task n nb nq) N)
    (hc : ∀ i, Charged c x registry.seen (origin i) (tasks.get i)) :
    Shared.Engine.workSum tasks ≤ 4 * x * budget ∧
      Packing.load (fun slot => Shared.capacity c slot.2) (Shared.Engine.active tasks) ≤ 2 * x * budget := by
  have hinc := (incidence_sum c registry.seen origin hi).trans (hv.1 ▸ hv.2)
  constructor
  · unfold Shared.Engine.workSum
    calc
      _ ≤ ∑ i : Fin N, 4 * x * (incidenceKeys c registry.seen (origin i)).card :=
        Finset.sum_le_sum (fun i _ => charged_work c x registry.seen _ _ (hc i))
      _ = 4 * x * ∑ i : Fin N, (incidenceKeys c registry.seen (origin i)).card := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hinc
  · rw [Shared.Engine.active_load]
    calc
      _ ≤ ∑ i : Fin N, 2 * x * (incidenceKeys c registry.seen (origin i)).card :=
        Finset.sum_le_sum (fun i _ => charged_capacity c x registry.seen _ _ (hc i))
      _ = 2 * x * ∑ i : Fin N, (incidenceKeys c registry.seen (origin i)).card := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ hinc

end StreamingReachability.Core.GuardedEngine
