module

public import StreamingSSSP.Core.RecordGuard

@[expose] public section

namespace StreamingSSSP.Core.RecordGuard

variable {n nb ns nq : ℕ}

theorem reserve_seen (c : Shared.Catalog n nb ns nq) (budget : ℕ) (key : Key n nq)
    (old next : Registry n nq) (h : reserve c budget key old = .ok next) :
    next.seen = insert key old.seen := by
  unfold reserve at h
  by_cases hk : key ∈ old.seen
  · rw [ite_eq_left hk] at h
    cases h
    exact (Finset.insert_eq_of_mem hk).symm
  · rw [ite_eq_right hk] at h
    split_ifs at h
    · cases h; rfl

theorem reserveMany_seen (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (keys : List (Key n nq)) (old next : Registry n nq)
    (h : reserveMany c budget keys old = .ok next) :
    next.seen = old.seen ∪ keys.toFinset := by
  induction keys generalizing old with
  | nil => cases h; simp
  | cons key keys ih =>
      rw [reserveMany] at h
      cases hr : reserve c budget key old with
      | error reason => simp [hr] at h
      | ok middle =>
          simp only [hr] at h
          rw [ih middle h, reserve_seen c budget key old middle hr]
          simp

theorem reserveMany_mono (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (keys : List (Key n nq)) (old next : Registry n nq)
    (h : reserveMany c budget keys old = .ok next) : old.seen ⊆ next.seen := by
  rw [reserveMany_seen c budget keys old next h]
  exact Finset.subset_union_left

theorem reserveMany_contains (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (keys : List (Key n nq)) (old next : Registry n nq)
    (h : reserveMany c budget keys old = .ok next) :
    ∀ key ∈ keys, key ∈ next.seen := by
  intro key hk
  rw [reserveMany_seen c budget keys old next h]
  exact Finset.mem_union_right _ (List.mem_toFinset.mpr hk)

theorem registry_cells (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (registry : Registry n nq) (h : Valid c budget registry) :
    2 + 3 * registry.seen.card ≤ 2 + 3 * budget := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 (registry_card c budget registry h)) 2

end StreamingSSSP.Core.RecordGuard
