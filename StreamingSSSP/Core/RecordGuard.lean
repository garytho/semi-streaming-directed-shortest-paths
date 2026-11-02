module

public import StreamingSSSP.Core.Descriptors
public import StreamingSSSP.Core.IndexedSums

@[expose] public section

namespace StreamingSSSP.Core.RecordGuard

variable {n nb ns nq : ℕ}

abbrev Key (n nq : ℕ) := Fin nq × Fin n

def vertexCharge (c : Shared.Catalog n nb ns nq) (v : Fin n) : ℕ :=
  1 + (List.finRange nb).foldl
    (fun count i => if v ∈ c.blocks.get i then count + 1 else count) 0

def charge (c : Shared.Catalog n nb ns nq) (key : Key n nq) : ℕ :=
  vertexCharge c key.2

theorem charge_eq (c : Shared.Catalog n nb ns nq) (key : Key n nq) :
    charge c key = 1 + ∑ i : Fin nb, if key.2 ∈ c.blocks.get i then 1 else 0 := by
  have h (indices : List (Fin nb)) (start : ℕ) :
      indices.foldl
        (fun count i => if key.2 ∈ c.blocks.get i then count + 1 else count) start =
      start + (indices.map fun i => if key.2 ∈ c.blocks.get i then 1 else 0).sum := by
    induction indices generalizing start with
    | nil => simp
    | cons i is ih =>
        by_cases hi : key.2 ∈ c.blocks.get i
        · simpa only [List.foldl_cons, hi, ↓reduceIte, List.map_cons, List.sum_cons,
            Nat.add_assoc] using ih (start + 1)
        · simpa only [List.foldl_cons, hi, ↓reduceIte, List.map_cons, List.sum_cons,
            Nat.zero_add] using ih start
  rw [charge, vertexCharge, h, Nat.zero_add]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

theorem charge_pos (c : Shared.Catalog n nb ns nq) (key : Key n nq) : 0 < charge c key := by
  unfold charge
  unfold vertexCharge
  omega

structure Registry (n nq : ℕ) where
  seen : Finset (Key n nq)
  used : ℕ

def empty : Registry n nq := ⟨∅, 0⟩

def weight (c : Shared.Catalog n nb ns nq) (keys : Finset (Key n nq)) : ℕ :=
  keys.sum (charge c)

def Valid (c : Shared.Catalog n nb ns nq) (budget : ℕ) (registry : Registry n nq) : Prop :=
  registry.used = weight c registry.seen ∧ registry.used ≤ budget

inductive Abort where
  | recordBudget
  deriving DecidableEq, Repr

def reserve (c : Shared.Catalog n nb ns nq) (budget : ℕ) (key : Key n nq)
    (old : Registry n nq) : Except Abort (Registry n nq) :=
  if key ∈ old.seen then .ok old
  else if old.used + charge c key ≤ budget
    then .ok ⟨insert key old.seen, old.used + charge c key⟩
    else .error .recordBudget

def reserveMany (c : Shared.Catalog n nb ns nq) (budget : ℕ) :
    List (Key n nq) → Registry n nq → Except Abort (Registry n nq)
  | [], old => .ok old
  | key :: keys, old =>
      match reserve c budget key old with
      | .error reason => .error reason
      | .ok next => reserveMany c budget keys next

theorem empty_valid (c : Shared.Catalog n nb ns nq) (budget : ℕ) : Valid c budget empty := by
  simp [Valid, empty, weight]

theorem reserve_valid (c : Shared.Catalog n nb ns nq) (budget : ℕ) (key : Key n nq)
    (old next : Registry n nq) (h : Valid c budget old)
    (hr : reserve c budget key old = .ok next) : Valid c budget next := by
  unfold reserve at hr
  by_cases hk : key ∈ old.seen
  · rw [ite_eq_left hk] at hr
    cases hr
    exact h
  · rw [ite_eq_right hk] at hr
    by_cases hb : old.used + charge c key ≤ budget
    · rw [ite_eq_left hb] at hr
      cases hr
      refine ⟨?_, hb⟩
      rw [weight, Finset.sum_insert hk, h.1]
      exact Nat.add_comm _ _
    · simp [hb] at hr

theorem reserveMany_valid (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (keys : List (Key n nq)) (old next : Registry n nq) (h : Valid c budget old)
    (hr : reserveMany c budget keys old = .ok next) : Valid c budget next := by
  induction keys generalizing old with
  | nil => cases hr; exact h
  | cons key keys ih =>
      rw [reserveMany] at hr
      cases hs : reserve c budget key old with
      | error reason => simp [hs] at hr
      | ok middle =>
          simp only [hs] at hr
          exact ih middle (reserve_valid c budget key old middle h hs) hr

theorem registry_card (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (old : Registry n nq) (h : Valid c budget old) : old.seen.card ≤ budget := by
  have hc : old.seen.card ≤ weight c old.seen := by
    have hh := Finset.sum_le_sum (s := old.seen)
      (fun key _ => Nat.succ_le_of_lt (charge_pos c key))
    simpa [weight] using hh
  exact hc.trans (h.1 ▸ h.2)

theorem reserve_bounded (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (allowed : Finset (Key n nq)) (hb : weight c allowed ≤ budget)
    (key : Key n nq) (hk : key ∈ allowed) (old : Registry n nq)
    (hs : old.seen ⊆ allowed) (he : old.used = weight c old.seen) :
    ∃ next, reserve c budget key old = .ok next ∧ next.seen ⊆ allowed := by
  by_cases hold : key ∈ old.seen
  · exact ⟨old, by simp [reserve, hold], hs⟩
  · have hsub : insert key old.seen ⊆ allowed := Finset.insert_subset hk hs
    have hcost : old.used + charge c key ≤ budget := by
      have hsum : weight c (insert key old.seen) ≤ weight c allowed :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      rw [weight, Finset.sum_insert hold] at hsum
      change charge c key + weight c old.seen ≤ weight c allowed at hsum
      rw [← he, Nat.add_comm] at hsum
      exact hsum.trans hb
    exact ⟨⟨insert key old.seen, old.used + charge c key⟩, by simp [reserve, hold, hcost], hsub⟩

theorem reserveMany_bounded (c : Shared.Catalog n nb ns nq) (budget : ℕ)
    (allowed : Finset (Key n nq)) (hb : weight c allowed ≤ budget)
    (keys : List (Key n nq)) (hk : ∀ key ∈ keys, key ∈ allowed)
    (old : Registry n nq) (hs : old.seen ⊆ allowed) (hv : Valid c budget old) :
    ∃ next, reserveMany c budget keys old = .ok next ∧
      next.seen ⊆ allowed ∧ Valid c budget next := by
  induction keys generalizing old with
  | nil => exact ⟨old, rfl, hs, hv⟩
  | cons key keys ih =>
      obtain ⟨middle, hm, hs'⟩ := reserve_bounded c budget allowed hb key (hk key (by simp)) old hs hv.1
      have hv' := reserve_valid c budget key old middle hv hm
      obtain ⟨next, hn, hs'', hv''⟩ := ih (fun q hq => hk q (by simp [hq])) middle hs' hv'
      exact ⟨next, by rw [reserveMany, hm]; exact hn, hs'', hv''⟩

end StreamingSSSP.Core.RecordGuard
