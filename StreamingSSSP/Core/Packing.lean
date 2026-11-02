module

public import Mathlib

@[expose] public section

namespace StreamingSSSP.Core.Packing

variable {J : Type*}

def load (capacity : J → ℕ) (jobs : List J) : ℕ := (jobs.map capacity).sum

def total (capacity : J → ℕ) (packs : List (List J)) : ℕ :=
  (packs.map (load capacity)).sum

def push (n : ℕ) (capacity : J → ℕ) (packs : List (List J)) (job : J) :
    List (List J) :=
  match packs with
  | [] => [[job]]
  | p :: ps =>
      if capacity job + load capacity p ≤ n then (job :: p) :: ps
      else [job] :: p :: ps

def pack (n : ℕ) (capacity : J → ℕ) (jobs : List J) : List (List J) :=
  jobs.foldl (push n capacity) []

theorem push_flatten (n : ℕ) (capacity : J → ℕ) (packs : List (List J)) (job : J) :
    (push n capacity packs job).flatten = job :: packs.flatten := by
  cases packs with
  | nil => rfl
  | cons p ps =>
      simp only [push]
      split_ifs <;> rfl

theorem pack_flatten (n : ℕ) (capacity : J → ℕ) (jobs : List J) :
    (pack n capacity jobs).flatten = jobs.reverse := by
  have h (xs : List J) (packs : List (List J)) :
      (xs.foldl (push n capacity) packs).flatten = xs.reverse ++ packs.flatten := by
    induction xs generalizing packs with
    | nil => simp
    | cons j js ih =>
        rw [List.foldl_cons, ih, push_flatten]
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
  simpa only [pack, List.flatten_nil, List.append_nil] using h jobs []

theorem total_eq_flatten (capacity : J → ℕ) (packs : List (List J)) :
    total capacity packs = load capacity packs.flatten := by
  simp only [total, load, List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def]
  rfl

theorem push_total (n : ℕ) (capacity : J → ℕ) (packs : List (List J)) (job : J) :
    total capacity (push n capacity packs job) = capacity job + total capacity packs := by
  rw [total_eq_flatten, push_flatten]
  change capacity job + load capacity packs.flatten = capacity job + total capacity packs
  rw [← total_eq_flatten]

theorem pack_total (n : ℕ) (capacity : J → ℕ) (jobs : List J) :
    total capacity (pack n capacity jobs) = load capacity jobs := by
  rw [total_eq_flatten, pack_flatten]
  simp [load]

theorem push_bounded (n : ℕ) (capacity : J → ℕ) (packs : List (List J)) (job : J)
    (hp : ∀ p ∈ packs, load capacity p ≤ n) (hj : capacity job ≤ n) :
    ∀ p ∈ push n capacity packs job, load capacity p ≤ n := by
  cases packs with
  | nil => simpa [push, load] using hj
  | cons p ps =>
      simp only [push]
      split_ifs with hfit
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hfit
        · exact hp q (List.mem_cons_of_mem _ hq)
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · simpa [load] using hj
        · exact hp q hq

theorem pack_bounded (n : ℕ) (capacity : J → ℕ) (jobs : List J)
    (hjobs : ∀ j ∈ jobs, capacity j ≤ n) :
    ∀ p ∈ pack n capacity jobs, load capacity p ≤ n := by
  have h (xs : List J) (packs : List (List J))
      (hp : ∀ p ∈ packs, load capacity p ≤ n)
      (hx : ∀ j ∈ xs, capacity j ≤ n) :
      ∀ p ∈ xs.foldl (push n capacity) packs, load capacity p ≤ n := by
    induction xs generalizing packs with
    | nil => exact hp
    | cons j js ih =>
        exact ih (push n capacity packs j)
          (push_bounded n capacity packs j hp (hx j (by simp)))
          (fun q hq => hx q (by simp [hq]))
  exact h jobs [] (by simp) hjobs

def potential (n : ℕ) (capacity : J → ℕ) (packs : List (List J)) : ℕ :=
  n * (packs.length - 1) + load capacity (packs.headD [])

theorem push_potential (n : ℕ) (capacity : J → ℕ) (packs : List (List J)) (job : J)
    (h : potential n capacity packs ≤ 2 * total capacity packs) :
    potential n capacity (push n capacity packs job) ≤
      2 * total capacity (push n capacity packs job) := by
  rw [push_total]
  cases packs with
  | nil =>
      simp only [potential, push, load, total, List.length_cons, List.length_nil,
        List.headD_cons, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.add_zero, Nat.sub_self, Nat.mul_zero,
        Nat.zero_add]
      omega
  | cons p ps =>
      simp only [potential, List.length_cons, Nat.add_sub_cancel, List.headD_cons] at h
      simp only [push]
      split_ifs with hfit
      · simpa only [potential, List.length_cons, Nat.add_sub_cancel, List.headD_cons,
          load, List.map_cons, List.sum_cons] using
          (show n * ps.length + (capacity job + load capacity p) ≤
            2 * (capacity job + total capacity (p :: ps)) by omega)
      · have hb : n ≤ capacity job + load capacity p := by omega
        simp only [potential, List.length_cons, Nat.add_sub_cancel, List.headD_cons,
          load, List.map_cons, List.sum_cons, List.map_nil, List.sum_nil, Nat.add_zero,
          Nat.mul_add, Nat.mul_one]
        omega

theorem pack_potential (n : ℕ) (capacity : J → ℕ) (jobs : List J) :
    potential n capacity (pack n capacity jobs) ≤ 2 * load capacity jobs := by
  have h (xs : List J) (packs : List (List J))
      (hp : potential n capacity packs ≤ 2 * total capacity packs) :
      potential n capacity (xs.foldl (push n capacity) packs) ≤
        2 * total capacity (xs.foldl (push n capacity) packs) := by
    induction xs generalizing packs with
    | nil => exact hp
    | cons j js ih => exact ih _ (push_potential n capacity packs j hp)
  simpa only [← pack_total n capacity jobs, pack] using
    h jobs [] (by simp [potential, load, total])

theorem pack_scan_bound (n : ℕ) (capacity : J → ℕ) (jobs : List J) :
    n * (pack n capacity jobs).length ≤ n + 2 * load capacity jobs := by
  have h := pack_potential n capacity jobs
  unfold potential at h
  rw [Nat.mul_sub_left_distrib] at h
  omega

theorem pack_scan_bound_div {n : ℕ} (hn : 0 < n) (capacity : J → ℕ) (jobs : List J) :
    (pack n capacity jobs).length ≤ 1 + 2 * load capacity jobs / n := by
  have h := pack_potential n capacity jobs
  have hm : ((pack n capacity jobs).length - 1) * n ≤ 2 * load capacity jobs := by
    simpa only [Nat.mul_comm] using (Nat.le_add_right _ _).trans h
  have hd := (Nat.le_div_iff_mul_le hn).mpr hm
  omega

end StreamingSSSP.Core.Packing
