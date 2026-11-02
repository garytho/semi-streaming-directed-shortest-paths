module

public import StreamingReachability.Core.Packing
public import StreamingReachability.Core.RegisteredUpdates

@[expose] public section

namespace StreamingReachability.Core.Packing

variable {J : Type*}

theorem pack_nonempty (n : ℕ) (capacity : J → ℕ) (jobs : List J) :
    ∀ p ∈ pack n capacity jobs, p ≠ [] := by
  have h (xs : List J) (packs : List (List J)) (hp : ∀ p ∈ packs, p ≠ []) :
      ∀ p ∈ xs.foldl (push n capacity) packs, p ≠ [] := by
    induction xs generalizing packs with
    | nil => exact hp
    | cons j js ih =>
        apply ih
        cases packs with
        | nil => simp [push]
        | cons p ps =>
            simp only [push]
            split_ifs
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact List.cons_ne_nil _ _
              · exact hp q (by simp [hq])
            · intro q hq
              rcases List.mem_cons.mp hq with rfl | hq
              · exact List.cons_ne_nil _ _
              · exact hp q hq
  exact h jobs [] (by simp)

theorem pack_length (n : ℕ) (capacity : J → ℕ) (jobs : List J) :
    (pack n capacity jobs).length ≤ jobs.length := by
  have h (packs : List (List J)) (hp : ∀ p ∈ packs, p ≠ []) :
      packs.length ≤ packs.flatten.length := by
    induction packs with
    | nil => simp
    | cons p ps ih =>
        have hpos : 0 < p.length := by cases p <;> simp_all
        have ht := ih (fun q hq => hp q (by simp [hq]))
        simp only [List.flatten_cons, List.length_cons, List.length_append]
        omega
  simpa only [pack_flatten, List.length_reverse] using h (pack n capacity jobs) (pack_nonempty n capacity jobs)

end StreamingReachability.Core.Packing

namespace StreamingReachability.Core.GuardedEngine

variable {n nb ns nq N : ℕ}

def planCells (c : Shared.Catalog n nb ns nq) (tasks : Vector (Shared.Engine.Task n nb nq) N) : ℕ :=
  let active := Shared.Engine.active tasks
  let packs := Packing.pack n (fun slot => Shared.capacity c slot.2) active
  4 * active.length + 2 * packs.length + 4 * packs.flatten.length

theorem planCells_bound (c : Shared.Catalog n nb ns nq) (tasks : Vector (Shared.Engine.Task n nb nq) N) :
    planCells c tasks ≤ 10 * N := by
  have ha : (Shared.Engine.active tasks).length ≤ N := by
    simpa only [Shared.Engine.active, List.length_finRange] using List.length_filterMap_le _ (List.finRange N)
  have hp := Packing.pack_length n (fun slot : Fin N × Shared.Job n nb nq => Shared.capacity c slot.2)
    (Shared.Engine.active tasks)
  simp only [planCells, Packing.pack_flatten, List.length_reverse]
  omega

end StreamingReachability.Core.GuardedEngine
