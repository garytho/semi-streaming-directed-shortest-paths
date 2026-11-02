module

public import StreamingSSSP.Hopset.Protocol

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

variable {n ns : ℕ}

theorem advance_target_mem (cfg : Config) (q : ℕ) (rank : Vector ℕ n)
    (sets : Vector (Finset (Fin n)) ns) (i : Fin ns) (p : Fin n)
    (hp : p ∈ sets.get i) (hfinite : rank.get p < cfg.earlyLevel) (hrank : rank.get p = q + cfg.advance) :
    (⟨i, p, .advanceStar⟩ : Target n ns) ∈ earlyTargets cfg q rank sets := by
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, List.mem_append_left _ ?_⟩
  apply List.mem_map.mpr
  refine ⟨p, List.mem_filter.mpr ⟨(mem_members _ _).mpr hp, ?_⟩, rfl⟩
  simpa only [advanceWanted, decide_eq_true_eq] using And.intro hfinite hrank

theorem global_target_mem (cfg : Config) (rank : Vector ℕ n) (p : Fin n)
    (hfinite : rank.get p < cfg.earlyLevel) (hrank : rank.get p < cfg.advance) :
    (⟨0, p, .globalStar⟩ : Target n 1) ∈ globalTargets cfg rank := by
  apply List.mem_map.mpr
  refine ⟨p, List.mem_filter.mpr ⟨List.mem_finRange p, ?_⟩, rfl⟩
  simpa only [globalWanted, decide_eq_true_eq] using And.intro hfinite hrank

theorem target_has_index (targets : List (Target n ns)) (target : Target n ns) (ht : target ∈ targets) :
    ∃ index : ℕ, targets[index]? = some target := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  refine ⟨i.val, ?_⟩
  rw [List.getElem?_eq_getElem i.isLt]
  exact congrArg some hi

end StreamingSSSP.Hopset
