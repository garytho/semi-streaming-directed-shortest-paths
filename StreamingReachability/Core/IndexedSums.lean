module

public import StreamingReachability.Core.RecordMap

@[expose] public section

namespace StreamingReachability.Core

theorem list_sum_get {S : Type*} (xs : List S) (f : S → ℕ) :
    (xs.map f).sum = ∑ i : Fin xs.length, f (xs.get i) := by
  have hmap : xs.map f = List.ofFn (fun i : Fin xs.length => f (xs.get i)) := by
    calc
      xs.map f = List.map f (List.ofFn xs.get) :=
        congrArg (List.map f) (List.ofFn_get xs).symm
      _ = _ := List.map_ofFn
  rw [hmap]
  exact List.sum_ofFn

namespace RecordMap

variable {K S : Type*} [DecidableEq K]

theorem index_key_injective (xs : Map K S) (hu : Unique xs) :
    Function.Injective (fun i : Fin xs.length => (xs.get i).1) := by
  intro i j he
  let i' : Fin (xs.map Prod.fst).length := ⟨i.val, by simpa using i.isLt⟩
  let j' : Fin (xs.map Prod.fst).length := ⟨j.val, by simpa using j.isLt⟩
  have hi : (xs.map Prod.fst).get i' = (xs.get i).1 := by
    simp [i', List.get_eq_getElem]
  have hj : (xs.map Prod.fst).get j' = (xs.get j).1 := by
    simp [j', List.get_eq_getElem]
  have hk : i' = j' := hu.get_inj_iff.mp (hi.trans (he.trans hj.symm))
  exact Fin.ext (congrArg (fun t : Fin (xs.map Prod.fst).length => t.val) hk)

theorem sum_values_le [Fintype K] (zero : S) (xs : Map K S) (hu : Unique xs) (weight : S → ℕ) :
    (xs.map fun pair => weight pair.2).sum ≤
      ∑ k : K, weight (get zero xs k) := by
  rw [list_sum_get]
  apply Finset.sum_le_sum_of_injOn (fun i : Fin xs.length => (xs.get i).1)
  · intro i _ j _ he
    exact index_key_injective xs hu he
  · exact Finset.subset_univ _
  · intro i _
    have hmem : ((xs.get i).1, (xs.get i).2) ∈ xs := List.get_mem xs i
    rw [get_mem zero xs hu hmem]
  · intro _ _ _
    exact Nat.zero_le _

end RecordMap

end StreamingReachability.Core
