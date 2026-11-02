module

public import Mathlib

@[expose] public section

namespace StreamingSSSP.Core.VectorStore

variable {S : Type*} {N : ℕ}

def set (xs : Vector S N) (i : Fin N) (value : S) : Vector S N :=
  xs.set i.val value i.isLt

theorem get_set (xs : Vector S N) (i j : Fin N) (value : S) :
    (set xs i value).get j = if j = i then value else xs.get j := by
  change (xs.set i.val value i.isLt)[j.val] = if j = i then value else xs[j.val]
  rw [Vector.getElem_set]
  by_cases h : j = i
  · subst j; simp
  · have hn : i.val ≠ j.val := fun he => h (Fin.ext he.symm)
    simp [h, hn]

theorem set_get (xs : Vector S N) (i : Fin N) : set xs i (xs.get i) = xs := by
  apply Vector.ext
  intro j hj
  change (set _ _ _).get ⟨j, hj⟩ = xs.get ⟨j, hj⟩
  rw [get_set]
  split_ifs with h
  · rw [h]
  · rfl

def applyEach (f : Fin N → S → S) (indices : List (Fin N)) (xs : Vector S N) : Vector S N :=
  indices.foldl (fun ys i => set ys i (f i (ys.get i))) xs

theorem get_applyEach (f : Fin N → S → S) (indices : List (Fin N)) (hu : indices.Nodup)
    (xs : Vector S N) (j : Fin N) :
    (applyEach f indices xs).get j =
      if j ∈ indices then f j (xs.get j) else xs.get j := by
  induction indices generalizing xs with
  | nil => simp [applyEach]
  | cons i is ih =>
      obtain ⟨hi, ht⟩ := List.nodup_cons.mp hu
      rw [applyEach, List.foldl_cons]
      change (applyEach f is (set xs i (f i (xs.get i)))).get j = _
      rw [ih ht, get_set]
      by_cases hj : j = i
      · subst j; simp [hi]
      · simp [hj, Ne.symm hj]

theorem applyEach_all (f : Fin N → S → S) (xs : Vector S N) :
    applyEach f (List.finRange N) xs = Vector.ofFn (fun j => f j (xs.get j)) := by
  apply Vector.ext
  intro j hj
  change (applyEach _ _ _).get ⟨j, hj⟩ = (Vector.ofFn _).get ⟨j, hj⟩
  rw [get_applyEach _ _ (List.nodup_finRange N), Vector.get_ofFn]
  simp

end StreamingSSSP.Core.VectorStore
