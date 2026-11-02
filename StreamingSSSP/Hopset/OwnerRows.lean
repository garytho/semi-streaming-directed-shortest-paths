module

public import StreamingSSSP.Hopset.OwnerGeometry
public import StreamingSSSP.Probability.Product

@[expose] public section

namespace StreamingSSSP.Hopset

open scoped Classical

noncomputable section

variable {n ns : ℕ}

abbrev ActiveOwners (P : Fin ns → Finset (Fin n)) :=
  Sigma fun i : Fin ns => {v : Fin n // v ∈ P i}

def activeOwnerIndex (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (hselected : ∀ i, selectedVertices targets i = members (P i)) : ActiveOwners P → Fin targets.length :=
  fun v => pivotIndex targets v.1 (P v.1) (hselected v.1) v.2

theorem activeOwnerIndex_injective (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (hselected : ∀ i, selectedVertices targets i = members (P i)) :
    Function.Injective (activeOwnerIndex targets P hselected) := by
  intro ⟨i, u⟩ ⟨j, v⟩ h
  have hu := pivotIndex_spec targets i (P i) (hselected i) u
  have hv := pivotIndex_spec targets j (P j) (hselected j) v
  have hij : i = j := by
    calc
      i = (targets.get (activeOwnerIndex targets P hselected ⟨i, u⟩)).setId := hu.2.1.symm
      _ = (targets.get (activeOwnerIndex targets P hselected ⟨j, v⟩)).setId := by rw [h]
      _ = j := hv.2.1
  subst j
  have huv : u = v := pivotIndex_injective targets i (P i) (hselected i) h
  subst v
  rfl

def flatOwnerIndex (P : Fin ns → Finset (Fin n)) : ActiveOwners P → Fin (ns * n) :=
  fun v => finProdFinEquiv (v.1, v.2.val)

theorem flatOwnerIndex_injective (P : Fin ns → Finset (Fin n)) :
    Function.Injective (flatOwnerIndex P) := by
  intro ⟨i, u⟩ ⟨j, v⟩ h
  have he := finProdFinEquiv.injective h
  have hij : i = j := congrArg Prod.fst he
  subst j
  have huv : u = v := Subtype.ext (congrArg Prod.snd he)
  subst v
  rfl

def extendOwners (cfg : Config) (P : Fin ns → Finset (Fin n))
    (xs : ActiveOwners P → Fin cfg.groups × Fin cfg.shifts) : Fin ns → Reference.Owners n cfg :=
  fun i v => if hv : v ∈ P i then xs ⟨i, ⟨v, hv⟩⟩
    else (⟨0, cfg.groups_pos⟩, ⟨0, cfg.shifts_pos⟩)

theorem expected_owner_rows (cfg : Config) (targets : List (Target n ns))
    (P : Fin ns → Finset (Fin n)) (hselected : ∀ i, selectedVertices targets i = members (P i))
    (f : (Fin ns → Reference.Owners n cfg) → ℝ)
    (hdepends : ∀ left right, (∀ i v, v ∈ P i → left i v = right i v) → f left = f right) :
    (Law.family targets.length (fun _ =>
        Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos)).expect
        (fun xs => f (fun i => ownersFromCoordinates cfg targets i (P i) (hselected i) xs)) =
      (Law.family ns (fun _ => Reference.ownerLaw n cfg)).expect f := by
  let mu := Law.uniformPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos
  have he := Law.family_reindex_finite targets.length (ns * n) mu
    (activeOwnerIndex targets P hselected) (flatOwnerIndex P)
    (activeOwnerIndex_injective targets P hselected) (flatOwnerIndex_injective P)
    (fun xs => f (extendOwners cfg P xs))
  change (Law.family targets.length (fun _ => mu)).expect
      (fun xs => f (fun i => ownersFromCoordinates cfg targets i (P i) (hselected i) xs)) =
    (Law.family (ns * n) (fun _ => mu)).expect
      (fun xs => f (extendOwners cfg P (fun v => xs (flatOwnerIndex P v)))) at he
  calc
    _ = (Law.family (ns * n) (fun _ => mu)).expect
        (fun xs => f (extendOwners cfg P (fun v => xs (flatOwnerIndex P v)))) := he
    _ = (Law.family (ns * n) (fun _ => mu)).expect
        (fun xs => f (Law.rowsFromFlat ns n xs)) := by
      apply congrArg (Law.family (ns * n) (fun _ => mu)).expect
      funext xs
      apply hdepends
      intro i v hv
      simp only [extendOwners, hv, ↓reduceDIte, flatOwnerIndex, Law.rowsFromFlat]
    _ = _ := (Law.family_rows ns n mu f).symm

theorem assignedPivots_congr_rows (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (P : Fin ns → Finset (Fin n))
    (hselected : ∀ i, selectedVertices targets i = members (P i))
    (left right : Fin ns → Reference.Owners n cfg)
    (h : ∀ i v, v ∈ P i → left i v = right i v) :
    pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets left) =
      pivotsFromOwners cfg r sets reply targets 0 (ownersForTargets cfg targets right) := by
  apply pivotsFromOwners_congr
  intro j hj
  exact h (targets.get j).setId (targets.get j).vertex
    (selected_vertex_mem targets (targets.get j).setId (P (targets.get j).setId)
      (hselected (targets.get j).setId) j hj rfl)

end

end StreamingSSSP.Hopset
