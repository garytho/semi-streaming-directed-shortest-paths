module

public import StreamingReachability.Hopset.Protocol

@[expose] public section

namespace StreamingReachability.Hopset

variable {n ns : ℕ}

def decodeQuery (cfg : Config) (r : ℕ) (targets : List (Target n ns)) (index : ℕ) :
    Option (Core.BatchAPI.Query n ns) :=
  targets[index / 2]?.map fun target =>
    ⟨target.setId, target.vertex, decide (index % 2 = 1), targetRadius cfg r target.kind⟩

theorem queries_decode (cfg : Config) (r : ℕ) (targets : List (Target n ns)) (index : ℕ) :
    (queries cfg r targets)[index]? = decodeQuery cfg r targets index := by
  induction targets generalizing index with
  | nil => simp [queries, decodeQuery]
  | cons target targets ih =>
      cases index with
      | zero => simp [queries, decodeQuery]
      | succ index =>
          cases index with
          | zero => simp [queries, decodeQuery]
          | succ index =>
              have hd : (index + 2) / 2 = index / 2 + 1 := by omega
              have hm : (index + 2) % 2 = index % 2 := by omega
              simpa [queries, decodeQuery, Nat.succ_eq_add_one, Nat.add_assoc, hd, hm]
                using ih index

theorem catalog_search_get (cfg : Config) (r : ℕ) (blocks : List (Finset (Fin n)))
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (j : Fin (queries cfg r targets).length) :
    (queries cfg r targets)[j.val]? =
      some ((catalog cfg r blocks sets targets).searches.get j) := by
  simp [catalog, Vector.get_eq_getElem, j.isLt]

theorem catalog_decoded (cfg : Config) (r : ℕ) (blocks : List (Finset (Fin n)))
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (j : Fin (queries cfg r targets).length) :
    decodeQuery cfg r targets j.val =
      some ((catalog cfg r blocks sets targets).searches.get j) :=
  (queries_decode cfg r targets j.val).symm.trans
    (catalog_search_get cfg r blocks sets targets j)

theorem catalog_search_fields (cfg : Config) (r : ℕ) (blocks : List (Finset (Fin n)))
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (j : Fin (queries cfg r targets).length) (target : Target n ns)
    (ht : targets[j.val / 2]? = some target) :
    (catalog cfg r blocks sets targets).searches.get j =
      ⟨target.setId, target.vertex, decide (j.val % 2 = 1), targetRadius cfg r target.kind⟩ := by
  have h := catalog_decoded cfg r blocks sets targets j
  simp only [decodeQuery, ht, Option.map_some, Option.some.injEq] at h
  exact h.symm

theorem catalog_block_mem (cfg : Config) (r : ℕ) (blocks : List (Finset (Fin n)))
    (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns))
    (i : Fin blocks.length) :
    (catalog cfg r blocks sets targets).blocks.get i ∈ blocks := by
  have h := List.get_mem (catalog cfg r blocks sets targets).blocks.toList
    ⟨i.val, by simpa using i.isLt⟩
  simp only [List.get_eq_getElem, Vector.getElem_toList, ← Vector.get_eq_getElem] at h
  simpa only [catalog, Array.toVector, Vector.toList_mk, List.toList_toArray] using h

theorem queries_radius (cfg : Config) (r : ℕ) (targets : List (Target n ns))
    (hsearch : cfg.searchRadius r ≤ cfg.globalRadius) :
    ∀ q ∈ queries cfg r targets, q.radius ≤ cfg.globalRadius := by
  intro q hq
  obtain ⟨target, _, hq⟩ := List.mem_flatMap.mp hq
  rcases List.mem_cons.mp hq with h | hq
  · subst q
    cases target.kind <;> simp only [targetRadius] <;> first | exact le_rfl | exact hsearch
  · have h := List.mem_singleton.mp hq
    subst q
    cases target.kind <;> simp only [targetRadius] <;> first | exact le_rfl | exact hsearch

theorem request_radius (cfg : Config) (r : ℕ) (stored : List (StoredEdges.Edge n))
    (blocks : List (Finset (Fin n))) (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (workspace : ℕ) (hsearch : cfg.searchRadius r ≤ cfg.globalRadius) :
    (Core.BatchAPI.Request.ofCatalog stored (catalog cfg r blocks sets targets) workspace).radius ≤
      cfg.globalRadius := by
  have hmax (xs : List ℕ) (h : ∀ a ∈ xs, a ≤ cfg.globalRadius) :
      xs.foldr Nat.max 0 ≤ cfg.globalRadius := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
        exact max_le (h a (by simp)) (ih (by intro b hb; exact h b (by simp [hb])))
  simp only [Core.BatchAPI.Request.radius, Core.BatchAPI.Request.ofCatalog, catalog,
    Array.toVector, Vector.toList_mk, List.toList_toArray]
  apply hmax
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  exact queries_radius cfg r targets hsearch q hq

end StreamingReachability.Hopset
