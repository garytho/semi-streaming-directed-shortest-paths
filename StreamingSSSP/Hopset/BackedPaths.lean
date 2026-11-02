module

public import StreamingSSSP.Hopset.RelativeTrial

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical

noncomputable section

variable {n : ℕ} {stored : Implicit.Representation n} {G : Graph (Fin n)} {s t : Fin n}

theorem exists_backed_path (xs : List (Fin n)) (hnd : xs.Nodup) (he : Graph.Endpoints xs s t)
    (hf : (stored.graph G).pathCost xs ≠ ⊤) :
    ∃ P : Path stored G s t, P.vertices = xs := by
  induction xs generalizing s with
  | nil => exact False.elim (Graph.endpoints_nonempty he rfl)
  | cons u xs ih =>
      have hu : u = s := by simpa only [List.head?_cons, Option.some.injEq] using he.1
      subst s
      cases xs with
      | nil =>
          have ht : u = t := by simpa only [List.getLast?_singleton, Option.some.injEq] using he.2
          subst t
          exact ⟨.nil u, rfl⟩
      | cons v xs =>
          have htail : (v :: xs).Nodup := (List.nodup_cons.mp hnd).2
          have hne : u ≠ v := by
            intro huv
            exact (List.nodup_cons.mp hnd).1 (List.mem_cons.mpr (Or.inl huv))
          have htailEnds : Graph.Endpoints (v :: xs) v t :=
            ⟨rfl, by simpa only [List.getLast?_cons_cons] using he.2⟩
          have htailFinite : (stored.graph G).pathCost (v :: xs) ≠ ⊤ := by
            intro htop
            have h := Graph.pathCost_tail_le (stored.graph G) u (v :: xs)
            rw [htop] at h
            exact hf (top_le_iff.mp h)
          have hedgeFinite : stored.graph G u v ≠ ⊤ := by
            intro htop
            apply hf
            simp only [Graph.pathCost_cons_cons, htop, top_add]
          obtain ⟨tail, hvertices⟩ := ih (s := v) htail htailEnds htailFinite
          let origin := Classical.choice (Origin.exists_origin hedgeFinite)
          lift stored.graph G u v to ℕ using hedgeFinite with w hw
          let edge : Edge stored G u v := ⟨w, hw.symm, hne, origin⟩
          exact ⟨.cons edge tail, congrArg (List.cons u) hvertices⟩

theorem exists_backed_hopPath (hops : ℕ) (s t : Fin n)
    (hf : (stored.graph G).hopDist hops s t ≠ ⊤) :
    ∃ P : Path stored G s t, P.vertices.Nodup ∧ P.length ≤ hops ∧
      (P.micro : Distance) = (stored.graph G).hopDist hops s t := by
  obtain ⟨xs, hnd, he, hl, hc⟩ := (stored.graph G).exists_hopDist_path hf
  have hfinite : (stored.graph G).pathCost xs ≠ ⊤ := by rwa [hc]
  obtain ⟨P, hp⟩ := exists_backed_path xs hnd he hfinite
  refine ⟨P, by rw [hp]; exact hnd, ?_, ?_⟩
  · have hlen := P.length_vertices
    rw [hp] at hlen
    omega
  · rw [← P.original_cost, hp, hc]

end

end StreamingSSSP.Late
