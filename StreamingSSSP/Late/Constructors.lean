module

public import StreamingSSSP.Late.Routes

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical
open Implicit

noncomputable section

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t u v : Fin n}

def Edge.ofFinite (R : Representation n) (G : Graph (Fin n)) (u v : Fin n)
    (hne : u ≠ v) (hf : R.graph G u v ≠ ⊤) : Edge R G u v where
  micro := (R.graph G u v).untop hf
  weight := (WithTop.coe_untop _ hf).symm
  distinct := hne
  origin := Classical.choice (Origin.exists_origin hf)

/-- Every fixed genuine simple finite comparison path obtains its origins
from attained implicit closure paths before any owner or pivot is sampled. -/
theorem exists_backed_path {xs : List (Fin n)}
    (he : Graph.Endpoints xs s t) (hn : xs.Nodup)
    (hf : (R.graph G).pathCost xs ≠ ⊤) :
    ∃ Q : Path R G s t, Q.vertices = xs := by
  induction xs generalizing s with
  | nil => simp [Graph.Endpoints] at he
  | cons u xs ih =>
      have hu : u = s := by simpa [Graph.Endpoints] using he.1
      subst s
      cases xs with
      | nil =>
          have ht : u = t := by simpa [Graph.Endpoints] using he.2
          subst t
          exact ⟨.nil u, rfl⟩
      | cons v xs =>
          have htail : Graph.Endpoints (v :: xs) v t := ⟨rfl, by simpa using he.2⟩
          have htailfinite : (R.graph G).pathCost (v :: xs) ≠ ⊤ := by
            intro ht
            apply hf
            apply top_le_iff.mp
            rw [← ht]
            exact (R.graph G).pathCost_tail_le u (v :: xs)
          have hedgefinite : R.graph G u v ≠ ⊤ := by
            intro ht
            simp [Graph.pathCost_cons_cons, ht] at hf
          have hne : u ≠ v :=
            fun h => (List.nodup_cons.mp hn).1 (by simp [h])
          obtain ⟨Q, hQ⟩ := ih htail (List.nodup_cons.mp hn).2 htailfinite
          exact ⟨.cons (Edge.ofFinite R G u v hne hedgefinite) Q, by
            simpa only [Path.vertices] using congrArg (u :: ·) hQ⟩

theorem backed_path_cost {xs : List (Fin n)}
    (he : Graph.Endpoints xs s t) (hn : xs.Nodup)
    (hf : (R.graph G).pathCost xs ≠ ⊤) :
    ∃ Q : Path R G s t, Q.vertices = xs ∧
      (Q.micro : Distance) = (R.graph G).pathCost xs ∧ Q.Inside Finset.univ := by
  obtain ⟨Q, hQ⟩ := exists_backed_path he hn hf
  exact ⟨Q, hQ, by rw [← hQ, Q.original_cost], fun _ _ => Finset.mem_univ _⟩

theorem exists_backed_shortest (R : Representation n) (G : Graph (Fin n))
    (hf : (R.graph G).dist s t ≠ ⊤) :
    ∃ Q : Path R G s t, Q.vertices.Nodup ∧
      (Q.micro : Distance) = (R.graph G).dist s t ∧ Q.Inside Finset.univ := by
  obtain ⟨xs, hn, he, _, hc⟩ := (R.graph G).exists_dist_path hf
  obtain ⟨Q, hQ, hcost, hinside⟩ := backed_path_cost he hn (by rwa [hc])
  exact ⟨Q, by rwa [hQ], hcost.trans hc, hinside⟩

end

end StreamingSSSP.Late
