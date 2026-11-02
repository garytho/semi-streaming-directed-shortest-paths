module

public import StreamingReachability.Late.Expectation

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical
open Early Implicit

noncomputable section

variable {n : ℕ} {R R' : Representation n} {G : Graph (Fin n)}
variable {s t u : Fin n}

theorem base_after_explicit_additions
    (h : ∀ e ∈ R.explicit, e ∈ R'.explicit) (u v : Fin n) :
    R'.base G u v ≤ R.base G u v :=
  min_le_min le_rfl (StoredEdges.graphOfEdges_antitone h u v)

theorem represented_prefix_after_commit (P : Path R G s u) (T : Path R G u t)
    (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : (P.append T).Inside S) (p : Fin n) (rho D : ℝ)
    (hD : ((P.append T).searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) t p rho)
    (hexplicit : ∀ e ∈ R.explicit, e ∈ R'.explicit)
    (hblock : block (rounded A (R.restricted G S)) S p rho D ∈ R'.blocks)
    (hsu : s ≠ u) : R'.graph G s u ≤ (P.micro : Distance) := by
  have h := closures_le_member (R'.base G) R'.blocks hblock s u
  exact h.trans ((closure_mono (base_after_explicit_additions hexplicit)
    (Finset.Subset.refl _) s u).trans
      (weighted_prefix_edge P T A hA S hS p rho D hD hp hsu))

theorem represented_suffix_after_commit (P : Path R G s u) (T : Path R G u t)
    (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : (P.append T).Inside S) (p : Fin n) (rho D : ℝ)
    (hD : ((P.append T).searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) p s rho)
    (hexplicit : ∀ e ∈ R.explicit, e ∈ R'.explicit)
    (hblock : block (rounded A (R.restricted G S)) S p rho D ∈ R'.blocks)
    (hut : u ≠ t) : R'.graph G u t ≤ (T.micro : Distance) := by
  have h := closures_le_member (R'.base G) R'.blocks hblock u t
  exact h.trans ((closure_mono (base_after_explicit_additions hexplicit)
    (Finset.Subset.refl _) u t).trans
      (weighted_suffix_edge P T A hA S hS p rho D hD hp hut))

namespace Config

def representation (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n)) : Representation n where
  explicit := R.explicit
  blocks := R.blocks ++ C.blocks R G S D run

theorem represented_graph (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n)) :
    (C.representation R G S D run).graph G = C.graph R G S D run := rfl

theorem graph_noncontracting (C : Config) (R : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n))
    (h : Noncontracting G (StoredEdges.graphOfEdges R.explicit)) :
    Noncontracting G (C.graph R G S D run) :=
  (C.representation R G S D run).noncontracting G h

theorem commit_le_graph (C : Config) (R R' : Representation n) (G : Graph (Fin n))
    (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n))
    (hexplicit : ∀ e ∈ R.explicit, e ∈ R'.explicit)
    (hblocks : ∀ B ∈ R.blocks ++ C.blocks R G S D run, B ∈ R'.blocks) :
    ∀ u v, R'.graph G u v ≤ C.graph R G S D run u v :=
  closures_mono _ _ (base_after_explicit_additions hexplicit) hblocks

def path_after_commit (C : Config) (R R' : Representation n) (G : Graph (Fin n))
    (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ) (run : List (C.Stage n))
    (hexplicit : ∀ e ∈ R.explicit, e ∈ R'.explicit)
    (hblocks : ∀ B ∈ R.blocks ++ C.blocks R G S D run, B ∈ R'.blocks) :
    Route (R'.graph G) s t Q.micro :=
  (C.path R G Q S D run).mono (C.commit_le_graph R R' G S D run hexplicit hblocks)

@[simp] theorem path_after_commit_hops (C : Config) (R R' : Representation n)
    (G : Graph (Fin n)) (Q : Path R G s t) (S : Finset (Fin n)) (D : ℝ)
    (run : List (C.Stage n)) (hexplicit : ∀ e ∈ R.explicit, e ∈ R'.explicit)
    (hblocks : ∀ B ∈ R.blocks ++ C.blocks R G S D run, B ∈ R'.blocks) :
    (C.path_after_commit R R' G Q S D run hexplicit hblocks).hops =
      (C.path R G Q S D run).hops := rfl

end Config

end

end StreamingReachability.Late
