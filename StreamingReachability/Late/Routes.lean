module

public import StreamingReachability.Late.Split

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {V : Type*}

structure Route (F : Graph V) (s t : V) (budget : ℕ) where
  vertices : List V
  endpoints : Graph.Endpoints vertices s t
  cost_le : F.pathCost vertices ≤ (budget : Distance)

namespace Route

variable {F H : Graph V} {s t u : V} {a b : ℕ}

def hops (P : Route F s t a) : ℕ := P.vertices.length - 1

def nil (s : V) : Route F s s 0 :=
  ⟨[s], by simp [Graph.Endpoints], by simp⟩

def edge (s t : V) (a : ℕ) (h : F s t ≤ (a : Distance)) : Route F s t a :=
  ⟨[s, t], by simp [Graph.Endpoints], by simpa using h⟩

@[simp] theorem hops_nil (s : V) : (nil (F := F) s).hops = 0 := rfl

@[simp] theorem hops_edge (s t : V) (a : ℕ) (h : F s t ≤ (a : Distance)) :
    (edge s t a h).hops = 1 := rfl

def weaken (P : Route F s t a) (hab : a ≤ b) : Route F s t b :=
  ⟨P.vertices, P.endpoints, P.cost_le.trans (WithTop.coe_le_coe.mpr hab)⟩

@[simp] theorem hops_weaken (P : Route F s t a) (hab : a ≤ b) :
    (P.weaken hab).hops = P.hops := rfl

def mono (P : Route F s t a) (h : ∀ u v, H u v ≤ F u v) : Route H s t a :=
  ⟨P.vertices, P.endpoints, (Graph.pathCost_mono h P.vertices).trans P.cost_le⟩

@[simp] theorem hops_mono (P : Route F s t a) (h : ∀ u v, H u v ≤ F u v) :
    (P.mono h).hops = P.hops := rfl

def append (P : Route F s u a) (Q : Route F u t b) : Route F s t (a + b) where
  vertices := join P.vertices Q.vertices
  endpoints := join_endpoints P.endpoints Q.endpoints
  cost_le := by
    rw [join_cost F P.endpoints Q.endpoints]
    exact_mod_cast add_le_add P.cost_le Q.cost_le

theorem hops_append (P : Route F s u a) (Q : Route F u t b) :
    (P.append Q).hops ≤ P.hops + Q.hops := by
  have hl := join_length P.vertices Q.vertices (Graph.endpoints_nonempty Q.endpoints)
  have hp := List.length_pos_iff.mpr (Graph.endpoints_nonempty P.endpoints)
  have hq := List.length_pos_iff.mpr (Graph.endpoints_nonempty Q.endpoints)
  dsimp only [hops, append]
  omega

end Route

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t u : Fin n}

namespace Path

theorem original_cost (Q : Path R G s t) :
    (R.graph G).pathCost Q.vertices = (Q.micro : Distance) := by
  induction Q with
  | nil => simp [vertices, micro]
  | @cons s v t e Q ih =>
      obtain ⟨w, ws, hvs⟩ := List.exists_cons_of_ne_nil
        (Graph.endpoints_nonempty Q.endpoints)
      have hw : w = v := by simpa [hvs, Graph.Endpoints] using Q.endpoints.1
      subst w
      change (R.graph G).pathCost (s :: Q.vertices) = _
      rw [hvs, Graph.pathCost_cons_cons, e.weight]
      rw [hvs] at ih
      rw [ih]
      rfl

def originalRoute (Q : Path R G s t) (F : Graph (Fin n))
    (hF : ∀ u v, F u v ≤ R.graph G u v) : Route F s t Q.micro :=
  ⟨Q.vertices, Q.endpoints, (Graph.pathCost_mono hF _).trans_eq Q.original_cost⟩

end Path

def closureRoute (Q : Path R G s t) (F : Graph (Fin n)) (B : Finset (Fin n))
    (hB : Q.Inside B) (hF : ∀ u v, F u v ≤ closure (R.base G) B u v) :
    Route F s t Q.micro :=
  if h : s = t then by
    subst t
    exact (Route.nil s).weaken (Nat.zero_le _)
  else Route.edge s t Q.micro ((hF s t).trans (weighted_closure_edge Q B hB h))

theorem closureRoute_hops (Q : Path R G s t) (F : Graph (Fin n)) (B : Finset (Fin n))
    (hB : Q.Inside B) (hF : ∀ u v, F u v ≤ closure (R.base G) B u v) :
    (closureRoute Q F B hB hF).hops ≤ 1 := by
  unfold closureRoute
  split_ifs with h
  · subst t
    simp
  · exact le_rfl

def prefixRoute (Q : Path R G s t) (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : Q.Inside S) (p : Fin n) (rho D : ℝ)
    (hD : (Q.searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) t p rho)
    (F : Graph (Fin n))
    (hF : ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p rho D) u v) :
    Route F s t Q.micro :=
  closureRoute Q F _ (prefix_support_in_block Q A hA S hS p rho D hD hp) hF

theorem prefixRoute_hops (Q : Path R G s t) (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : Q.Inside S) (p : Fin n) (rho D : ℝ)
    (hD : (Q.searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) t p rho)
    (F : Graph (Fin n))
    (hF : ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p rho D) u v) :
    (prefixRoute Q A hA S hS p rho D hD hp F hF).hops ≤ 1 :=
  closureRoute_hops _ _ _ _ _

def suffixRoute (Q : Path R G s t) (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : Q.Inside S) (p : Fin n) (rho D : ℝ)
    (hD : (Q.searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) p s rho)
    (F : Graph (Fin n))
    (hF : ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p rho D) u v) :
    Route F s t Q.micro :=
  closureRoute Q F _ (suffix_support_in_block Q A hA S hS p rho D hD hp) hF

theorem suffixRoute_hops (Q : Path R G s t) (A : ℕ) (hA : 0 < A) (S : Finset (Fin n))
    (hS : Q.Inside S) (p : Fin n) (rho D : ℝ)
    (hD : (Q.searchWeight A : ℝ) ≤ D)
    (hp : Within (rounded A (R.restricted G S)) p s rho)
    (F : Graph (Fin n))
    (hF : ∀ u v, F u v ≤
      closure (R.base G) (block (rounded A (R.restricted G S)) S p rho D) u v) :
    (suffixRoute Q A hA S hS p rho D hD hp F hF).hops ≤ 1 :=
  closureRoute_hops _ _ _ _ _

namespace Route

def candidates (F : Graph (Fin n)) (s t : Fin n) (budget : ℕ) : Finset (List (Fin n)) :=
  (Graph.routes n).filter fun xs =>
    xs.Nodup ∧ Graph.Endpoints xs s t ∧ F.pathCost xs ≤ (budget : Distance)

theorem candidates_nonempty (F : Graph (Fin n)) {budget : ℕ}
    (P : Route F s t budget) : (candidates F s t budget).Nonempty := by
  obtain ⟨v, vs, hvs⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty P.endpoints)
  have hv : v = s := by simpa [hvs, Graph.Endpoints] using P.endpoints.1
  subst v
  obtain ⟨xs, hn, hh, ht, hsub, hc⟩ := F.exists_simple_path s vs
  refine ⟨xs, Finset.mem_filter.mpr ⟨?_, hn, ⟨hh, ?_⟩, ?_⟩⟩
  · apply (Graph.mem_routes _ _).mpr
    simpa using Graph.simple_length_le hn
  · have ht' : xs.getLast? = P.vertices.getLast? := by simpa only [← hvs] using ht
    exact ht'.trans P.endpoints.2
  · exact hc.trans (by simpa only [← hvs] using P.cost_le)

def best (F : Graph (Fin n)) {budget : ℕ} (P : Route F s t budget) : Route F s t budget :=
  let choice := Classical.choose
    (Finset.exists_min_image (candidates F s t budget) List.length (candidates_nonempty F P))
  let hc := Classical.choose_spec
    (Finset.exists_min_image (candidates F s t budget) List.length (candidates_nonempty F P))
  ⟨choice, (Finset.mem_filter.mp hc.1).2.2.1, (Finset.mem_filter.mp hc.1).2.2.2⟩

theorem best_nodup (F : Graph (Fin n)) {budget : ℕ} (P : Route F s t budget) :
    (best F P).vertices.Nodup := by
  exact (Finset.mem_filter.mp (Classical.choose_spec
    (Finset.exists_min_image (candidates F s t budget) List.length
      (candidates_nonempty F P))).1).2.1

theorem best_le (F : Graph (Fin n)) {budget : ℕ} (P Q : Route F s t budget) :
    (best F P).hops ≤ Q.hops := by
  obtain ⟨v, vs, hvs⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty Q.endpoints)
  have hv : v = s := by simpa [hvs, Graph.Endpoints] using Q.endpoints.1
  subst v
  obtain ⟨xs, hn, hh, ht, hsub, hc⟩ := F.exists_simple_path s vs
  have hx : xs ∈ candidates F s t budget := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hn, ⟨hh, ?_⟩, ?_⟩
    · apply (Graph.mem_routes _ _).mpr
      simpa using Graph.simple_length_le hn
    · have ht' : xs.getLast? = Q.vertices.getLast? := by simpa only [← hvs] using ht
      exact ht'.trans Q.endpoints.2
    · exact hc.trans (by simpa only [← hvs] using Q.cost_le)
  have hmin := (Classical.choose_spec
    (Finset.exists_min_image (candidates F s t budget) List.length
      (candidates_nonempty F P))).2 xs hx
  have hl := hsub.length_le
  rw [← hvs] at hl
  exact Nat.sub_le_sub_right (hmin.trans hl) 1

end Route

namespace Partition

variable {X : Finset (Fin n)} {A : ℕ} {d : ℝ} {F : Graph (Fin n)}

def assemble (hF : ∀ u v, F u v ≤ R.graph G u v)
    (child : (P : ChildPiece R G X A d) → Route F P.source P.target P.path.micro) :
    {s t : Fin n} → {Q : Path R G s t} → Partition R G X A d Q → Route F s t Q.micro
  | _, _, _, .one Q hX hd => child ⟨_, _, Q, hX, hd⟩
  | _, _, _, .cut P e Q hX hd rest => by
      have left := child ⟨_, _, P, hX, hd⟩
      have edge := Route.edge _ _ e.micro ((hF _ _).trans_eq e.weight)
      have tail := assemble hF child rest
      exact (left.append (edge.append tail)).weaken (by
        simp only [Path.micro_append, Path.micro]
        exact le_rfl)

theorem assemble_hops (hF : ∀ u v, F u v ≤ R.graph G u v)
    (child : (P : ChildPiece R G X A d) → Route F P.source P.target P.path.micro)
    {Q : Path R G s t} (P : Partition R G X A d Q) :
    (P.assemble hF child).hops ≤ P.boundaries +
      (P.pieces.map fun C => (child C).hops).sum := by
  induction P with
  | one Q hX hd => simp [assemble, boundaries, pieces]
  | cut Pre e Q hX hd rest ih =>
      have h := (child ⟨_, _, Pre, hX, hd⟩).hops_append
        ((Route.edge _ _ e.micro ((hF _ _).trans_eq e.weight)).append
          (rest.assemble hF child))
      have h' := (Route.edge _ _ e.micro ((hF _ _).trans_eq e.weight)).hops_append
        (rest.assemble hF child)
      simp only [Route.hops_edge] at h'
      simp only [assemble, Route.hops_weaken, boundaries, pieces, List.map_cons, List.sum_cons]
      omega

end Partition

end

end StreamingReachability.Late
