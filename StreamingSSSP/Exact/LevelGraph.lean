module

public import StreamingSSSP.Exact.Envelope
public import StreamingSSSP.Exact.Bins

@[expose] public section

namespace StreamingSSSP.Exact

variable {V : Type*}

def mapWeights (G : Graph V) (f : ℕ → ℕ) : Graph V :=
  fun u v => WithTop.map f (G u v)

@[simp] theorem mapWeights_coe (G : Graph V) (f : ℕ → ℕ)
    {u v : V} {w : ℕ} (h : G u v = w) :
    mapWeights G f u v = (f w : Distance) := by
  simp [mapWeights, h]

@[simp] theorem mapWeights_top (G : Graph V) (f : ℕ → ℕ)
    {u v : V} (h : G u v = ⊤) :
    mapWeights G f u v = ⊤ := by
  simp [mapWeights, h]

/-- Every streamed edge is either deleted or multiplied by the current slope.
The only new edges are the one-per-vertex edges leaving `none`. -/
def levelGraph (G : Graph V) (labels : V → ℕ)
    (slope width shift : ℕ) : Graph (Option V)
  | none, some v => residue width shift (labels v)
  | some u, some v =>
      if binIndex width shift (labels u) = binIndex width shift (labels v)
      then mapWeights G (slope * ·) u v else ⊤
  | _, none => ⊤

theorem levelGraph_local (G : Graph V) (labels : V → ℕ)
    (slope width shift : ℕ) (u v : V) :
    levelGraph G labels slope width shift (some u) (some v) =
      if (labels u + shift) / width = (labels v + shift) / width
      then WithTop.map (slope * ·) (G u v) else ⊤ := rfl

theorem level_pathCost (G : Graph V) (labels : V → ℕ)
    (slope width shift k : ℕ) (xs : List V) (c : ℕ)
    (hc : G.pathCost xs = c)
    (hb : ∀ x ∈ xs, binIndex width shift (labels x) = k) :
    (levelGraph G labels slope width shift).pathCost (xs.map some) =
      ((slope * c : ℕ) : Distance) := by
  induction xs generalizing c with
  | nil =>
      have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
      simp [hc0]
  | cons u xs ih =>
      cases xs with
      | nil =>
          have hc0 : c = 0 := WithTop.coe_eq_coe.mp hc.symm
          simp [hc0]
      | cons v xs =>
          obtain ⟨a, b, ha, hbc, hab⟩ := finite_add hc
          have hbin : binIndex width shift (labels u) =
              binIndex width shift (labels v) := (hb u (by simp)).trans (hb v (by simp)).symm
          have ht := ih b hbc (by
            intro x hx
            exact hb x (by simp [hx]))
          simp only [List.map_cons] at ht
          simp only [List.map_cons, Graph.pathCost_cons_cons]
          rw [show levelGraph G labels slope width shift (some u) (some v) =
            ((slope * a : ℕ) : Distance) by simp [levelGraph, hbin, ha], ht]
          calc
            ((slope * a : ℕ) : Distance) + ((slope * b : ℕ) : Distance) =
                ((slope * a + slope * b : ℕ) : Distance) := (Nat.cast_add _ _).symm
            _ = ((slope * c : ℕ) : Distance) := by rw [← Nat.mul_add, hab]

theorem level_path_upper [Fintype V] (G : Graph V) (labels : V → ℕ)
    (slope width shift k : ℕ) {u v : V} (p : Route G u v)
    (hb : ∀ x ∈ p.vertices, binIndex width shift (labels x) = k) :
    (levelGraph G labels slope width shift).dist none (some v) ≤
      ((residue width shift (labels u) + slope * p.cost : ℕ) : Distance) := by
  obtain ⟨a, tail, hlist⟩ :=
    List.exists_cons_of_ne_nil (Graph.endpoints_nonempty p.endpoints)
  have hau : a = u := by simpa [Graph.Endpoints, hlist] using p.endpoints.1
  subst a
  have hcost := level_pathCost G labels slope width shift k p.vertices p.cost p.cost_eq hb
  have he : Graph.Endpoints (none :: p.vertices.map some) none (some v) := by
    constructor
    · rfl
    · simpa [Graph.Endpoints, hlist] using
        (Graph.endpoints_map (some : V → Option V) p.endpoints).2
  have hp := (levelGraph G labels slope width shift).dist_le_pathCost he
  have ht : (levelGraph G labels slope width shift).pathCost
      (none :: p.vertices.map some) =
        ((residue width shift (labels u) + slope * p.cost : ℕ) : Distance) := by
    rw [hlist, List.map_cons, Graph.pathCost_cons_cons]
    rw [← List.map_cons, ← hlist, hcost]
    exact (Nat.cast_add _ _).symm
  exact ht ▸ hp

theorem level_dist_finite [Fintype V] (G : Graph V) (labels : V → ℕ)
    (slope width shift : ℕ) (v : V) :
    ∃ d : ℕ, (levelGraph G labels slope width shift).dist none (some v) = d := by
  obtain ⟨d, hd, _⟩ := finite_of_le
    ((levelGraph G labels slope width shift).dist_le_edge none (some v))
  exact ⟨d, hd⟩

theorem envelope_le_level [Fintype V] (G : Graph V) (labels : V → ℕ)
    (slope width shift : ℕ) {v : V} {d : ℕ}
    (hd : (levelGraph G labels slope width shift).dist none (some v) = d) :
    (envelope G labels slope v : ℤ) ≤ binBase width shift (labels v) + d := by
  let f : Option V → ℤ
    | none => 0
    | some u => (envelope G labels slope u : ℤ) - binBase width shift (labels u)
  have he : ∀ a b (w : ℕ),
      levelGraph G labels slope width shift a b = (w : Distance) →
        f b ≤ f a + w := by
    intro a b w hw
    cases b with
    | none => simp [levelGraph] at hw
    | some v =>
        cases a with
        | none =>
            have hw' : residue width shift (labels v) = w :=
              WithTop.coe_eq_coe.mp hw
            have hl := envelope_le_label G labels slope v
            have hh := bin_decomposition width shift (labels v)
            dsimp [f]
            omega
        | some u =>
            by_cases hb : binIndex width shift (labels u) =
                binIndex width shift (labels v)
            · have hnot : G u v ≠ ⊤ := by
                intro hn
                simp [levelGraph, hb, hn] at hw
              lift G u v to ℕ using hnot with z hz
              have hw' : slope * z = w := by
                apply WithTop.coe_eq_coe.mp
                simpa [levelGraph, hb, ← hz] using hw
              have hbase := binBase_eq hb
              have henv := envelope_edge G labels slope hz.symm
              have henv' : (envelope G labels slope v : ℤ) ≤
                  envelope G labels slope u + (slope : ℤ) * z := by
                exact_mod_cast henv
              dsimp [f]
              have hwz : (slope : ℤ) * z = w := by exact_mod_cast hw'
              omega
            · simp [levelGraph, hb] at hw
  let p := shortestRoute (levelGraph G labels slope width shift) hd
  have ht := potential_le_path f he p.endpoints p.cost_eq
  change (envelope G labels slope v : ℤ) -
    binBase width shift (labels v) ≤ (0 : ℤ) + d at ht
  omega

end StreamingSSSP.Exact
