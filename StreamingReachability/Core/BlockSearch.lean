module

public import StreamingReachability.Core.Skeleton

@[expose] public section

namespace StreamingReachability.Core

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def OutgoingWitness (B known : Finset V) (G F : Graph V) (τ : ℕ) : Prop :=
  ∀ a b, b ∉ known → F a b ≤ G a b ∨
    ∃ Z : Finset V, Z ⊆ B \ known ∧ Z.card = τ ∧ ∀ z ∈ Z, F a z ≤ G a b

omit [Fintype V] in
theorem walk_witness (B known : Finset V) (G F : Graph V)
    (d f : V → Distance) (τ : ℕ)
    (hd : ∀ a b, d b ≤ d a + G a b)
    (hf : ∀ a b, f b ≤ f a + F a b)
    (hknown : ∀ a ∈ known, f a ≤ d a)
    (hout : OutgoingWitness B known G F τ)
    {u v : V} {xs : List V} (he : Graph.Endpoints xs u v) (start : Distance)
    (hdu : d u ≤ start) (hfu : f u ≤ start) :
    f v ≤ start + G.pathCost xs ∨
      ∃ Z : Finset V, Z ⊆ B \ known ∧ Z.card = τ ∧
        ∀ z ∈ Z, f z ≤ start + G.pathCost xs := by
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil (Graph.endpoints_nonempty he)
  have hau : a = u := by simpa [Graph.Endpoints] using he.1
  subst a
  induction tail generalizing u start with
  | nil =>
      have huv : u = v := by simpa [Graph.Endpoints] using he.2
      exact Or.inl (by simpa [huv] using hfu)
  | cons b tail ih =>
      have he' : Graph.Endpoints (b :: tail) b v :=
        ⟨rfl, by simpa [Graph.Endpoints] using he.2⟩
      have hdb : d b ≤ start + G u b :=
        (hd u b).trans (add_le_add hdu le_rfl)
      have hstep : f b ≤ start + G u b ∨
          ∃ Z : Finset V, Z ⊆ B \ known ∧ Z.card = τ ∧
            ∀ z ∈ Z, f z ≤ start + G u b := by
        by_cases hbk : b ∈ known
        · exact Or.inl ((hknown b hbk).trans hdb)
        rcases hout u b hbk with hkeep | ⟨Z, hZ, hc, hz⟩
        · exact Or.inl ((hf u b).trans (add_le_add hfu hkeep))
        · exact Or.inr ⟨Z, hZ, hc, fun z hzm =>
            (hf u z).trans (add_le_add hfu (hz z hzm))⟩
      rcases hstep with hfb | ⟨Z, hZ, hc, hz⟩
      · rcases ih (start + G u b) hdb hfb he' with hv | ⟨Z, hZ, hc, hz⟩
        · exact Or.inl (by simpa only [Graph.pathCost_cons_cons, add_assoc] using hv)
        · exact Or.inr ⟨Z, hZ, hc, fun z hzm => by
            simpa only [Graph.pathCost_cons_cons, add_assoc] using hz z hzm⟩
      · refine Or.inr ⟨Z, hZ, hc, fun z hzm => (hz z hzm).trans ?_⟩
        rw [Graph.pathCost_cons_cons, ← add_assoc]
        exact le_add_of_nonneg_right bot_le

theorem multisource_gap (B known : Finset V) (G F : Graph V)
    (seed initial : V → Distance) (τ : ℕ)
    (hseed : ∀ u, u ∉ known → seed u = ⊤)
    (hinit : ∀ u ∈ known, initial u = multiDist G seed u)
    (hout : OutgoingWitness B known G F τ) :
    GapWitness B known (multiDist G seed) (multiDist F initial) τ := by
  intro v _ _ hgap
  obtain ⟨u, hu⟩ := multiDist_attained G seed v
  have hdtop : multiDist G seed v ≠ ⊤ := ne_top_of_lt hgap
  have hutop : seed u ≠ ⊤ := by
    intro h
    exact hdtop (by simp [hu, h])
  have huk : u ∈ known := by
    by_contra h
    exact hutop (hseed u h)
  have hdist : G.dist u v ≠ ⊤ := by
    intro h
    exact hdtop (by simp [hu, h])
  obtain ⟨xs, _, he, _, hc⟩ := G.exists_dist_path hdist
  have hfu : multiDist F initial u ≤ seed u := by
    exact (multiDist_le_seed F initial u).trans
      ((hinit u huk) ▸ multiDist_le_seed G seed u)
  have hknown : ∀ a ∈ known, multiDist F initial a ≤ multiDist G seed a := by
    intro a ha
    simpa only [hinit a ha] using multiDist_le_seed F initial a
  rcases walk_witness B known G F (multiDist G seed) (multiDist F initial) τ
    (multiDist_edge G seed) (multiDist_edge F initial) hknown hout he (seed u)
    (multiDist_le_seed G seed u) hfu with hv | ⟨Z, hZ, hcard, hz⟩
  · exact False.elim (not_le_of_gt hgap (by simpa only [hc, ← hu] using hv))
  · exact ⟨Z, hZ, hcard, fun z hzm => by simpa only [hc, ← hu] using hz z hzm⟩

namespace BlockSearch

open StoredEdges

variable {n : ℕ}

def blockGraph (edges : List (Edge n)) (B : Finset (Fin n)) : Graph (Fin n) :=
  fun a b => if a ∈ B ∧ b ∈ B then graphOfEdges edges a b else ⊤

theorem blockGraph_subgraph (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) (a b : Fin n) :
    blockGraph edges B a b ≤ graphOfEdges (Skeleton.build hn B known τ edges) a b := by
  apply (le_graphOfEdges_iff _ a b _).mpr
  intro e he hs ht
  have hm := Skeleton.retained hn B known τ edges he
  have hb : a ∈ B ∧ b ∈ B := ⟨hs ▸ hm.2.1, ht ▸ hm.2.2.1⟩
  simpa [blockGraph, hb, hs, ht] using graphOfEdges_le_edge edges hm.1

theorem outgoing_witness (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (edges : List (Edge n)) :
    OutgoingWitness B known (blockGraph edges B)
      (graphOfEdges (Skeleton.build hn B known τ edges)) τ := by
  intro a b hbk
  by_cases htop : blockGraph edges B a b = ⊤
  · exact Or.inl (by rw [htop]; exact le_top)
  have hab : a ∈ B ∧ b ∈ B := by
    by_contra h
    exact htop (by simp [blockGraph, h])
  have hg : graphOfEdges edges a b ≠ ⊤ := by
    simpa [blockGraph, hab] using htop
  obtain ⟨e, he, hs, ht, hw⟩ := exists_edge_eq edges hg
  have ho := Skeleton.outgoing hn B known τ edges he (hs ▸ hab.1) (ht ▸ hab.2)
    (ht ▸ hbk)
  simpa [hs, ht, hw, blockGraph, hab] using ho

def labels (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) : DistanceArray n :=
  StoredSearch.run (Skeleton.build hn B known τ edges) initial

theorem labels_correct (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) (v : Fin n) :
    (labels hn B known τ initial edges).get v =
      multiDist (graphOfEdges (Skeleton.build hn B known τ edges)) initial.get v :=
  StoredSearch.correct _ _ _

theorem actual_gap (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (seed : Fin n → Distance) (initial : DistanceArray n) (edges : List (Edge n))
    (hseed : ∀ u, u ∉ known → seed u = ⊤)
    (hinit : ∀ u ∈ known, initial.get u = multiDist (blockGraph edges B) seed u) :
    GapWitness B known (multiDist (blockGraph edges B) seed)
      (labels hn B known τ initial edges).get τ := by
  have heq : (labels hn B known τ initial edges).get =
      multiDist (graphOfEdges (Skeleton.build hn B known τ edges)) initial.get :=
    funext (labels_correct hn B known τ initial edges)
  rw [heq]
  exact multisource_gap B known (blockGraph edges B)
    (graphOfEdges (Skeleton.build hn B known τ edges)) seed initial.get τ hseed hinit
    (outgoing_witness hn B known τ edges)

theorem actual_lower (hn : 0 < n) (B known : Finset (Fin n)) (τ : ℕ)
    (seed : Fin n → Distance) (initial : DistanceArray n) (edges : List (Edge n))
    (hinit : ∀ u, multiDist (blockGraph edges B) seed u ≤ initial.get u) (v : Fin n) :
    multiDist (blockGraph edges B) seed v ≤ (labels hn B known τ initial edges).get v := by
  rw [labels_correct]
  exact multiDist_potential (blockGraph_subgraph hn B known τ edges) hinit v

theorem search_certificate (hn : 0 < n) (B known : Finset (Fin n)) (τ r : ℕ)
    (seed : Fin n → Distance) (initial : DistanceArray n) (edges : List (Edge n))
    (hseed : ∀ u, u ∉ known → seed u = ⊤)
    (hinit : ∀ u, initial.get u =
      if u ∈ known then multiDist (blockGraph edges B) seed u else ⊤)
    (hsmall : (found B known (labels hn B known τ initial edges).get r).card < τ) :
    let d := multiDist (blockGraph edges B) seed
    let f := (labels hn B known τ initial edges).get
    found B known f r = found B known d r ∧
      (∀ v ∈ found B known f r, f v = d v) ∧
      nextDistance B (known ∪ found B known f r) f =
        nextDistance B (known ∪ found B known f r) d := by
  dsimp only
  have hge := actual_lower hn B known τ seed initial edges (fun u => by
    rw [hinit]
    split_ifs
    · exact le_rfl
    · exact le_top)
  have hgap := actual_gap hn B known τ seed initial edges hseed
    (fun u hu => by simp only [hinit, hu, ↓reduceIte])
  exact ⟨certificate_complete B known _ _ r τ (fun v _ => hge v) hgap hsmall,
    certificate_exact B known _ _ r τ (fun v _ => hge v) hgap hsmall,
    certificate_next B known _ _ r τ (fun v _ => hge v) hgap hsmall⟩

end BlockSearch

end StreamingReachability.Core
