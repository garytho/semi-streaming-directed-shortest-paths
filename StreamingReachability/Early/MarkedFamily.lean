module

public import StreamingReachability.Early.Sampling
public import StreamingReachability.Probability.Sequence

@[expose] public section

namespace StreamingReachability.Early.Sampling

open scoped Classical

noncomputable section

variable {V O : Type*}

theorem marked_expect_congr (left right : V → Law O)
    (h : ∀ v f, (left v).expect f = (right v).expect f)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (vertices : List V) (f : List (V × O) → ℝ) :
    (marked left p hp hp1 vertices).expect f = (marked right p hp hp1 vertices).expect f := by
  induction vertices generalizing f with
  | nil => simp [marked]
  | cons v vertices ih =>
      simp only [marked, Law.expect_bind]
      apply congrArg (Law.coin p hp hp1).expect
      funext b
      cases b with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih f
      | true =>
          simp only [↓reduceIte, Law.expect_bind, Law.expect_map]
          rw [h v (fun o => (marked left p hp hp1 vertices).expect (fun rest => f ((v, o) :: rest)))]
          apply congrArg (right v).expect
          funext o
          exact ih (fun rest => f ((v, o) :: rest))

theorem ownerLaw_uniformPair_expect (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (f : Fin M × Fin N → ℝ) :
    (Early.ownerLaw M N hM hN).expect f = (Law.uniformPair M N hM hN).expect f := by
  simp only [Early.ownerLaw, Law.uniformPair, Law.expect_bind, Law.expect_map]
  exact (Law.expect_comm (Law.uniform M hM) (Law.uniform N hN) (fun sigma phi => f (sigma, phi))).symm

def zipSelected : List V → List Bool → List O → List (V × O)
  | v :: vs, b :: bs, o :: os =>
      if b then (v, o) :: zipSelected vs bs os else zipSelected vs bs os
  | _, _, _ => []

def ownedSubset (vertices : List V) (coins : V → Bool) (owners : V → O) : List (V × O) :=
  vertices.filterMap fun v => if coins v then some (v, owners v) else none

theorem zipSelected_map (vertices : List V) (coins : V → Bool) (owners : V → O) :
    zipSelected vertices (vertices.map coins) (vertices.map owners) = ownedSubset vertices coins owners := by
  induction vertices with
  | nil => rfl
  | cons v vertices ih =>
      cases hb : coins v <;> simp only [List.map_cons, zipSelected, ownedSubset, List.filterMap_cons,
        hb, Bool.false_eq_true, ↓reduceIte] at *
      · exact ih
      · exact congrArg ((v, owners v) :: ·) ih

theorem samples_marked (owner : V → Law O) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (vertices : List V) (f : List (V × O) → ℝ) :
    (Law.sampleIndices (fun _ : V => Law.coin p hp hp1) vertices).expect (fun coins =>
        (Law.sampleIndices owner vertices).expect (fun owners => f (zipSelected vertices coins owners))) =
      (marked owner p hp hp1 vertices).expect f := by
  induction vertices generalizing f with
  | nil => simp [Law.sampleIndices, marked, zipSelected]
  | cons v vertices ih =>
      simp only [Law.sampleIndices, Law.expect_bind, Law.expect_map, marked]
      apply congrArg (Law.coin p hp hp1).expect
      funext b
      cases b with
      | false =>
          simp only [zipSelected, Bool.false_eq_true, ↓reduceIte, Law.expect_const]
          exact ih f
      | true =>
          simp only [zipSelected, ↓reduceIte, Law.expect_bind, Law.expect_map]
          rw [Law.expect_comm (Law.sampleIndices (fun _ : V => Law.coin p hp hp1) vertices)
            (owner v) (fun coins o => (Law.sampleIndices owner vertices).expect
              (fun owners => f ((v, o) :: zipSelected vertices coins owners)))]
          apply congrArg (owner v).expect
          funext o
          exact ih (fun rest => f ((v, o) :: rest))

theorem family_ownedSubset {n : ℕ} [Fintype O] (coin : Fin n → Law Bool)
    (owner : Fin n → Law O) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (vertices : List (Fin n)) (hvertices : vertices.Nodup)
    (hcoin : ∀ v ∈ vertices, coin v = Law.coin p hp hp1) (f : List (Fin n × O) → ℝ) :
    (Law.family n coin).expect (fun coins =>
        (Law.family n owner).expect (fun owners => f (ownedSubset vertices coins owners))) =
      (marked owner p hp hp1 vertices).expect f := by
  have ho (coins : List Bool) :
      (Law.family n owner).expect (fun owners => f (zipSelected vertices coins (vertices.map owners))) =
        (Law.sampleIndices owner vertices).expect (fun owners => f (zipSelected vertices coins owners)) :=
    (Law.expect_sampleIndices_projection n owner vertices hvertices
      (fun owners => f (zipSelected vertices coins owners))).symm
  have hc := Law.expect_sampleIndices_projection n coin vertices hvertices
    (fun coins => (Law.family n owner).expect
      (fun owners => f (zipSelected vertices coins (vertices.map owners))))
  calc
    _ = (Law.family n coin).expect (fun coins =>
        (Law.family n owner).expect (fun owners =>
          f (zipSelected vertices (vertices.map coins) (vertices.map owners)))) := by
      apply congrArg (Law.family n coin).expect
      funext coins
      apply congrArg (Law.family n owner).expect
      funext owners
      rw [zipSelected_map]
    _ = (Law.sampleIndices coin vertices).expect (fun coins =>
        (Law.family n owner).expect (fun owners =>
          f (zipSelected vertices coins (vertices.map owners)))) := hc.symm
    _ = (Law.sampleIndices (fun _ : Fin n => Law.coin p hp hp1) vertices).expect
        (fun coins => (Law.sampleIndices owner vertices).expect
          (fun owners => f (zipSelected vertices coins owners))) := by
      rw [Law.sampleIndices_congr coin (fun _ => Law.coin p hp hp1) vertices hcoin]
      simp_rw [ho]
    _ = _ := samples_marked owner p hp hp1 vertices f

theorem ownedSubset_mem (vertices : List V) (coins : V → Bool) (owners : V → O) (v : V) (o : O) :
    (v, o) ∈ ownedSubset vertices coins owners ↔ v ∈ vertices ∧ coins v = true ∧ o = owners v := by
  simp only [ownedSubset, List.mem_filterMap]
  constructor
  · rintro ⟨u, hu, he⟩
    by_cases hb : coins u = true
    · have hp : (u, owners u) = (v, o) := by simpa only [hb, ↓reduceIte, Option.some.injEq] using he
      obtain ⟨rfl, ho⟩ := Prod.mk.inj hp
      exact ⟨hu, hb, ho.symm⟩
    · simp [hb] at he
  · rintro ⟨hv, hb, ho⟩
    subst o
    exact ⟨v, hv, by simp only [hb, ↓reduceIte]⟩

theorem ownedSubset_keys (vertices : List V) (coins : V → Bool) (owners : V → O) :
    ((ownedSubset vertices coins owners).map Prod.fst).Sublist vertices := by
  induction vertices with
  | nil => simp [ownedSubset]
  | cons v vertices ih =>
      cases hb : coins v
      · simp only [ownedSubset, List.filterMap_cons, hb, Bool.false_eq_true, ↓reduceIte]
        exact ih.trans (List.sublist_cons_self _ _)
      · simp only [ownedSubset, List.filterMap_cons, hb, ↓reduceIte, List.map_cons]
        exact List.Sublist.cons_cons v ih

theorem ownedSubset_pivots (vertices : List V) (coins : V → Bool) (owners : V → O) :
    pivots (ownedSubset vertices coins owners) = vertices.toFinset.filter (fun v => coins v = true) := by
  ext v
  simp only [pivots, Finset.mem_filter, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨u, o⟩, hm, he⟩
    subst v
    have h := (ownedSubset_mem vertices coins owners u o).mp hm
    exact ⟨h.1, h.2.1⟩
  · rintro ⟨hv, hb⟩
    exact ⟨(v, owners v), (ownedSubset_mem vertices coins owners v (owners v)).mpr ⟨hv, hb, rfl⟩, rfl⟩

theorem ownedSubset_owner (vertices : List V) (hvertices : vertices.Nodup)
    (coins : V → Bool) (owners : V → O) (fallback : O) (v : V)
    (hv : v ∈ pivots (ownedSubset vertices coins owners)) :
    ownerFor fallback (ownedSubset vertices coins owners) v = owners v := by
  have hn := hvertices.sublist (ownedSubset_keys vertices coins owners)
  rw [ownedSubset_pivots] at hv
  obtain ⟨hv, hb⟩ := Finset.mem_filter.mp hv
  exact ownerFor_mem fallback hn
    ((ownedSubset_mem vertices coins owners v (owners v)).mpr ⟨List.mem_toFinset.mp hv, hb, rfl⟩)

end

end StreamingReachability.Early.Sampling
