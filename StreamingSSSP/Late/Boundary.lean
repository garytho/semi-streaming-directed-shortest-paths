module

public import StreamingSSSP.Late.Geometry
public import StreamingSSSP.Late.Choice
public import StreamingSSSP.Shifts

@[expose] public section

namespace StreamingSSSP.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {V : Type*} [Fintype V]

def NoBridge (H : Graph V) (xs : List V) (p : V) (R : ℝ) : Prop :=
  ¬ ((∃ v ∈ xs, Within H p v R) ∧ ∃ v ∈ xs, Within H v p R)

def AdmissibleChild (H : Graph V) (S P : Finset V) (rho : V → ℝ)
    (D R : ℝ) (xs : List V) (X : Finset V) : Prop :=
  (∃ L, X = coreChild H S P rho L) ∨
  ∃ p ∈ P, X = S ∩ fringe H p (rho p) D ∧ NoBridge H xs p R

def offset (i : Fin 3) : ℝ := (i.val : ℝ) - 1

def offsetRadius (rho D : ℝ) (i : Fin 3) : ℝ := rho + offset i * D

theorem offset_le_one (i : Fin 3) : offset i ≤ 1 := by
  have h : (i.val : ℝ) ≤ 2 := by exact_mod_cast (show i.val ≤ 2 from by omega)
  unfold offset
  linarith

theorem no_bridge_directions (H : Graph V) (xs : List V) (p : V) (R T : ℝ)
    {u v : V} (hu : u ∈ xs) (hv : v ∈ xs) (hT : T ≤ R)
    (hnb : NoBridge H xs p R) :
    (¬ Within H u p T ∧ ¬ Within H v p T) ∨
      (¬ Within H p u T ∧ ¬ Within H p v T) := by
  by_cases ha : ∃ w ∈ xs, Within H p w R
  · exact Or.inl ⟨fun h => hnb ⟨ha, u, hu, within_mono h hT⟩,
      fun h => hnb ⟨ha, v, hv, within_mono h hT⟩⟩
  · exact Or.inr ⟨fun h => ha ⟨u, hu, within_mono h hT⟩,
      fun h => ha ⟨v, hv, within_mono h hT⟩⟩

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t u v : Fin n}

def Type3 (H : Graph (Fin n)) (S P : Finset (Fin n)) (rho : Fin n → ℝ)
    (D Rmax : ℝ) (xs : List (Fin n)) (e : Edge R G u v) : Prop :=
  ∃ X : Finset (Fin n), AdmissibleChild H S P rho D Rmax xs X ∧
    u ∈ X ∧ v ∈ X ∧ ¬ e.Inside X

theorem type3_windows (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S P : Finset (Fin n)) (hS : Q.Inside S) (rho : Fin n → ℝ) (D Rmax : ℝ)
    (hrho : ∀ p ∈ P, rho p + D ≤ Rmax)
    {e : Path.PackedEdge R G} (he : e ∈ Q.edges)
    (hcut : Type3 (rounded A (R.restricted G S)) S P rho D Rmax Q.vertices e.2.2) :
    ∃ p ∈ P, ∃ i : Fin 3,
      windows (rounded A (R.restricted G S)) p e.1 e.2.1
        (e.2.2.searchWeight A : ℝ) (offsetRadius (rho p) D i) := by
  let H := rounded A (R.restricted G S)
  obtain ⟨Pre, Post, hQ⟩ := Q.edge_decompose he
  have hparts := (Pre.inside_append (.cons e.2.2 Post)).mp (by rwa [← hQ])
  have heS := (Path.inside_cons e.2.2 Post).mp hparts.2 |>.1
  have huQ : e.1 ∈ Q.vertices := by
    rw [hQ]
    have h := (Pre.append (.cons e.2.2 Post)).vertex_mem Pre.length
    rwa [Pre.vertex_append_length] at h
  have hvQ : e.2.1 ∈ Q.vertices := by
    have hmem : e.2.1 ∈ (Path.cons e.2.2 Post).vertices :=
      List.mem_cons_of_mem _ (endpoints_mem Post.endpoints).1
    rw [hQ]
    exact Pre.mem_vertices_append_right _ hmem
  obtain ⟨X, hX, huX, hvX, heX⟩ := hcut
  have hz : ∃ z ∈ e.2.2.vertices, z ∉ X := by
    by_contra hn
    apply heX
    intro z hz
    by_contra hzX
    exact hn ⟨z, hz, hzX⟩
  obtain ⟨z, hz, hzX⟩ := hz
  have hbounds := e.2.2.subpath_bounds A hA heS hz
  rcases hX with ⟨L, rfl⟩ | ⟨p, hp, rfl, hnb⟩
  · obtain ⟨p, hp, hsep⟩ := core_cut H S P rho L huX hvX (heS z hz) hzX
    refine ⟨p, hp, ⟨1, by decide⟩, ?_⟩
    have hw := separation_windows H hbounds.1 hbounds.2 hsep
    convert hw using 1; norm_num [offsetRadius, offset]
  · simp only [Finset.mem_inter] at huX hvX hzX
    have huF : e.1 ∈ fringe H p (rho p) D := huX.2
    have hvF : e.2.1 ∈ fringe H p (rho p) D := hvX.2
    have hzF : z ∉ fringe H p (rho p) D :=
      fun h => hzX ⟨heS z hz, h⟩
    have hd := no_bridge_directions H Q.vertices p Rmax (rho p + D)
      huQ hvQ (hrho p hp) hnb
    rcases fringe_cut H p (rho p) D huF hvF hzF hd with hsep | hsep
    · refine ⟨p, hp, ⟨0, by decide⟩, ?_⟩
      have hw := separation_windows H hbounds.1 hbounds.2 hsep
      simpa [offsetRadius, offset, sub_eq_add_neg] using hw
    · refine ⟨p, hp, ⟨2, by decide⟩, ?_⟩
      have hw := separation_windows H hbounds.1 hbounds.2 hsep
      convert hw using 1; norm_num [offsetRadius, offset]

theorem radius_lattice (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (hN : 0 < N) (p : Fin n) (z : Fin M × Fin N) (i : Fin 3) :
    offsetRadius (radius H D k M N hk p z) D i =
      (lambda k M + offset i) * D +
        (D / N) * Shifts.pointIndex (4 * k) M N (candidate H D k M N hk p) z.1 z.2 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [offsetRadius, radius, candidateRadius, shiftValue,
    Shifts.pointIndex, Nat.cast_add, Nat.cast_mul]
  field_simp [hN0]
  ring

theorem window_probability (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (hM : 0 < M) (hN : 0 < N) (hD : 0 < D) (p : Fin n)
    (d : Distance) (a : ℝ) (b : Bool) (i : Fin 3) (ha : D / N ≤ a) :
    (Law.uniformPair M N hM hN).prob (fun z =>
      Window d a b (offsetRadius (radius H D k M N hk p z) D i)) ≤
        2 * a / ((M : ℝ) * D) := by
  induction d using WithTop.recTopCoe with
  | top =>
      have he : (fun z : Fin M × Fin N =>
          Window ⊤ a b (offsetRadius (radius H D k M N hk p z) D i)) =
          fun _ => False := by
        funext z
        apply propext
        simp [Window]
      rw [he, Law.prob_false]
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have ha0 : 0 ≤ a := (le_of_lt (div_pos hD hN')).trans ha
      positivity
  | coe q =>
      let lo : ℝ := if b then q - a else q
      let hi : ℝ := if b then q else q + a
      have hlen : hi - lo = a := by cases b <;> simp [hi, lo]
      have hc := Shifts.window_charge (4 * k) M N (by omega) hM hN
        (candidate H D k M N hk p) ((lambda k M + offset i) * D) D lo hi hD
        (by rwa [hlen])
      apply le_trans _ (by simpa only [hlen] using hc)
      apply Law.prob_mono
      intro z hz
      rw [← radius_lattice H D k M N hk hN p z i]
      obtain ⟨q', hq, hr⟩ := hz
      have hqq : q' = q := WithTop.coe_eq_coe.mp hq.symm
      subst q'
      cases b <;> simpa only [Bool.false_eq_true, ↓reduceIte, lo, hi] using
        (show _ ∧ _ from ⟨hr.1, hr.2.le⟩)

def Hits (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (p u v : Fin n) (a : ℝ) (z : Fin M × Fin N) : Prop :=
  ∃ i : Fin 3, windows H p u v a (offsetRadius (radius H D k M N hk p z) D i)

theorem hits_probability (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (hM : 0 < M) (hN : 0 < N) (hD : 0 < D) (p u v : Fin n) (a : ℝ)
    (ha : D / N ≤ a) :
    (Law.uniformPair M N hM hN).prob (Hits H D k M N hk p u v a) ≤
      24 * a / ((M : ℝ) * D) := by
  let mu := Law.uniformPair M N hM hN
  have hw (i : Fin 3) :
      mu.prob (fun z => windows H p u v a
        (offsetRadius (radius H D k M N hk p z) D i)) ≤
          8 * a / ((M : ℝ) * D) := by
    have h1 := window_probability H D k M N hk hM hN hD p (H.dist p u) a false i ha
    have h2 := window_probability H D k M N hk hM hN hD p (H.dist p v) a true i ha
    have h3 := window_probability H D k M N hk hM hN hD p (H.dist v p) a false i ha
    have h4 := window_probability H D k M N hk hM hN hD p (H.dist u p) a true i ha
    have h := mu.prob_union
      (fun z => Window (H.dist p u) a false
        (offsetRadius (radius H D k M N hk p z) D i))
      (fun z => Window (H.dist p v) a true
        (offsetRadius (radius H D k M N hk p z) D i) ∨
        Window (H.dist v p) a false
          (offsetRadius (radius H D k M N hk p z) D i) ∨
        Window (H.dist u p) a true
          (offsetRadius (radius H D k M N hk p z) D i))
    have h' := mu.prob_union
      (fun z => Window (H.dist p v) a true
        (offsetRadius (radius H D k M N hk p z) D i))
      (fun z => Window (H.dist v p) a false
        (offsetRadius (radius H D k M N hk p z) D i) ∨
        Window (H.dist u p) a true
          (offsetRadius (radius H D k M N hk p z) D i))
    have h'' := mu.prob_union
      (fun z => Window (H.dist v p) a false
        (offsetRadius (radius H D k M N hk p z) D i))
      (fun z => Window (H.dist u p) a true
        (offsetRadius (radius H D k M N hk p z) D i))
    change mu.prob _ ≤ _ at h1 h2 h3 h4
    change mu.prob _ ≤ _ at h
    calc
      mu.prob _ ≤ _ := h
      _ ≤ 2 * a / ((M : ℝ) * D) +
          (2 * a / ((M : ℝ) * D) +
            (2 * a / ((M : ℝ) * D) + 2 * a / ((M : ℝ) * D))) :=
        add_le_add h1 (h'.trans (add_le_add h2 (h''.trans (add_le_add h3 h4))))
      _ = _ := by ring
  calc
    _ = mu.prob (fun z => ∃ i ∈ (Finset.univ : Finset (Fin 3)),
        windows H p u v a (offsetRadius (radius H D k M N hk p z) D i)) := by
      apply mu.prob_congr
      intro z
      simp [Hits]
    _ ≤ ∑ i : Fin 3, mu.prob (fun z => windows H p u v a
        (offsetRadius (radius H D k M N hk p z) D i)) := mu.finite_union _ _
    _ ≤ ∑ _i : Fin 3, 8 * a / ((M : ℝ) * D) := Finset.sum_le_sum fun i _ => hw i
    _ = _ := by simp; ring

def endpointNear (H : Graph (Fin n)) (s t : Fin n) (Rmax : ℝ) : Finset (Fin n) :=
  searchIn H t Rmax ∪ searchOut H s Rmax

theorem endpointNear_card (H : Graph (Fin n)) (s t : Fin n) (Rmax : ℝ) (b : ℕ)
    (hin : (searchIn H t Rmax).card ≤ b) (hout : (searchOut H s Rmax).card ≤ b) :
    (endpointNear H s t Rmax).card ≤ 2 * b :=
  (Finset.card_union_le _ _).trans (by omega)

/-- In the second and fourth windows the remaining path budget is `D-a`.
This is what leaves exactly the two units of radius margin. -/
theorem window_near (Q : Path R G s t) (A : ℕ) (S : Finset (Fin n))
    (hS : Q.Inside S) (D rho Rmax : ℝ) (hQ : (Q.searchWeight A : ℝ) ≤ D)
    (hrho : rho + D < Rmax) {e : Path.PackedEdge R G} (he : e ∈ Q.edges)
    (p : Fin n) (hw : windows (rounded A (R.restricted G S)) p e.1 e.2.1
      (e.2.2.searchWeight A : ℝ) rho) :
    p ∈ endpointNear (rounded A (R.restricted G S)) s t Rmax := by
  let H := rounded A (R.restricted G S)
  obtain ⟨Pre, Post, hpath⟩ := Q.edge_decompose he
  have hparts := (Pre.inside_append (.cons e.2.2 Post)).mp (by rwa [← hpath])
  obtain ⟨heS, hPost⟩ := (Path.inside_cons e.2.2 Post).mp hparts.2
  have hPre := Pre.forward A hparts.1
  have hTail := Post.forward A hPost
  have hEdge := within_edge H (e.2.2.search_edge A heS).le
  have hbudget : (Pre.searchWeight A : ℝ) + e.2.2.searchWeight A +
      Post.searchWeight A ≤ D := by
    simpa only [hpath, Path.searchWeight_append, Path.searchWeight, Nat.cast_add,
      add_assoc] using hQ
  have hp0 : (0 : ℝ) ≤ Pre.searchWeight A := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ Post.searchWeight A := Nat.cast_nonneg _
  have inNear (h : Within H p t (rho + D)) :
      p ∈ endpointNear H s t Rmax := by
    apply Finset.mem_union_left
    simp only [searchIn, Finset.mem_filter, Finset.mem_univ, true_and]
    exact within_mono h hrho.le
  have outNear (h : Within H s p (rho + D)) :
      p ∈ endpointNear H s t Rmax := by
    apply Finset.mem_union_right
    simp only [searchOut, Finset.mem_filter, Finset.mem_univ, true_and]
    exact within_mono h hrho.le
  rcases hw with ⟨q, hq, hlo, _⟩ | ⟨q, hq, hlo, _⟩ |
    ⟨q, hq, hlo, _⟩ | ⟨q, hq, hlo, _⟩
  · apply inNear
    exact within_mono (within_trans (within_trans
      (show Within H p e.1 rho from ⟨q, hq, hlo⟩) hEdge) hTail) (by linarith)
  · apply inNear
    exact within_mono (within_trans
      (show Within H p e.2.1 (rho + e.2.2.searchWeight A) from
        ⟨q, hq, by linarith⟩) hTail) (by linarith)
  · apply outNear
    exact within_mono (within_trans (within_trans hPre hEdge)
      (show Within H e.2.1 p rho from ⟨q, hq, hlo⟩)) (by linarith)
  · apply outNear
    exact within_mono (within_trans hPre
      (show Within H e.1 p (rho + e.2.2.searchWeight A) from
        ⟨q, hq, by linarith⟩)) (by linarith)

theorem radius_margin (H : Graph (Fin n)) (D : ℝ) (k M N : ℕ) (hk : 0 < k)
    (hD : 0 < D) (p : Fin n) (z : Fin M × Fin N) (i : Fin 3) :
    offsetRadius (radius H D k M N hk p z) D i + D < searchRadius k M D := by
  have h := (radius_bounds H D k M N hk hD p z).2
  have hi := mul_le_mul_of_nonneg_right (offset_le_one i) hD.le
  dsimp only [radius, offsetRadius, nearRadius, searchRadius] at *
  nlinarith

def type3Count (Q : Path R G s t) (H : Graph (Fin n)) (S P : Finset (Fin n))
    (rho : Fin n → ℝ) (D Rmax : ℝ) : ℕ :=
  (Q.edges.map fun e => if Type3 H S P rho D Rmax Q.vertices e.2.2 then 1 else 0).sum

theorem expect_list_sum {T E : Type*} (mu : Law T) (xs : List E) (f : E → T → ℝ) :
    mu.expect (fun t => (xs.map fun e => f e t).sum) =
      (xs.map fun e => mu.expect (f e)).sum := by
  induction xs with
  | nil => simp
  | cons e xs ih => simp only [List.map_cons, List.sum_cons, Law.expect_add, ih]

theorem type3_indicator_charge (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S : Finset (Fin n)) (hS : Q.Inside S) (D : ℝ) (hD : 0 < D)
    (hQ : (Q.searchWeight A : ℝ) ≤ D)
    (k M N : ℕ) (hk : 0 < k) (hM : 0 < M) (hN : 0 < N)
    {e : Path.PackedEdge R G} (he : e ∈ Q.edges)
    (xs : List (Fin n × (Fin M × Fin N)))
    (hnd : (xs.map Prod.fst).Nodup) :
    (if Type3 (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) Q.vertices e.2.2
      then (1 : ℝ) else 0) ≤
    (xs.map fun z => if z.1 ∈ endpointNear (rounded A (R.restricted G S)) s t
        (searchRadius k M D) ∧
      Hits (rounded A (R.restricted G S)) D k M N hk z.1 e.1 e.2.1
        (e.2.2.searchWeight A : ℝ) z.2 then (1 : ℝ) else 0).sum := by
  let H := rounded A (R.restricted G S)
  let fallback : Fin M × Fin N := (⟨0, hM⟩, ⟨0, hN⟩)
  let f := fun p z => if p ∈ endpointNear H s t (searchRadius k M D) ∧
    Hits H D k M N hk p e.1 e.2.1 (e.2.2.searchWeight A : ℝ) z then (1 : ℝ) else 0
  rw [← Sampling.sum_pivots fallback xs hnd f]
  split_ifs with hcut
  · obtain ⟨p, hp, i, hi⟩ := type3_windows Q A hA S (Sampling.pivots xs) hS
      (radiusFor (radius H D k M N hk) fallback xs) D (searchRadius k M D)
      (by
        intro p _
        simpa [radiusFor, offsetRadius, offset] using
          (radius_margin H D k M N hk hD p
            (Sampling.ownerFor fallback xs p) ⟨1, by decide⟩).le) he hcut
    have hnear := window_near Q A S hS D _ _ hQ
      (radius_margin H D k M N hk hD p (Sampling.ownerFor fallback xs p) i) he p hi
    have hf : f p (Sampling.ownerFor fallback xs p) = 1 := by
      apply ite_eq_left
      exact ⟨hnear, i, hi⟩
    rw [← hf]
    exact Finset.single_le_sum (f := fun q => f q (Sampling.ownerFor fallback xs q))
      (fun q _ => by dsimp only [f]; split_ifs <;> norm_num) hp
  · exact Finset.sum_nonneg fun p _ => by dsimp [f]; split_ifs <;> norm_num

theorem expected_type3_edge (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S E : Finset (Fin n)) (hS : Q.Inside S) (D : ℝ) (hD : 0 < D)
    (hQ : (Q.searchWeight A : ℝ) ≤ D) (k M N b : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hgrid : D ≤ N)
    (hin : (searchIn (rounded A (R.restricted G S)) t (searchRadius k M D)).card ≤ b)
    (hout : (searchOut (rounded A (R.restricted G S)) s (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {e : Path.PackedEdge R G} (he : e ∈ Q.edges) :
    (Sampling.marked (fun _ : Fin n => Law.uniformPair M N hM hN) p hp hp1 E.toList).expect
      (fun xs => if Type3 (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) Q.vertices e.2.2
        then (1 : ℝ) else 0) ≤
      (48 * b * p / ((M : ℝ) * D)) * e.2.2.searchWeight A := by
  let H := rounded A (R.restricted G S)
  let mu := Sampling.marked (fun _ : Fin n => Law.uniformPair M N hM hN) p hp hp1 E.toList
  let C := endpointNear H s t (searchRadius k M D)
  let a : ℝ := e.2.2.searchWeight A
  let f := fun v z => if v ∈ C ∧ Hits H D k M N hk v e.1 e.2.1 a z
    then (1 : ℝ) else 0
  have hnd : Sampling.Holds mu (fun xs => (xs.map Prod.fst).Nodup) :=
    Sampling.holds_mono (Sampling.marked_keys_sublist _ p hp hp1 E.toList)
      (fun _ h => (Finset.nodup_toList E).sublist h)
  have hcharge := Sampling.expect_mono_on mu (Sampling.holds_mono hnd (fun xs hn =>
    type3_indicator_charge Q A hA S hS D hD hQ k M N hk hM hN he xs hn))
  change mu.expect _ ≤ mu.expect (fun xs => (xs.map fun z => f z.1 z.2).sum) at hcharge
  rw [Sampling.expected_total_finset] at hcharge
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hprob (v : Fin n) :
      (Law.uniformPair M N hM hN).expect (f v) ≤
        if v ∈ C then 24 * a / ((M : ℝ) * D) else 0 := by
    by_cases hv : v ∈ C
    · simp only [f, hv, true_and, ↓reduceIte]
      change (Law.uniformPair M N hM hN).prob _ ≤ _
      by_cases ha0 : e.2.2.searchWeight A = 0
      · have hevent : Hits H D k M N hk v e.1 e.2.1 a = fun _ => False := by
          funext z
          apply propext
          constructor
          · rintro ⟨i, hi⟩
            have h := windows_positive H hi
            simp [a, ha0] at h
          · simp
        rw [hevent, Law.prob_false]
        simp [a, ha0]
      · apply hits_probability H D k M N hk hM hN hD v e.1 e.2.1 a
        have hgrid' : D / N ≤ 1 := (div_le_one hN').mpr hgrid
        have ha1 : (1 : ℝ) ≤ a := by
          dsimp only [a]
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ha0)
        exact hgrid'.trans ha1
    · simp [f, hv]
  have hcard : ((E.filter fun v => v ∈ C).card : ℝ) ≤ 2 * b := by
    have h1 := Finset.card_le_card (show (E.filter fun v => v ∈ C) ⊆ C from by
      intro v hv; exact (Finset.mem_filter.mp hv).2)
    have h2 := endpointNear_card H s t (searchRadius k M D) b hin hout
    exact_mod_cast h1.trans h2
  apply hcharge.trans
  calc
    p * ∑ v ∈ E, (Law.uniformPair M N hM hN).expect (f v) ≤
        p * ∑ v ∈ E, if v ∈ C then 24 * a / ((M : ℝ) * D) else 0 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hprob v) hp
    _ = p * ((E.filter fun v => v ∈ C).card : ℝ) * (24 * a / ((M : ℝ) * D)) := by
      rw [← Finset.sum_filter]
      simp [mul_assoc]
    _ ≤ p * (2 * b) * (24 * a / ((M : ℝ) * D)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hp) (by dsimp [a]; positivity)
    _ = _ := by dsimp [a]; ring

/-- Unconditional local boundary charge for the actual minimum-shell radius
and independent eligible pivot coins. Child selection may depend on every owner. -/
theorem expected_type3 (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S E : Finset (Fin n)) (hS : Q.Inside S) (D : ℝ) (hD : 0 < D)
    (hQ : (Q.searchWeight A : ℝ) ≤ D) (k M N b : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hgrid : D ≤ N)
    (hin : (searchIn (rounded A (R.restricted G S)) t (searchRadius k M D)).card ≤ b)
    (hout : (searchOut (rounded A (R.restricted G S)) s (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (Sampling.marked (fun _ : Fin n => Law.uniformPair M N hM hN) p hp hp1 E.toList).expect
      (fun xs => (type3Count Q (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) : ℝ)) ≤
        48 * b * p / M := by
  let mu := Sampling.marked (fun _ : Fin n => Law.uniformPair M N hM hN) p hp hp1 E.toList
  let C : ℝ := 48 * b * p / ((M : ℝ) * D)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcast (xs : List (Fin n × (Fin M × Fin N))) :
      (type3Count Q (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) : ℝ) =
      (Q.edges.map fun e => if Type3 (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) Q.vertices e.2.2
        then (1 : ℝ) else 0).sum := by
    simp only [type3Count, Nat.cast_list_sum, List.map_map, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, Function.comp_def]
  simp_rw [hcast]
  rw [expect_list_sum]
  have hsum : (Q.edges.map fun e => mu.expect (fun xs =>
      if Type3 (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) Q.vertices e.2.2
        then (1 : ℝ) else 0)).sum ≤
      (Q.edges.map fun e => C * (e.2.2.searchWeight A : ℝ)).sum := by
    apply List.sum_le_sum
    intro e he
    exact expected_type3_edge Q A hA S E hS D hD hQ k M N b hk hM hN hgrid
      hin hout p hp hp1 he
  apply hsum.trans
  calc
    _ = C * (Q.searchWeight A : ℝ) := by
      rw [List.sum_map_mul_left]
      congr 1
      have h := congrArg (fun w : ℕ => (w : ℝ)) (Q.sum_edge_weights A)
      simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using h
    _ ≤ C * D := mul_le_mul_of_nonneg_left hQ hC
    _ = _ := by
      dsimp [C]
      field_simp

theorem boundary_numeric (b p M gamma k ell : ℝ)
    (_hb : 0 ≤ b) (_hp : 0 ≤ p) (hM : 0 < M)
    (hg : 0 < gamma) (hk : 0 < k) (hl : 0 < ell)
    (hbp : b * p ≤ 2 * gamma * k * ell)
    (hgroups : 384 * gamma ^ 2 * k ^ 2 * ell ^ 2 ≤ M) :
    48 * b * p / M ≤ 1 / (4 * gamma * k * ell) := by
  apply (div_le_div_iff₀ hM (by positivity : 0 < 4 * gamma * k * ell)).mpr
  have h := mul_le_mul_of_nonneg_right hbp
    (by positivity : 0 ≤ 192 * gamma * k * ell)
  nlinarith

end

end StreamingSSSP.Late
