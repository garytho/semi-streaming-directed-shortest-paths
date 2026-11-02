module

public import StreamingSSSP.Early.Fractional
public import StreamingSSSP.Early.Shells

@[expose] public section

namespace StreamingSSSP.Early

open scoped Classical BigOperators

noncomputable section

namespace Sampling

variable {V O T : Type*}

def Holds (mu : Law T) (P : T → Prop) : Prop := ∀ z ∈ mu.atoms, P z.1

theorem holds_pure (t : T) (P : T → Prop) (h : P t) : Holds (Law.pure t) P := by
  intro z hz
  have he : z = (t, 1) := by simpa [Law.pure] using hz
  simpa [he] using h

theorem holds_mono {mu : Law T} {P Q : T → Prop}
    (h : Holds mu P) (hPQ : ∀ t, P t → Q t) : Holds mu Q :=
  fun z hz => hPQ z.1 (h z hz)

theorem holds_map {mu : Law T} {P : T → Prop} (h : Holds mu P)
    (f : T → O) (Q : O → Prop) (hQ : ∀ t, P t → Q (f t)) :
    Holds (mu.map f) Q := by
  intro z hz
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hz
  exact hQ t.1 (h t ht)

theorem holds_bind (mu : Law T) (f : T → Law O) (P : O → Prop)
    (h : ∀ t, Holds (f t) P) : Holds (mu.bind f) P := by
  intro z hz
  obtain ⟨t, _, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hz
  exact h t.1 o ho

theorem expect_mono_on (mu : Law T) {f g : T → ℝ}
    (h : Holds mu (fun t => f t ≤ g t)) : mu.expect f ≤ mu.expect g := by
  have hs : ∀ (xs : List (T × ℝ)),
      (∀ z ∈ xs, 0 ≤ z.2) →
      (∀ z ∈ xs, f z.1 ≤ g z.1) →
      weightedSum xs f ≤ weightedSum xs g := by
    intro xs
    induction xs with
    | nil => simp
    | cons z xs ih =>
        intro h0 hfg
        exact add_le_add (mul_le_mul_of_nonneg_left (hfg z (by simp)) (h0 z (by simp)))
          (ih (fun t ht => h0 t (by simp [ht])) (fun t ht => hfg t (by simp [ht])))
  exact hs mu.atoms mu.nonneg h

/-- Local conditional sampling on a fixed eligible list. This does not assign
new ranks: the controller instantiates it after deferring the current coins. -/
def marked (owner : V → Law O) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    List V → Law (List (V × O))
  | [] => Law.pure []
  | v :: vs =>
      (Law.coin p hp hp1).bind fun hit =>
        if hit then (owner v).bind fun o => (marked owner p hp hp1 vs).map ((v, o) :: ·)
        else marked owner p hp hp1 vs

theorem marked_keys_sublist (owner : V → Law O) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (vs : List V) :
    Holds (marked owner p hp hp1 vs) (fun xs => (xs.map Prod.fst).Sublist vs) := by
  induction vs with
  | nil => exact holds_pure [] _ (by simp)
  | cons v vs ih =>
      apply holds_bind
      intro hit
      cases hit with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact holds_mono ih (fun xs hs => hs.trans (List.sublist_cons_self _ _))
      | true =>
          simp only [↓reduceIte]
          apply holds_bind
          intro o
          exact holds_map ih ((v, o) :: ·) _
            (fun xs hs => List.Sublist.cons_cons v hs)

def pivots (xs : List (V × O)) : Finset V := (xs.map Prod.fst).toFinset

def ownerFor (fallback : O) : List (V × O) → V → O
  | [], _ => fallback
  | (u, o) :: xs, v => if u = v then o else ownerFor fallback xs v

theorem ownerFor_mem (fallback : O) {xs : List (V × O)}
    (hn : (xs.map Prod.fst).Nodup) {v : V} {o : O} (hmem : (v, o) ∈ xs) :
    ownerFor fallback xs v = o := by
  induction xs with
  | nil => simp at hmem
  | cons z xs ih =>
      obtain ⟨u, t⟩ := z
      have hnd := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hmem with he | hm
      · cases he
        simp [ownerFor]
      · have huv : u ≠ v := by
          intro he
          apply hnd.1
          exact List.mem_map.mpr ⟨(v, o), hm, he.symm⟩
        simp only [ownerFor, huv, ↓reduceIte]
        exact ih hnd.2 hm

theorem sum_pivots (fallback : O) (xs : List (V × O))
    (hn : (xs.map Prod.fst).Nodup) (f : V → O → ℝ) :
    (∑ v ∈ pivots xs, f v (ownerFor fallback xs v)) =
      (xs.map fun z => f z.1 z.2).sum := by
  rw [pivots, List.sum_toFinset _ hn]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro z hz
  change f z.1 (ownerFor fallback xs z.1) = f z.1 z.2
  rw [ownerFor_mem fallback hn hz]

def All (K : V → O → Prop) (xs : List (V × O)) : Prop :=
  ∀ z ∈ xs, K z.1 z.2

theorem expect_indicator (mu : Law O) (P : O → Prop) (c : ℝ) :
    mu.expect (fun o => if P o then c else 0) = c * mu.prob P := by
  rw [Law.prob, ← Law.expect_mul]
  congr 1
  funext o
  by_cases h : P o <;> simp [h]

theorem prob_cons_all (mu : Law (List (V × O))) (K : V → O → Prop) (v : V) (o : O) :
    (mu.map ((v, o) :: ·)).prob (All K) =
      if K v o then mu.prob (All K) else 0 := by
  rw [Law.prob_map]
  by_cases h : K v o
  · rw [ite_eq_left h]
    exact mu.prob_congr _ _ (by intro xs; simp [All, h])
  · rw [ite_eq_right h]
    have he := mu.prob_congr (fun xs => All K ((v, o) :: xs)) (fun _ => False)
      (by intro xs; simp [All, h])
    simpa using he

theorem probability_all (owner : V → Law O) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (vs : List V) (K : V → O → Prop) :
    (marked owner p hp hp1 vs).prob (All K) =
      (vs.map fun v => 1 - p + p * (owner v).prob (K v)).prod := by
  induction vs with
  | nil => simp [marked, Law.prob, All]
  | cons v vs ih =>
      rw [marked, Law.prob_bind, Law.expect_coin]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Law.prob_bind]
      simp_rw [prob_cons_all]
      rw [expect_indicator, ih]
      simp only [List.map_cons, List.prod_cons]
      ring

theorem probability_all_finset (owner : V → Law O) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset V) (K : V → O → Prop) :
    (marked owner p hp hp1 A.toList).prob (All K) =
      ∏ v ∈ A, (1 - p + p * (owner v).prob (K v)) := by
  rw [probability_all, ← List.prod_toFinset _ (Finset.nodup_toList A)]
  simp

theorem probability_all_subset (owner : V → Law O) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (E A : Finset V) (hAE : A ⊆ E)
    (K : V → O → Prop) :
    (marked owner p hp hp1 E.toList).prob (All K) ≤
      ∏ v ∈ A, (1 - p + p * (owner v).prob (K v)) := by
  have hm := Law.prob_mono (marked owner p hp hp1 E.toList)
    (P := All K) (Q := All (fun v o => v ∈ A → K v o))
    (by intro xs h z hz _; exact h z hz)
  apply hm.trans_eq
  rw [probability_all_finset]
  have hprob (v : V) :
      (owner v).prob (fun o => v ∈ A → K v o) =
        if v ∈ A then (owner v).prob (K v) else 1 := by
    by_cases h : v ∈ A
    · simp only [h, true_implies, ↓reduceIte]
    · simp [h]
  simp_rw [hprob]
  rw [← Finset.prod_subset hAE (by
    intro v _ hv
    simp [hv])]
  apply Finset.prod_congr rfl
  intro v hv
  simp [hv]

theorem expected_total (owner : V → Law O) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (vs : List V) (f : V → O → ℝ) :
    (marked owner p hp hp1 vs).expect
      (fun xs => (xs.map fun z => f z.1 z.2).sum) =
        p * (vs.map fun v => (owner v).expect (f v)).sum := by
  induction vs with
  | nil => simp [marked]
  | cons v vs ih =>
      rw [marked, Law.expect_bind, Law.expect_coin]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Law.expect_bind]
      simp_rw [Law.expect_map, List.map_cons, List.sum_cons, Law.expect_add,
        Law.expect_const]
      rw [ih]
      ring

theorem expected_total_finset (owner : V → Law O) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset V) (f : V → O → ℝ) :
    (marked owner p hp hp1 A.toList).expect
      (fun xs => (xs.map fun z => f z.1 z.2).sum) =
        p * ∑ v ∈ A, (owner v).expect (f v) := by
  rw [expected_total, ← List.sum_toFinset _ (Finset.nodup_toList A)]
  simp

theorem expect_finset_sum (mu : Law T) (A : Finset V) (f : V → T → ℝ) :
    mu.expect (fun t => ∑ v ∈ A, f v t) = ∑ v ∈ A, mu.expect (f v) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert v A hv ih =>
      simp only [Finset.sum_insert hv, Law.expect_add, ih]

theorem expected_filter_card (mu : Law T) (A : Finset V) (P : V → T → Prop) :
    mu.expect (fun t => ((A.filter fun v => P v t).card : ℝ)) =
      ∑ v ∈ A, mu.prob (P v) := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  exact expect_finset_sum _ _ _

def survivors (A : Finset V) (K : V → V → O → Prop) (xs : List (V × O)) : Finset V :=
  A.filter fun u => All (fun v o => K u v o) xs

theorem expected_survivors_le (owner : V → Law O) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (E A : Finset V) (hAE : A ⊆ E)
    (K : V → V → O → Prop)
    (hpair : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      (owner v).prob (K u v) + (owner u).prob (K v u) ≤ (3 : ℝ) / 2) :
    (marked owner p hp.le hp1 E.toList).expect
      (fun xs => ((survivors A K xs).card : ℝ)) ≤ 8 / p := by
  let a := fun u v => (owner v).prob (K u v)
  let q := fun u v => 1 - a u v
  have h0 (u : V) (hu : u ∈ A) (v : V) (hv : v ∈ A) : 0 ≤ q u v :=
    sub_nonneg.mpr (Law.prob_le_one _ _)
  have h1 (u : V) (hu : u ∈ A) (v : V) (hv : v ∈ A) : q u v ≤ 1 := by
    have := Law.prob_nonneg (owner v) (K u v)
    dsimp [q, a]
    linarith
  have hqp (u : V) (hu : u ∈ A) (v : V) (hv : v ∈ A) (hne : u ≠ v) :
      (1 : ℝ) / 2 ≤ q u v + q v u := by
    have := hpair u hu v hv hne
    dsimp [q, a]
    linarith
  change (marked owner p hp.le hp1 E.toList).expect
    (fun xs => ((A.filter fun u => All (fun v o => K u v o) xs).card : ℝ)) ≤ _
  rw [expected_filter_card]
  calc
    _ ≤ ∑ u ∈ A, ∏ v ∈ A, (1 - p * q u v) := by
      apply Finset.sum_le_sum
      intro u _
      apply (probability_all_subset owner p hp.le hp1 E A hAE (K u)).trans_eq
      apply Finset.prod_congr rfl
      intro v _
      dsimp [q, a]
      ring
    _ ≤ ∑ u ∈ A, ∏ v ∈ A.erase u, (1 - p * q u v) := by
      apply Finset.sum_le_sum
      intro u hu
      rw [← Finset.mul_prod_erase A (fun v => 1 - p * q u v) hu]
      have hprod : 0 ≤ ∏ v ∈ A.erase u, (1 - p * q u v) := by
        apply Finset.prod_nonneg
        intro v hv
        have hvA := Finset.mem_of_mem_erase hv
        nlinarith [h0 u hu v hvA, h1 u hu v hvA]
      apply mul_le_of_le_one_left hprod
      nlinarith [h0 u hu u hu]
    _ ≤ _ := Fractional.product_survival_sum_le A q h0 h1 hqp p hp hp1

end Sampling

end

end StreamingSSSP.Early
