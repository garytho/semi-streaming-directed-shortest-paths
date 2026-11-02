module

public import StreamingReachability.Late.Boundary

@[expose] public section

namespace StreamingReachability.Late

open scoped Classical BigOperators
open Early Implicit

noncomputable section

variable {n : ℕ} {R : Representation n} {G : Graph (Fin n)}
variable {s t : Fin n}

/-- There is at most one followed child per edge occurrence. This models the
disjoint type 1 pieces, including child choices depending on all current bits. -/
def selectedType3Count (Q : Path R G s t)
    (select : Path.PackedEdge R G → Option (Finset (Fin n))) : ℕ :=
  (Q.edges.map fun e => match select e with
    | none => 0
    | some X => if e.2.2.Inside X then 0 else 1).sum

theorem selectedType3Count_le (Q : Path R G s t) (H : Graph (Fin n))
    (S P : Finset (Fin n)) (rho : Fin n → ℝ) (D Rmax : ℝ)
    (select : Path.PackedEdge R G → Option (Finset (Fin n)))
    (hselect : ∀ e ∈ Q.edges, ∀ X, select e = some X →
      AdmissibleChild H S P rho D Rmax Q.vertices X ∧ e.1 ∈ X ∧ e.2.1 ∈ X) :
    selectedType3Count Q select ≤ type3Count Q H S P rho D Rmax := by
  apply List.sum_le_sum
  intro e he
  cases hs : select e with
  | none => simp
  | some X =>
      by_cases hin : e.2.2.Inside X
      · simp [hin]
      · have hc : Type3 H S P rho D Rmax Q.vertices e.2.2 :=
          ⟨X, (hselect e he X hs).1, (hselect e he X hs).2.1,
            (hselect e he X hs).2.2, hin⟩
        simp [hin, hc]

theorem expected_selected_type3 (Q : Path R G s t) (A : ℕ) (hA : 0 < A)
    (S E : Finset (Fin n)) (hS : Q.Inside S) (D : ℝ) (hD : 0 < D)
    (hQ : (Q.searchWeight A : ℝ) ≤ D) (k M N b : ℕ)
    (hk : 0 < k) (hM : 0 < M) (hN : 0 < N) (hgrid : D ≤ N)
    (hin : (searchIn (rounded A (R.restricted G S)) t (searchRadius k M D)).card ≤ b)
    (hout : (searchOut (rounded A (R.restricted G S)) s (searchRadius k M D)).card ≤ b)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (select : List (Fin n × (Fin M × Fin N)) →
      Path.PackedEdge R G → Option (Finset (Fin n)))
    (hselect : Sampling.Holds
      (Sampling.marked (fun _ : Fin n => Law.uniformPair M N hM hN) p hp hp1 E.toList)
      (fun xs => ∀ e ∈ Q.edges, ∀ X, select xs e = some X →
        AdmissibleChild (rounded A (R.restricted G S)) S (Sampling.pivots xs)
          (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
            (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) Q.vertices X ∧
          e.1 ∈ X ∧ e.2.1 ∈ X)) :
    (Sampling.marked (fun _ : Fin n => Law.uniformPair M N hM hN) p hp hp1 E.toList).expect
      (fun xs => (selectedType3Count Q (select xs) : ℝ)) ≤ 48 * b * p / M := by
  have h := Sampling.expect_mono_on _ (Sampling.holds_mono hselect (fun xs hs =>
    show (selectedType3Count Q (select xs) : ℝ) ≤
      (type3Count Q (rounded A (R.restricted G S)) S (Sampling.pivots xs)
        (radiusFor (radius (rounded A (R.restricted G S)) D k M N hk)
          (⟨0, hM⟩, ⟨0, hN⟩) xs) D (searchRadius k M D) : ℝ) from by
      exact_mod_cast selectedType3Count_le Q _ _ _ _ _ _ (select xs) hs))
  exact h.trans (expected_type3 Q A hA S E hS D hD hQ k M N b hk hM hN hgrid
    hin hout p hp hp1)

end

end StreamingReachability.Late
