module

public import StreamingSSSP.Hopset.PrimitiveResources

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ} {A : Type*}

theorem Certificate.strengthen (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (program : Code n A)
    (draws calls : ℕ) (P T : A → Prop)
    (hc : Certificate input Q word program draws calls P) (ht : program.Ensures T) :
    Certificate input Q word program draws calls T := by
  induction program generalizing draws calls with
  | pure value => exact ht
  | abort => trivial
  | uniform bound positive next ih => exact ⟨hc.1, hc.2.1, fun i => ih i _ _ (hc.2.2 i) (ht i)⟩
  | batch request allowance next ih => exact ⟨hc.1, hc.2.1, ih _ _ _ hc.2.2 (ht _)⟩

theorem draw_rate_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (p : Rate) (hp : p.denominator ≤ word) :
    Certificate input Q word (Code.drawRate p) 1 0 (fun _ => True) :=
  ⟨by decide, hp, fun _ => trivial⟩

theorem draw_pair_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (hwm : m ≤ word) (hwd : d ≤ word) :
    Certificate input Q word (Code.drawPair m d hm hd) 2 0 (fun _ => True) :=
  ⟨by decide, hwm, fun _ => ⟨by decide, hwd, fun _ => trivial⟩⟩

theorem first_rank_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (rates : List Rate)
    (hr : ∀ p ∈ rates, p.denominator ≤ word) :
    Certificate input Q word (Code.firstRank rates) rates.length 0 (fun _ => True) := by
  induction rates with
  | nil => trivial
  | cons p rates ih =>
      have ht := ih (by intro rate hm; exact hr rate (List.mem_cons_of_mem p hm))
      have hd := draw_rate_certificate input Q word p (hr p (by simp))
      let resume : Bool → Code n ℕ :=
        fun hit => if hit then .pure 0 else (Code.firstRank rates).map Nat.succ
      have hn : ∀ hit, True → Certificate input Q word (resume hit) rates.length 0 (fun _ => True) := by
        intro hit _
        cases hit with
        | false =>
            simp only [resume, Bool.false_eq_true, ↓reduceIte]
            exact ht.map input Q word _ Nat.succ _ _ (fun _ => True) (fun _ => True) (fun _ _ => trivial)
        | true => trivial
      have h := hd.bind input Q word (Code.drawRate p) resume 1 0 rates.length 0
        (fun _ => True) (fun _ => True) hn
      simpa only [Code.firstRank, resume, List.length_cons, Nat.add_comm, Nat.add_zero] using h

theorem rank_vector_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (rates : List Rate)
    (hr : ∀ p ∈ rates, p.denominator ≤ word) (m : ℕ) :
    Certificate input Q word (Code.rankVector rates m) (m * rates.length) 0 (fun _ => True) := by
  induction m with
  | zero => trivial
  | succ m ih =>
      have hf := first_rank_certificate input Q word rates hr
      have h := hf.bind input Q word (Code.firstRank rates) _ rates.length 0 (m * rates.length) 0
        (fun _ => True) (fun _ => True) (fun r _ =>
          ih.map input Q word _ (fun tail => Vector.ofFn (Fin.cases r (fun i => tail.get i)))
            _ _ (fun _ => True) (fun _ => True) (fun _ _ => trivial))
      have he : rates.length + m * rates.length = (m + 1) * rates.length := by ring
      simpa only [Code.rankVector, Nat.add_zero, he] using h

theorem subset_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (p : Rate) (vertices : List (Fin n))
    (hp : p.denominator ≤ word) :
    Certificate input Q word (Code.subset p vertices) vertices.length 0 (fun _ => True) := by
  induction vertices with
  | nil => trivial
  | cons v vertices ih =>
      have hf := draw_rate_certificate input Q word p hp
      let resume : Bool → Code n (Finset (Fin n)) :=
        fun hit => if hit then (Code.subset p vertices).map (insert v) else Code.subset p vertices
      have hn : ∀ hit, True → Certificate input Q word (resume hit) vertices.length 0 (fun _ => True) := by
        intro hit _
        cases hit with
        | false => simpa only [resume, Bool.false_eq_true, ↓reduceIte] using ih
        | true =>
            exact ih.map input Q word _ (insert v) _ _ (fun _ => True) (fun _ => True) (fun _ _ => trivial)
      have h := hf.bind input Q word (Code.drawRate p) resume 1 0 vertices.length 0
        (fun _ => True) (fun _ => True) hn
      simpa only [Code.subset, resume, List.length_cons, Nat.add_comm, Nat.add_zero] using h

theorem pivot_loop_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) (targets : List (Target n ns)) (offset : ℕ) :
    (pivotLoop cfg r sets reply targets offset).Ensures (fun pivots => pivots.length ≤ targets.length) := by
  induction targets generalizing offset with
  | nil => simp [pivotLoop, Code.Ensures]
  | cons target targets ih =>
      unfold pivotLoop
      split
      · apply Code.ensures_bind _ _ (fun _ => True) _ (Code.ensures_true _)
        intro owner _
        apply Code.ensures_map
        apply Code.ensures_mono _ _ _ (ih (offset + 1))
        intro pivots hp
        simpa only [List.length_cons] using Nat.add_le_add_right hp 1
      · exact Code.ensures_mono _ _ _ (ih (offset + 1)) (fun pivots hp => hp.trans (by simp))

theorem pivot_loop_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (cfg : Config) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (reply : Core.BatchAPI.SparseReply n)
    (targets : List (Target n ns)) (offset : ℕ)
    (hg : cfg.groups ≤ word) (hs : cfg.shifts ≤ word) :
    Certificate input Q word (pivotLoop cfg r sets reply targets offset) (2 * targets.length) 0
      (fun pivots => pivots.length ≤ targets.length) := by
  have hc : Certificate input Q word (pivotLoop cfg r sets reply targets offset) (2 * targets.length) 0
      (fun _ => True) := by
    induction targets generalizing offset with
    | nil => trivial
    | cons target targets ih =>
        unfold pivotLoop
        split
        · have hd := draw_pair_certificate input Q word _ _ cfg.groups_pos cfg.shifts_pos hg hs
          let make : Fin cfg.groups × Fin cfg.shifts → Pivot n ns := fun owner =>
            ⟨target.setId, target.vertex,
              chooseEta cfg r (sets.get target.setId) reply (2 * offset) (2 * offset + 1) owner.1 owner.2,
              owner.2.val, 2 * offset, 2 * offset + 1⟩
          let resume : Fin cfg.groups × Fin cfg.shifts → Code n (List (Pivot n ns)) := fun owner =>
            (pivotLoop cfg r sets reply targets (offset + 1)).map (make owner :: ·)
          have hn : ∀ owner, True → Certificate input Q word (resume owner) (2 * targets.length) 0
              (fun _ => True) := fun owner _ =>
            (ih (offset + 1)).map input Q word _ (make owner :: ·) _ _
              (fun _ => True) (fun _ => True) (fun _ _ => trivial)
          have h := hd.bind input Q word _ resume 2 0 (2 * targets.length) 0
            (fun _ => True) (fun _ => True) hn
          have he : 2 + 2 * targets.length = 2 * (target :: targets).length := by
            change 2 + 2 * targets.length = 2 * (targets.length + 1)
            ring
          simpa only [resume, make, he, Nat.add_zero] using h
        · exact (ih (offset + 1)).weaken input Q word _ _ _ _ _ (fun _ => True)
            (by change 2 * targets.length ≤ 2 * (targets.length + 1); omega) (by omega)
  exact hc.strengthen input Q word _ _ _ (fun _ => True) _ (pivot_loop_count cfg r sets reply targets offset)

def indexVolume (sets : Vector (Finset (Fin n)) ns) (indices : List (Fin ns)) : ℕ :=
  (indices.map (fun i => (sets.get i).card)).sum

theorem index_volume_all (sets : Vector (Finset (Fin n)) ns) :
    indexVolume sets (List.finRange ns) = setVolume sets := by
  rw [indexVolume, ← List.ofFn_eq_map, List.sum_ofFn, vector_volume]

theorem late_targets_certificate (input : List (StoredEdges.Edge n))
    (Q : Core.BatchAPI.Request n → ℕ → Prop) (word : ℕ) (cfg : Config) (hn : 0 < n) (r : ℕ)
    (sets : Vector (Finset (Fin n)) ns) (indices : List (Fin ns)) (hword : n ≤ word) :
    Certificate input Q word (lateTargetLoop cfg hn r sets indices) (indexVolume sets indices) 0
      (fun targets => targets.length ≤ indexVolume sets indices) := by
  induction indices with
  | nil => simp [lateTargetLoop, Certificate, indexVolume]
  | cons i indices ih =>
      have hchosen : Certificate input Q word
          (if r < cfg.maximumLevel then Code.subset (PivotProfile.rate n hn cfg.k cfg.logarithm r) (members (sets.get i))
            else Code.pure (sets.get i))
          (sets.get i).card 0 (fun P => P ⊆ sets.get i) := by
        split
        · have h := subset_certificate input Q word (PivotProfile.rate n hn cfg.k cfg.logarithm r)
            (members (sets.get i)) hword
          rw [members_count] at h
          exact h.strengthen input Q word _ _ _ (fun _ => True) _ (subset_of_members _ _)
        · exact Finset.Subset.refl _
      let resume : Finset (Fin n) → Code n (List (Target n ns)) := fun P =>
        (lateTargetLoop cfg hn r sets indices).map fun rest =>
          ((members P).map fun v => ⟨i, v, .pivot⟩) ++ rest
      have hnext : ∀ P, P ⊆ sets.get i → Certificate input Q word (resume P) (indexVolume sets indices) 0
          (fun targets => targets.length ≤ indexVolume sets (i :: indices)) := by
        intro P hP
        apply ih.map input Q word _ _ _ _ _ _
        intro targets ht
        simp only [List.length_append, List.length_map, members_count, indexVolume, List.map_cons, List.sum_cons]
        exact Nat.add_le_add (Finset.card_le_card hP) ht
      have h := hchosen.bind input Q word _ resume (sets.get i).card 0 (indexVolume sets indices) 0
        (fun P => P ⊆ sets.get i) (fun targets => targets.length ≤ indexVolume sets (i :: indices)) hnext
      simpa only [lateTargetLoop, resume, indexVolume, List.map_cons, List.sum_cons, Nat.add_zero] using h

end StreamingSSSP.Hopset.Measured
