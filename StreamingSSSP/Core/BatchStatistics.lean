module

public import StreamingSSSP.Core.BatchCorrect
public import StreamingSSSP.Core.IndexedSums
public import StreamingSSSP.Core.SharedResources

@[expose] public section

namespace StreamingSSSP.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

theorem viewed_positive (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (j : Fin nq) :
    ∀ e ∈ (stored ++ input).filterMap (Shared.view c j), 0 < e.weight := by
  apply Shared.viewed_positive
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hs e he
  · exact hp e he

noncomputable def reached (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (j : Fin nq) : Finset (Fin n) :=
  Finset.univ.filter fun v =>
    Global.target (Shared.referenceProblem c j) ((stored ++ input).filterMap (Shared.view c j)) v ≤
      ((c.searches.get j).radius : Distance)

noncomputable def Nrec (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n)) : ℕ :=
  ∑ j : Fin nq, ((reached c stored input j).card +
    ∑ i : Fin nb, (reached c stored input j ∩ c.blocks.get i).card)

noncomputable def reserve (states : States n nb nq) : ℕ :=
  ∑ j : Fin nq, Global.reservationCount (SparseDriver.observe (states.get j))

def recordCount (states : States n nb nq) : ℕ :=
  ∑ j : Fin nq, SparseDriver.distanceRecords (states.get j)

def stateCells (states : States n nb nq) : ℕ :=
  2 + nq + ∑ j : Fin nq, SparseDriver.stateCells (states.get j)

theorem execute_global_invariant (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (j : Fin nq) :
    Global.Invariant (Shared.referenceProblem c j) ((stored ++ input).filterMap (Shared.view c j))
      (SparseDriver.observe ((execute hn c stored input x r).states.get j))
      (min r ((c.searches.get j).radius + 1)) := by
  rw [execute_get hn c stored input x r hx j, SparseDriver.execute_observe]
  exact Global.execute_invariant hn (Shared.referenceProblem c j) _
    (viewed_positive c stored input hs hp j) hA _

theorem execute_shape (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    ∀ j, SparseDriver.Shape ((execute hn c stored input x r).states.get j) := by
  intro j
  rw [execute_get hn c stored input x r hx j]
  exact SparseDriver.execute_shape hn _ stored input _

theorem stateCells_bound (states : States n nb nq)
    (hshape : ∀ j, SparseDriver.Shape (states.get j)) :
    stateCells states ≤ 2 + 13 * recordCount states := by
  have hcount : nq ≤ recordCount states := by
    have hpoint (j : Fin nq) : 1 ≤ SparseDriver.distanceRecords (states.get j) :=
      (Nat.succ_le_of_lt (hshape j).labels_nonempty).trans
        (Nat.le_add_right (states.get j).labels.length (SparseDriver.membershipRecords (states.get j)))
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin nq))) (fun j _ => hpoint j)
    simpa only [recordCount, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Nat.mul_one] using h
  have hcells : (∑ j : Fin nq, SparseDriver.stateCells (states.get j)) ≤ 12 * recordCount states := by
    rw [recordCount, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => SparseDriver.stateCells_bound _ (hshape j))
  unfold stateCells
  omega

theorem execute_space (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x r : ℕ) (hx : ∀ i, (c.blocks.get i).card ≤ x) :
    stateCells (execute hn c stored input x r).states ≤
      2 + 13 * recordCount (execute hn c stored input x r).states :=
  stateCells_bound _ (execute_shape hn c stored input x r hx)

theorem final_settled (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hR : ∀ j, (c.searches.get j).radius ≤ R) (j : Fin nq) :
    ((execute hn c stored input x (R + 1)).states.get j).settled = reached c stored input j := by
  have h := (execute_global_invariant hn c stored input x (R + 1) hs hp hA hx j).1
  rw [Nat.min_eq_right (Nat.add_le_add_right (hR j) 1)] at h
  simp only [SparseDriver.observe] at h
  ext v
  rw [h.settled_iff, distance_lt_succ_iff]
  simp [reached]

theorem final_membership_lengths (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hR : ∀ j, (c.searches.get j).radius ≤ R)
    (j : Fin nq) (i : Fin nb) :
    ((SparseDriver.observe ((execute hn c stored input x (R + 1)).states.get j)).blocks.get i).known.length =
      (reached c stored input j ∩ Shared.block c j i).card := by
  have h := (execute_global_invariant hn c stored input x (R + 1) hs hp hA hx j).2 i
  rw [SparseLabels.length_eq_card _ h.known_unique, h.known_support]
  simp only [SparseDriver.observe, Shared.referenceProblem, Vector.get_ofFn]
  rw [final_settled hn c stored input x R hs hp hA hx hR j]

theorem final_record_bound (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hR : ∀ j, (c.searches.get j).radius ≤ R) :
    recordCount (execute hn c stored input x (R + 1)).states ≤ Nrec c stored input := by
  unfold recordCount Nrec
  apply Finset.sum_le_sum
  intro j _
  let state := (execute hn c stored input x (R + 1)).states.get j
  have hg := (execute_global_invariant hn c stored input x (R + 1) hs hp hA hx j).1
  rw [Nat.min_eq_right (Nat.add_le_add_right (hR j) 1)] at hg
  have hsource : (c.searches.get j).source ∈ state.settled := by
    apply (hg.settled_iff _).mpr
    simp [Global.target, Shared.referenceProblem]
  have hlabels : state.labels.length = (reached c stored input j).card := by
    have hu : (state.labels.map Prod.fst).Nodup := hg.label_unique
    have hsupp : SparseLabels.support state.labels = state.settled ∪ {(c.searches.get j).source} :=
      hg.label_support
    rw [SparseLabels.length_eq_card _ hu, hsupp]
    have he : state.settled ∪ {(c.searches.get j).source} = state.settled := by
      simp [Finset.insert_eq_of_mem hsource, hsource]
    rw [he]
    exact congrArg Finset.card (final_settled hn c stored input x R hs hp hA hx hR j)
  have hshape := execute_shape hn c stored input x (R + 1) hx j
  have hm := RecordMap.sum_values_le Global.emptyBlock state.cache hshape.unique
    (fun bs => bs.known.length)
  have hknown : (∑ i : Fin nb, (RecordMap.get Global.emptyBlock state.cache i).known.length) =
      ∑ i : Fin nb, (reached c stored input j ∩ Shared.block c j i).card := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [SparseDriver.observe, Vector.get_ofFn] using
      final_membership_lengths hn c stored input x R hs hp hA hx hR j i
  change state.labels.length + SparseDriver.membershipRecords state ≤ _
  rw [hlabels]
  apply Nat.add_le_add_left
  apply (hm.trans_eq hknown).trans
  exact Finset.sum_le_sum (fun i _ => Finset.card_le_card
    (Finset.inter_subset_inter (Finset.Subset.refl _ : reached c stored input j ⊆ _)
      Finset.inter_subset_left))

theorem final_reservation_bound (hn : 0 < n) (c : Shared.Catalog n nb ns nq)
    (stored input : List (Edge n)) (x R : ℕ)
    (hs : ∀ e ∈ stored, 0 < e.weight) (hp : ∀ e ∈ input, 0 < e.weight) (hA : 0 < c.scale)
    (hx : ∀ i, (c.blocks.get i).card ≤ x) (hR : ∀ j, (c.searches.get j).radius ≤ R) :
    reserve (execute hn c stored input x (R + 1)).states ≤ 8 * x * Nrec c stored input := by
  unfold reserve Nrec
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have he := execute_get hn c stored input x (R + 1) hx j
  rw [Nat.min_eq_right (Nat.add_le_add_right (hR j) 1)] at he
  rw [he, SparseDriver.execute_observe]
  have hc := Global.execute_reservation_charge hn (Shared.referenceProblem c j)
    ((stored ++ input).filterMap (Shared.view c j)) (viewed_positive c stored input hs hp j)
    hA x ((c.searches.get j).radius + 1)
    (fun i => by
      simpa only [Shared.referenceProblem, Vector.get_ofFn] using
        (Shared.block_card_le c j i).trans (hx i))
  apply hc.trans
  apply Nat.mul_le_mul_left (8 * x)
  unfold Global.membershipRecords
  have hm : (∑ i : Fin nb,
      ((Global.execute hn (Shared.referenceProblem c j) ((stored ++ input).filterMap (Shared.view c j))
        ((c.searches.get j).radius + 1)).blocks.get i).known.length) =
      ∑ i : Fin nb, (reached c stored input j ∩ Shared.block c j i).card := by
    apply Finset.sum_congr rfl
    intro i _
    have hlen := final_membership_lengths hn c stored input x R hs hp hA hx hR j i
    rwa [he, SparseDriver.execute_observe] at hlen
  rw [hm]
  apply (Finset.sum_le_sum (fun i _ => Finset.card_le_card
    (Finset.inter_subset_inter (Finset.Subset.refl _ : reached c stored input j ⊆ _)
      Finset.inter_subset_left))).trans
  exact Nat.le_add_left _ _

end StreamingSSSP.Core.BatchDriver
