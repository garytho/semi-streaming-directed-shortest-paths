module

public import StreamingSSSP.Hopset.ReplyDensity

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open scoped Classical

variable {n ns : ℕ}

def signatureVolume (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) : ℕ :=
  ∑ i : Fin ns, ∑ v ∈ sets.get i, (labels cfg r pivots reply i v).length

theorem flag_count (reply : Core.BatchAPI.SparseReply n) (query numerator denominator : ℕ) (S : Finset (Fin n)) :
    (∑ v ∈ S, if withinFraction (lookup reply query v) numerator denominator = true then (1 : ℕ) else 0) ≤
      (hits reply query).card := by
  rw [← Finset.card_filter]
  apply Finset.card_le_card
  intro v hv
  exact flag_hits reply query numerator denominator v (Finset.mem_filter.mp hv).2

theorem labels_cons_length (cfg : Config) (r : ℕ) (p : Pivot n ns) (pivots : List (Pivot n ns))
    (reply : Core.BatchAPI.SparseReply n) (i : Fin ns) (v : Fin n) :
    (labels cfg r (p :: pivots) reply i v).length =
      (if p.setId = i then
        (if inFlag cfg r p reply v = true then 1 else 0) +
          (if outFlag cfg r p reply v = true then 1 else 0)
        else 0) + (labels cfg r pivots reply i v).length := by
  by_cases hi : p.setId = i <;> cases hin : inFlag cfg r p reply v <;> cases hout : outFlag cfg r p reply v <;>
    simp [labels, hi, hin, hout, Nat.add_comm, Nat.add_assoc] <;> omega

theorem pivot_signature_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (p : Pivot n ns) (reply : Core.BatchAPI.SparseReply n) :
    (∑ i : Fin ns, ∑ v ∈ sets.get i, if p.setId = i then
      (if inFlag cfg r p reply v = true then (1 : ℕ) else 0) +
        (if outFlag cfg r p reply v = true then 1 else 0)
      else 0) ≤ (hits reply p.forward).card + (hits reply p.backward).card := by
  have he : (∑ i : Fin ns, ∑ v ∈ sets.get i, if p.setId = i then
      (if inFlag cfg r p reply v = true then (1 : ℕ) else 0) +
        (if outFlag cfg r p reply v = true then 1 else 0)
      else 0) =
      ∑ v ∈ sets.get p.setId,
        ((if inFlag cfg r p reply v = true then (1 : ℕ) else 0) +
          (if outFlag cfg r p reply v = true then 1 else 0)) := by
    rw [Finset.sum_eq_single p.setId]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  rw [he, Finset.sum_add_distrib]
  have hin := flag_count reply p.backward
    ((p.eta * cfg.shifts + p.shift) * cfg.initialNumerator) (cfg.shifts * cfg.denominatorAt r) (sets.get p.setId)
  have hout := flag_count reply p.forward
    ((p.eta * cfg.shifts + p.shift) * cfg.initialNumerator) (cfg.shifts * cfg.denominatorAt r) (sets.get p.setId)
  change _ ≤ _ at hin hout
  exact (Nat.add_le_add hin hout).trans_eq (Nat.add_comm _ _)

theorem signatures_queries_count (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n) :
    signatureVolume cfg r sets pivots reply ≤ ((pivotIds pivots).map (fun query => (hits reply query).card)).sum := by
  induction pivots with
  | nil => simp [signatureVolume, labels, pivotIds]
  | cons p pivots ih =>
      have hhead := pivot_signature_count cfg r sets p reply
      unfold signatureVolume at *
      simp only [labels_cons_length, Finset.sum_add_distrib]
      have h := Nat.add_le_add hhead ih
      simpa only [pivotIds, List.flatMap_cons, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero] using h

/-- All materialized signature keys together are paid for by actual sparse
distance records, including records charged before an execution is aborted. -/
theorem signatures_record_density (cfg : Config) (r : ℕ) (sets : Vector (Finset (Fin n)) ns)
    (pivots : List (Pivot n ns)) (reply : Core.BatchAPI.SparseReply n)
    (h : (pivotIds pivots).Nodup) : signatureVolume cfg r sets pivots reply ≤ reply.length :=
  (signatures_queries_count cfg r sets pivots reply).trans (distinct_hits_count reply _ h)

end StreamingSSSP.Hopset.Measured
