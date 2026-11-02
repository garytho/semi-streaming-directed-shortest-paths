module

public import StreamingReachability.Core.Rounding

@[expose] public section

namespace StreamingReachability.Core.BlockSearch

open StoredEdges

variable {n : ℕ}

structure Outcome (n : ℕ) where
  vertices : Finset (Fin n)
  records : List (Fin n × Distance)
  nextNumerator : Distance
  lastThreshold : ℕ
  scans : ℕ
  reservations : ℕ

def finish (B known : Finset (Fin n)) (r τ : ℕ) (f : DistanceArray n) : Outcome n :=
  let U := found B known f.get r
  { vertices := U
    records := (U.sort (· ≤ ·)).map fun v => (v, f.get v)
    nextNumerator := nextDistance B (known ∪ U) f.get
    lastThreshold := τ
    scans := 1
    reservations := B.card * τ }

def searchAux (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) :
    ℕ → ℕ → Option (Outcome n)
  | 0, _ => none
  | fuel + 1, τ =>
      let f := labels hn B known τ initial edges
      if (found B known f.get r).card < τ then some (finish B known r τ f)
      else (searchAux hn B known r initial edges fuel (2 * τ)).map fun out =>
        { out with scans := out.scans + 1
                   reservations := out.reservations + B.card * τ }

def search (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) : Option (Outcome n) :=
  searchAux hn B known r initial edges (Nat.log 2 B.card + 2) 1

theorem found_card_le (B known : Finset (Fin n)) (f : Fin n → Distance) (r : ℕ) :
    (found B known f r).card ≤ B.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem searchAux_terminates (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) (fuel τ : ℕ)
    (hbound : B.card < τ * 2 ^ fuel) :
    ∃ out, searchAux hn B known r initial edges (fuel + 1) τ = some out := by
  induction fuel generalizing τ with
  | zero =>
      have hsmall : (found B known (labels hn B known τ initial edges).get r).card < τ :=
        (found_card_le B known _ r).trans_lt (by simpa using hbound)
      exact ⟨finish B known r τ (labels hn B known τ initial edges),
        by rw [searchAux, ite_eq_left hsmall]⟩
  | succ fuel ih =>
      by_cases hsmall : (found B known (labels hn B known τ initial edges).get r).card < τ
      · exact ⟨finish B known r τ (labels hn B known τ initial edges),
          by rw [searchAux, ite_eq_left hsmall]⟩
      · have hb : B.card < (2 * τ) * 2 ^ fuel := by
          simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbound
        obtain ⟨out, hout⟩ := ih (2 * τ) hb
        refine ⟨{ out with scans := out.scans + 1
                           reservations := out.reservations + B.card * τ }, ?_⟩
        rw [searchAux, ite_eq_right hsmall, hout]
        rfl

theorem search_terminates (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) :
    ∃ out, search hn B known r initial edges = some out := by
  simpa only [search, Nat.add_assoc] using
    searchAux_terminates hn B known r initial edges (Nat.log 2 B.card + 1) 1
      (by simpa using Nat.lt_pow_succ_log_self (by decide : 1 < 2) B.card)

theorem searchAux_exact (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) (seed : Fin n → Distance)
    (hseed : ∀ u, u ∉ known → seed u = ⊤)
    (hinit : ∀ u, initial.get u =
      if u ∈ known then multiDist (blockGraph edges B) seed u else ⊤)
    (fuel τ : ℕ) {out : Outcome n}
    (hout : searchAux hn B known r initial edges fuel τ = some out) :
    out.vertices = found B known (multiDist (blockGraph edges B) seed) r ∧
      out.records = (out.vertices.sort (· ≤ ·)).map
        (fun v => (v, multiDist (blockGraph edges B) seed v)) ∧
      out.nextNumerator =
        nextDistance B (known ∪ out.vertices) (multiDist (blockGraph edges B) seed) := by
  induction fuel generalizing τ out with
  | zero => simp [searchAux] at hout
  | succ fuel ih =>
      simp only [searchAux] at hout
      split_ifs at hout with hs
      · have heq := Option.some.inj hout
        subst out
        obtain ⟨hU, hv, he⟩ := search_certificate hn B known τ r seed initial edges
          hseed hinit hs
        refine ⟨hU, ?_, he⟩
        apply List.map_congr_left
        intro v hvU
        exact congrArg (Prod.mk v) (hv v ((Finset.mem_sort _).mp hvU))
      · obtain ⟨out', ho', heq⟩ := Option.map_eq_some_iff.mp hout
        subst out
        exact ih (2 * τ) (out := out') ho'

theorem searchAux_accounting (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) (fuel τ : ℕ)
    {out : Outcome n} (hout : searchAux hn B known r initial edges fuel τ = some out) :
    τ ≤ out.lastThreshold ∧ out.scans ≤ fuel ∧
      out.reservations + B.card * τ = 2 * B.card * out.lastThreshold := by
  induction fuel generalizing τ out with
  | zero => simp [searchAux] at hout
  | succ fuel ih =>
      simp only [searchAux] at hout
      split_ifs at hout with hs
      · have he := Option.some.inj hout
        subst out
        dsimp only [finish]
        exact ⟨le_rfl, Nat.succ_le_succ (Nat.zero_le _), by ring⟩
      · obtain ⟨out', ho', heq⟩ := Option.map_eq_some_iff.mp hout
        subst out
        obtain ⟨hτ, hsc, hr⟩ := ih (2 * τ) ho'
        dsimp only
        refine ⟨(by omega), (by omega), ?_⟩
        nlinarith only [hr]

theorem searchAux_threshold (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) (seed : Fin n → Distance)
    (hinit : ∀ u, multiDist (blockGraph edges B) seed u ≤ initial.get u)
    (fuel τ K : ℕ) (hτ : τ ≤ K)
    (hK : 2 * (found B known (multiDist (blockGraph edges B) seed) r).card ≤ K)
    {out : Outcome n} (hout : searchAux hn B known r initial edges fuel τ = some out) :
    out.lastThreshold ≤ K := by
  induction fuel generalizing τ out with
  | zero => simp [searchAux] at hout
  | succ fuel ih =>
      simp only [searchAux] at hout
      split_ifs at hout with hs
      · have he := Option.some.inj hout
        subst out
        exact hτ
      · obtain ⟨out', ho', heq⟩ := Option.map_eq_some_iff.mp hout
        subst out
        have hsub := found_subset B known (multiDist (blockGraph edges B) seed)
          (labels hn B known τ initial edges).get r
          (fun v _ => actual_lower hn B known τ seed initial edges hinit v)
        have hc := Finset.card_le_card hsub
        have hτ' : 2 * τ ≤ K := by omega
        exact ih (2 * τ) hτ' (out := out') ho'

theorem search_correct_and_cost (hn : 0 < n) (B known : Finset (Fin n)) (r : ℕ)
    (initial : DistanceArray n) (edges : List (Edge n)) (seed : Fin n → Distance)
    (hseed : ∀ u, u ∉ known → seed u = ⊤)
    (hinit : ∀ u, initial.get u =
      if u ∈ known then multiDist (blockGraph edges B) seed u else ⊤) :
    ∃ out, search hn B known r initial edges = some out ∧
      out.vertices = found B known (multiDist (blockGraph edges B) seed) r ∧
      out.records = (out.vertices.sort (· ≤ ·)).map
        (fun v => (v, multiDist (blockGraph edges B) seed v)) ∧
      out.nextNumerator =
        nextDistance B (known ∪ out.vertices) (multiDist (blockGraph edges B) seed) ∧
      out.scans ≤ Nat.log 2 B.card + 2 ∧
      out.reservations ≤ 4 * B.card * (out.vertices.card + 1) ∧
      out.lastThreshold ≤ max 1 (2 * out.vertices.card) := by
  obtain ⟨out, hout⟩ := search_terminates hn B known r initial edges
  obtain ⟨hU, hrec, hnext⟩ := searchAux_exact hn B known r initial edges seed
    hseed hinit _ _ hout
  obtain ⟨_, hsc, hres⟩ := searchAux_accounting hn B known r initial edges _ _ hout
  have hlo : ∀ u, multiDist (blockGraph edges B) seed u ≤ initial.get u := by
    intro u
    rw [hinit]
    split_ifs
    · exact le_rfl
    · exact le_top
  have hτ := searchAux_threshold hn B known r initial edges seed hlo _ _
    (max 1 (2 * out.vertices.card)) (le_max_left _ _)
    (by simpa only [hU] using le_max_right 1 (2 * out.vertices.card)) hout
  refine ⟨out, hout, hU, hrec, hnext, hsc, ?_, hτ⟩
  have hτ' : out.lastThreshold ≤ 2 * (out.vertices.card + 1) := by omega
  nlinarith only [hres, Nat.mul_le_mul_left (2 * B.card) hτ']

end StreamingReachability.Core.BlockSearch
