module

public import StreamingSSSP.Core.BatchSearch

@[expose] public section

namespace StreamingSSSP.Core.BatchSearch

open StoredEdges

variable {n : ℕ}

def double (q : Query n) : Query n :=
  { q with request := { q.request with threshold := 2 * q.request.threshold } }

def completed (stages : List (Query n × Stage n)) : List (Query n × BlockSearch.Outcome n) :=
  stages.filterMap fun (q, s) =>
    match s with
    | .returned out => some (q, out)
    | .retry => none

def retryJobs (stages : List (Query n × Stage n)) : List (Query n) :=
  stages.filterMap fun (q, s) =>
    match s with
    | .returned _ => none
    | .retry => some (double q)

structure Batch (n : ℕ) where
  answers : List (Query n × BlockSearch.Outcome n)
  unfinished : List (Query n)
  scans : ℕ
  phases : ℕ
  reservations : ℕ
  peakRows : ℕ

def runPhases (hn : 0 < n) (input : List (Edge n)) : ℕ → List (Query n) → Batch n
  | 0, jobs => ⟨[], jobs, 0, 0, 0, 0⟩
  | fuel + 1, jobs =>
      if jobs.isEmpty then ⟨[], [], 0, 0, 0, 0⟩
      else
        let phase := runPhase hn input jobs
        let tail := runPhases hn input fuel (retryJobs phase.stages)
        ⟨completed phase.stages ++ tail.answers, tail.unfinished,
          phase.scans + tail.scans, 1 + tail.phases,
          Packing.load capacity jobs + tail.reservations,
          max phase.peakRows tail.peakRows⟩

def localCost (hn : 0 < n) (input : List (Edge n)) : ℕ → Query n → ℕ
  | 0, _ => 0
  | fuel + 1, q =>
      capacity q +
        match (semanticStage hn input q).2 with
        | .returned _ => 0
        | .retry => localCost hn input fuel (double q)

theorem localCost_step (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (jobs : List (Query n)) :
    (jobs.map (localCost hn input (fuel + 1))).sum =
      Packing.load capacity jobs +
        ((retryJobs (jobs.map (semanticStage hn input))).map (localCost hn input fuel)).sum := by
  induction jobs with
  | nil => simp [Packing.load, retryJobs]
  | cons q qs ih =>
      cases hs : (semanticStage hn input q).2 with
      | returned out =>
          simp only [localCost, hs, Nat.add_zero, List.map_cons, List.sum_cons,
            Packing.load, retryJobs, List.filterMap_cons] at ih ⊢
          omega
      | retry =>
          simp only [localCost, hs, List.map_cons, List.sum_cons, Packing.load,
            retryJobs, List.filterMap_cons] at ih ⊢
          rw [show (semanticStage hn input q).1 = q from rfl]
          omega

theorem retryJobs_reverse (stages : List (Query n × Stage n)) :
    retryJobs stages.reverse = (retryJobs stages).reverse := by
  simp only [retryJobs, List.filterMap_reverse]

theorem runPhases_reservations (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (jobs : List (Query n)) :
    (runPhases hn input fuel jobs).reservations =
      (jobs.map (localCost hn input fuel)).sum := by
  induction fuel generalizing jobs with
  | zero => simp [runPhases, localCost]
  | succ fuel ih =>
      by_cases hj : jobs.isEmpty = true
      · have he := List.isEmpty_iff.mp hj
        subst jobs
        simp [runPhases]
      · rw [runPhases, ite_eq_right hj]
        dsimp only
        rw [ih, runPhase_correct, List.map_reverse, retryJobs_reverse, List.map_reverse,
          List.sum_reverse, localCost_step]

theorem runPhases_cost (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (jobs : List (Query n)) :
    (runPhases hn input fuel jobs).phases ≤ fuel ∧
      n * (runPhases hn input fuel jobs).scans ≤
        n * (runPhases hn input fuel jobs).phases +
          2 * (runPhases hn input fuel jobs).reservations := by
  induction fuel generalizing jobs with
  | zero => simp [runPhases]
  | succ fuel ih =>
      by_cases hj : jobs.isEmpty = true
      · simp [runPhases, hj]
      · rw [runPhases, ite_eq_right hj]
        dsimp only
        obtain ⟨hph, hcost⟩ := ih (retryJobs (runPhase hn input jobs).stages)
        have hscan := runPhase_scan_bound hn input jobs
        constructor
        · omega
        · simp only [Nat.mul_add]
          omega

theorem retry_mem (hn : 0 < n) (input : List (Edge n)) (jobs : List (Query n))
    {q : Query n} (hq : q ∈ retryJobs (runPhase hn input jobs).stages) :
    ∃ old ∈ jobs, q = double old ∧
      (found old.request.block old.request.known
        (BlockSearch.labels hn old.request.block old.request.known old.request.threshold
          (SparseLabels.vector old.sources) input).get old.radiusNumerator).card ≥
          old.request.threshold := by
  rw [runPhase_correct] at hq
  obtain ⟨p, hp, hs⟩ := List.mem_filterMap.mp hq
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hp
  have ho : old ∈ jobs := List.mem_reverse.mp hold
  by_cases hsmall : (found old.request.block old.request.known
      (BlockSearch.labels hn old.request.block old.request.known old.request.threshold
        (SparseLabels.vector old.sources) input).get old.radiusNumerator).card <
      old.request.threshold
  · simp [semanticStage, evaluate, hsmall] at hs
  · have heq : double old = q := by simpa [semanticStage, evaluate, hsmall] using hs
    exact ⟨old, ho, heq.symm, by omega⟩

def WorkspaceReady (x : ℕ) (q : Query n) : Prop :=
  0 < q.request.block.card ∧ q.request.block.card ≤ x ∧
    0 < q.request.threshold ∧ q.request.threshold ≤ 2 * x

theorem retry_ready (hn : 0 < n) (input : List (Edge n)) (x : ℕ)
    (jobs : List (Query n)) (hj : ∀ q ∈ jobs, WorkspaceReady x q) :
    ∀ q ∈ retryJobs (runPhase hn input jobs).stages, WorkspaceReady x q := by
  intro q hq
  obtain ⟨old, ho, rfl, hfail⟩ := retry_mem hn input jobs hq
  obtain ⟨hb0, hbx, ht0, _⟩ := hj old ho
  have hcard := BlockSearch.found_card_le old.request.block old.request.known
    (BlockSearch.labels hn old.request.block old.request.known old.request.threshold
      (SparseLabels.vector old.sources) input).get old.radiusNumerator
  exact ⟨hb0, hbx, by dsimp [double]; omega, by dsimp [double]; omega⟩

theorem runPhases_memory (hn : 0 < n) (input : List (Edge n)) (x fuel : ℕ)
    (jobs : List (Query n)) (hj : ∀ q ∈ jobs, WorkspaceReady x q)
    (hspace : 2 * x * x ≤ n) :
    (runPhases hn input fuel jobs).peakRows ≤ 8 * n := by
  induction fuel generalizing jobs with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
      by_cases he : jobs.isEmpty = true
      · simp [runPhases, he]
      · rw [runPhases, ite_eq_right he]
        apply max_le
        · apply runPhase_memory hn input jobs
          · intro q hq
            exact ⟨(hj q hq).1, (hj q hq).2.2.1⟩
          · intro q hq
            have h := hj q hq
            have hc := Nat.mul_le_mul h.2.1 h.2.2.2
            unfold capacity BatchSkeleton.capacity
            nlinarith only [hc, hspace]
        · exact ih _ (retry_ready hn input x jobs hj)

theorem runPhases_finished (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (jobs : List (Query n))
    (hj : ∀ q ∈ jobs, q.request.block.card < q.request.threshold * 2 ^ fuel) :
    (runPhases hn input (fuel + 1) jobs).unfinished = [] := by
  induction fuel generalizing jobs with
  | zero =>
      by_cases he : jobs.isEmpty = true
      · simp [runPhases, he]
      · rw [runPhases, ite_eq_right he]
        dsimp only
        have hr : retryJobs (runPhase hn input jobs).stages = [] := by
          apply List.eq_nil_iff_forall_not_mem.mpr
          intro q hq
          obtain ⟨old, ho, _, hf⟩ := retry_mem hn input jobs hq
          have hb := hj old ho
          have hc := BlockSearch.found_card_le old.request.block old.request.known
            (BlockSearch.labels hn old.request.block old.request.known old.request.threshold
              (SparseLabels.vector old.sources) input).get old.radiusNumerator
          simp only [pow_zero, Nat.mul_one] at hb
          omega
        rw [hr]
        rfl
  | succ fuel ih =>
      by_cases he : jobs.isEmpty = true
      · simp [runPhases, he]
      · rw [runPhases, ite_eq_right he]
        dsimp only
        apply ih
        intro q hq
        obtain ⟨old, ho, rfl, _⟩ := retry_mem hn input jobs hq
        have hb := hj old ho
        simpa only [double, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb

def run (hn : 0 < n) (input : List (Edge n)) (x : ℕ) (jobs : List (Query n)) : Batch n :=
  runPhases hn input (Nat.log 2 x + 2) jobs

theorem run_finished (hn : 0 < n) (input : List (Edge n)) (x : ℕ)
    (jobs : List (Query n)) (hj : ∀ q ∈ jobs, q.request.block.card ≤ x ∧ q.request.threshold = 1) :
    (run hn input x jobs).unfinished = [] := by
  apply runPhases_finished hn input (Nat.log 2 x + 1) jobs
  intro q hq
  obtain ⟨hb, ht⟩ := hj q hq
  rw [ht, Nat.one_mul]
  exact hb.trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) x)

theorem localCost_eq_reservations (hn : 0 < n) (input : List (Edge n)) (fuel : ℕ)
    (q : Query n) {out : BlockSearch.Outcome n}
    (hout : BlockSearch.searchAux hn q.request.block q.request.known q.radiusNumerator
      (SparseLabels.vector q.sources) input fuel q.request.threshold = some out) :
    localCost hn input fuel q = out.reservations := by
  induction fuel generalizing q out with
  | zero => simp [BlockSearch.searchAux] at hout
  | succ fuel ih =>
      rw [BlockSearch.searchAux] at hout
      by_cases hs : (found q.request.block q.request.known
          (BlockSearch.labels hn q.request.block q.request.known q.request.threshold
            (SparseLabels.vector q.sources) input).get q.radiusNumerator).card < q.request.threshold
      · rw [ite_eq_left hs] at hout
        have he := Option.some.inj hout
        subst out
        simp only [localCost, semanticStage, evaluate, hs, ↓reduceIte,
          Nat.add_zero, BlockSearch.finish, capacity, BatchSkeleton.capacity]
      · rw [ite_eq_right hs] at hout
        obtain ⟨out', ho, he⟩ := Option.map_eq_some_iff.mp hout
        subst out
        have hh := ih (double q) (out := out') ho
        simp only [localCost, semanticStage, evaluate, hs, ↓reduceIte, hh]
        exact Nat.add_comm _ _

theorem localCost_bound (hn : 0 < n) (input : List (Edge n)) (x : ℕ) (q : Query n)
    (hB : q.request.block.card ≤ x) (hτ : q.request.threshold = 1)
    (seed : Fin n → Distance)
    (hinit : ∀ v, multiDist (BlockSearch.blockGraph input q.request.block) seed v ≤
      SparseLabels.get q.sources v) :
    localCost hn input (Nat.log 2 x + 2) q ≤
      4 * x * ((found q.request.block q.request.known
        (multiDist (BlockSearch.blockGraph input q.request.block) seed) q.radiusNumerator).card + 1) := by
  have hb : q.request.block.card < q.request.threshold * 2 ^ (Nat.log 2 x + 1) := by
    rw [hτ, Nat.one_mul]
    exact hB.trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) x)
  obtain ⟨out, hout⟩ := BlockSearch.searchAux_terminates hn q.request.block q.request.known
    q.radiusNumerator (SparseLabels.vector q.sources) input (Nat.log 2 x + 1)
    q.request.threshold hb
  have hlo : ∀ v, multiDist (BlockSearch.blockGraph input q.request.block) seed v ≤
      (SparseLabels.vector q.sources).get v := by simpa only [SparseLabels.vector_get] using hinit
  let c := (found q.request.block q.request.known
    (multiDist (BlockSearch.blockGraph input q.request.block) seed) q.radiusNumerator).card
  have ht := BlockSearch.searchAux_threshold hn q.request.block q.request.known
    q.radiusNumerator (SparseLabels.vector q.sources) input seed hlo _ _
    (max 1 (2 * c)) (by rw [hτ]; exact le_max_left _ _)
    (le_max_right _ _) hout
  have ha := (BlockSearch.searchAux_accounting hn q.request.block q.request.known
    q.radiusNumerator (SparseLabels.vector q.sources) input _ _ hout).2.2
  have he := localCost_eq_reservations hn input _ q hout
  have ht' : out.lastThreshold ≤ 2 * (c + 1) := by omega
  have hres : out.reservations ≤ 4 * q.request.block.card * (c + 1) := by
    nlinarith only [ha, Nat.mul_le_mul_left (2 * q.request.block.card) ht']
  rw [he]
  exact hres.trans (Nat.mul_le_mul_right (c + 1) (Nat.mul_le_mul_left 4 hB))

theorem run_scan_bound (hn : 0 < n) (input : List (Edge n)) (x : ℕ)
    (jobs : List (Query n)) (seed : Query n → Fin n → Distance)
    (hj : ∀ q ∈ jobs, q.request.block.card ≤ x ∧ q.request.threshold = 1)
    (hi : ∀ q ∈ jobs, ∀ v,
      multiDist (BlockSearch.blockGraph input q.request.block) (seed q) v ≤
        SparseLabels.get q.sources v) :
    n * (run hn input x jobs).scans ≤ n * (Nat.log 2 x + 2) +
      8 * x * (jobs.map (fun q =>
        (found q.request.block q.request.known
          (multiDist (BlockSearch.blockGraph input q.request.block) (seed q))
          q.radiusNumerator).card + 1)).sum := by
  let charge : Query n → ℕ := fun q =>
    (found q.request.block q.request.known
      (multiDist (BlockSearch.blockGraph input q.request.block) (seed q))
      q.radiusNumerator).card + 1
  have hpoint : ∀ q ∈ jobs, localCost hn input (Nat.log 2 x + 2) q ≤ 4 * x * charge q := by
    intro q hq
    exact localCost_bound hn input x q (hj q hq).1 (hj q hq).2 (seed q) (hi q hq)
  have hsum (xs : List (Query n))
      (hx : ∀ q ∈ xs, localCost hn input (Nat.log 2 x + 2) q ≤ 4 * x * charge q) :
      (xs.map (localCost hn input (Nat.log 2 x + 2))).sum ≤
        4 * x * (xs.map charge).sum := by
    induction xs with
    | nil => simp
    | cons q qs ih =>
        have hh := hx q (by simp)
        have ht := ih (fun z hz => hx z (by simp [hz]))
        simp only [List.map_cons, List.sum_cons]
        nlinarith only [hh, ht]
  obtain ⟨hph, hcost⟩ := runPhases_cost hn input (Nat.log 2 x + 2) jobs
  rw [runPhases_reservations] at hcost
  have hs := hsum jobs hpoint
  have hm := Nat.mul_le_mul_left n hph
  change n * (runPhases hn input (Nat.log 2 x + 2) jobs).scans ≤ _
  dsimp only [charge] at hs
  nlinarith only [hcost, hs, hm]

end StreamingSSSP.Core.BatchSearch
