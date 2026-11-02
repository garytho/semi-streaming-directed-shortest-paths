module

public import StreamingReachability.Core.BatchDriver

@[expose] public section

namespace StreamingReachability.Core.BatchDriver

open StoredEdges

variable {n nb ns nq : ℕ}

def canonical (old : States n nb nq) (j : Fin nq) (i : Fin nb) : Shared.Job n nb nq :=
  ⟨j, i, (RecordMap.get Global.emptyBlock (old.get j).cache i).known, 1, 0, 0⟩

theorem job_origin (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    {job : Shared.Job n nb nq} (hj : job ∈ jobs c r old) :
    ∃ bs, (job.blockId, bs) ∈ (old.get job.searchId).cache ∧ bs.next = (r : Distance) ∧
      job.sources = bs.known ∧ job.threshold = 1 ∧ job.spentScans = 0 ∧
      job.spentReservations = 0 ∧ r ≤ (c.searches.get job.searchId).radius := by
  rw [jobs, List.mem_dedup] at hj
  obtain ⟨j, _, hmem⟩ := List.mem_flatMap.mp hj
  by_cases ha : r ≤ (c.searches.get j).radius
  · simp only [ha, ↓reduceIte] at hmem
    obtain ⟨pair, hp, he⟩ := List.mem_filterMap.mp hmem
    by_cases hn : pair.2.next = (r : Distance)
    · have hjob : (⟨j, pair.1, pair.2.known, 1, 0, 0⟩ : Shared.Job n nb nq) = job := by
        simpa only [hn, ↓reduceIte, Option.some.injEq] using he
      subst job
      exact ⟨pair.2, hp, hn, rfl, rfl, rfl, rfl, ha⟩
    · simp [hn] at he
  · simp [ha] at hmem

theorem job_canonical (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache)
    {job : Shared.Job n nb nq} (hj : job ∈ jobs c r old) :
    job = canonical old job.searchId job.blockId := by
  obtain ⟨bs, hm, _, hsrc, ht, hsc, hres, _⟩ := job_origin c r old hj
  have hg := RecordMap.get_mem Global.emptyBlock (old.get job.searchId).cache (hu _) hm
  cases job
  simp_all [canonical]

theorem canonical_mem (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (hu : ∀ j, RecordMap.Unique (old.get j).cache) (j : Fin nq) (i : Fin nb)
    (bs : Global.BlockState n) (hm : (i, bs) ∈ (old.get j).cache)
    (ha : r ≤ (c.searches.get j).radius) (hn : bs.next = (r : Distance)) :
    canonical old j i ∈ jobs c r old := by
  rw [jobs, List.mem_dedup]
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_finRange j, ?_⟩
  simp only [ha, ↓reduceIte]
  apply List.mem_filterMap.mpr
  refine ⟨(i, bs), hm, ?_⟩
  have hg := RecordMap.get_mem Global.emptyBlock (old.get j).cache (hu j) hm
  simp only [hn, ↓reduceIte, canonical, hg]

theorem get_all_equal {K S : Type*} [DecidableEq K] (zero : S)
    (xs : RecordMap.Map K S) (k : K) (s : S)
    (hex : ∃ p ∈ xs, p.1 = k)
    (hall : ∀ p ∈ xs, p.1 = k → p.2 = s) : RecordMap.get zero xs k = s := by
  induction xs with
  | nil => simp at hex
  | cons p ps ih =>
      by_cases hp : p.1 = k
      · rw [RecordMap.get_cons, ite_eq_left hp]
        exact hall p (by simp) hp
      · rw [RecordMap.get_cons, ite_eq_right hp]
        apply ih
        · obtain ⟨q, hq, he⟩ := hex
          rcases List.mem_cons.mp hq with rfl | hq
          · exact False.elim (hp he)
          · exact ⟨q, hq, he⟩
        · intro q hq he
          exact hall q (by simp [hq]) he

theorem answers_get (hn : 0 < n) (c : Shared.Catalog n nb ns nq) (stored input : List (Edge n))
    (x r : ℕ) (old : States n nb nq) (hu : ∀ j, RecordMap.Unique (old.get j).cache)
    (hx : ∀ i, (c.blocks.get i).card ≤ x)
    (j : Fin nq) (i : Fin nb) (hj : canonical old j i ∈ jobs c r old) :
    ∃ out,
      ViewedSkeleton.search hn (Shared.view c j) (Shared.block c j i)
        (SparseLabels.support (canonical old j i).sources) (c.scale * r)
        (SparseLabels.vector (canonical old j i).sources) stored input = some out ∧
      RecordMap.get none
        (answers (jobs c r old)
          (Shared.Engine.run hn c stored input r (Nat.log 2 x + 2) (tasks (jobs c r old))).tasks)
        (j, i) = some out := by
  let pending := jobs c r old
  let done := (Shared.Engine.run hn c stored input r (Nat.log 2 x + 2) (tasks pending)).tasks
  obtain ⟨wanted, hw⟩ := BlockSearch.search_terminates hn (Shared.block c j i)
    (SparseLabels.support (canonical old j i).sources) (c.scale * r)
    (SparseLabels.vector (canonical old j i).sources) ((stored ++ input).filterMap (Shared.view c j))
  have hview : ViewedSkeleton.search hn (Shared.view c j) (Shared.block c j i)
      (SparseLabels.support (canonical old j i).sources) (c.scale * r)
      (SparseLabels.vector (canonical old j i).sources) stored input = some wanted := by
    rwa [ViewedSkeleton.search_eq]
  have hdone (k : Fin pending.length) (hkey : key (pending.get k) = (j, i)) :
      done.get k = .finished wanted := by
    have hmem : pending.get k ∈ pending := List.get_mem pending k
    have hc := job_canonical c r old hu hmem
    have hjob : pending.get k = canonical old j i := by
      obtain ⟨h1, h2⟩ := Prod.mk.inj hkey
      simpa only [h1, h2] using hc
    obtain ⟨out, hout, htask⟩ := Shared.Engine.finished_result hn c stored input r x
      (tasks pending) k (pending.get k) (by simp [tasks])
      ((Shared.block_card_le c _ _).trans (hx _))
      (by rw [hjob]; rfl) (by rw [hjob]; rfl) (by rw [hjob]; rfl)
    rw [hjob] at hout
    have he : out = wanted := Option.some.inj (hout.symm.trans hview)
    subst out
    exact htask
  refine ⟨wanted, hview, ?_⟩
  apply get_all_equal none (answers pending done) (j, i) (some wanted)
  · obtain ⟨k, hk⟩ := List.mem_iff_get.mp hj
    refine ⟨_, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩, ?_⟩
    change key (pending.get k) = (j, i)
    rw [hk]
    rfl
  · intro pair hp hkey
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    have ht := hdone k hkey
    simp only [ht]

theorem ordinary_get (c : Shared.Catalog n nb ns nq) (r : ℕ) (old : States n nb nq)
    (stored input : List (Edge n)) (j : Fin nq) :
    (ordinary c r old stored input).state.get j =
      if r ≤ (c.searches.get j).radius
      then (stored ++ input).foldl
        (SparseDriver.edgeStep (SparseDriver.ofCatalog c j) r (old.get j)) ∅ else ∅ := by
  have h (xs : List (Edge n)) (C : Vector (Finset (Fin n)) nq) :
      (xs.foldl (ordinaryStep c r old) C).get j =
        if r ≤ (c.searches.get j).radius
        then xs.foldl (SparseDriver.edgeStep (SparseDriver.ofCatalog c j) r (old.get j)) (C.get j)
        else C.get j := by
    induction xs generalizing C with
    | nil => split_ifs <;> rfl
    | cons e es ih =>
        rw [List.foldl_cons, ih]
        simp only [ordinaryStep, Vector.get_ofFn]
        split_ifs <;> rfl
  rw [ordinary, Streaming.readPass_state, ← List.foldl_append, h]
  simp

end StreamingReachability.Core.BatchDriver
