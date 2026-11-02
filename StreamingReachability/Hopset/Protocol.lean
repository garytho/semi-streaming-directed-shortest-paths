module

public import StreamingReachability.Core.InterfaceCorrect

@[expose] public section

namespace StreamingReachability.Hopset

open StoredEdges

structure Config where
  split : ℕ
  split_pos : 0 < split
  groups : ℕ
  groups_pos : 0 < groups
  shifts : ℕ
  shifts_pos : 0 < shifts
  logarithm : ℕ
  maximumLevel : ℕ
  earlyLevel : ℕ
  advance : ℕ
  initialNumerator : ℕ
  initialDenominator : ℕ
  denominator_pos : 0 < initialDenominator
  inputScale : ℕ
  inputScale_pos : 0 < inputScale
  globalRadius : ℕ
  blockSize : ℕ
  copyCap : ℕ
  blockCap : ℕ
  recordCap : ℕ

namespace Config

def k (cfg : Config) : ℕ := cfg.split ^ 2
def width (cfg : Config) : ℕ := 4 * cfg.k
def lambda (cfg : Config) : ℕ := cfg.width * cfg.groups
def etaMax (cfg : Config) : ℕ := 2 * cfg.lambda + 2

def denominatorAt (cfg : Config) (r : ℕ) : ℕ :=
  cfg.initialDenominator * (100 * cfg.split) ^ min r cfg.earlyLevel *
    4 ^ (r - cfg.earlyLevel)

def searchRadius (cfg : Config) (r : ℕ) : ℕ :=
  cfg.etaMax * cfg.initialNumerator / cfg.denominatorAt r

theorem k_pos (cfg : Config) : 0 < cfg.k := by
  have h := cfg.split_pos
  unfold k
  positivity

theorem width_pos (cfg : Config) : 0 < cfg.width := by
  unfold width k
  have h := cfg.split_pos
  positivity

theorem denominatorAt_pos (cfg : Config) (r : ℕ) : 0 < cfg.denominatorAt r := by
  unfold denominatorAt
  have hs := cfg.split_pos
  have hd := cfg.denominator_pos
  positivity

end Config

variable {n : ℕ}

def members (S : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (v ∈ S)

@[simp] theorem mem_members (S : Finset (Fin n)) (v : Fin n) :
    v ∈ members S ↔ v ∈ S := by simp [members]

theorem members_nodup (S : Finset (Fin n)) : (members S).Nodup :=
  (List.nodup_finRange n).filter _

@[simp] theorem members_toFinset (S : Finset (Fin n)) : (members S).toFinset = S := by
  ext v
  simp

def lookup (reply : Core.BatchAPI.SparseReply n) (query : ℕ) (v : Fin n) : Distance :=
  Core.BatchAPI.lookup reply query v

def withinFraction (d : Distance) (numerator denominator : ℕ) : Bool :=
  decide (d ≤ ((numerator / denominator : ℕ) : Distance))

def bothBall (cfg : Config) (r eta shift : ℕ) (S : Finset (Fin n))
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ) : Finset (Fin n) :=
  let numerator := (eta * cfg.shifts + shift) * cfg.initialNumerator
  let denominator := cfg.shifts * cfg.denominatorAt r
  S.filter fun v =>
    withinFraction (lookup reply forward v) numerator denominator ||
      withinFraction (lookup reply backward v) numerator denominator

def fringe (cfg : Config) (r eta shift : ℕ) (S : Finset (Fin n))
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ) : Finset (Fin n) :=
  bothBall cfg r (eta + 1) shift S reply forward backward \
    bothBall cfg r (eta - 1) shift S reply forward backward

def argmin (score : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
      let previous := argmin score t
      if score t < score previous then t else previous

theorem argmin_lt (score : ℕ → ℕ) (t : ℕ) (ht : 0 < t) : argmin score t < t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases hz : t = 0
      · subst t
        simp [argmin]
      · have hb := ih (Nat.pos_of_ne_zero hz)
        simp only [argmin]
        split_ifs <;> omega

theorem argmin_minimal (score : ℕ → ℕ) (t : ℕ) :
    ∀ j < t, score (argmin score t) ≤ score j := by
  induction t with
  | zero => simp
  | succ t ih =>
      intro j hj
      by_cases ht : t = 0
      · subst t
        have he : j = 0 := by omega
        subst j
        simp [argmin]
      · simp only [argmin]
        split_ifs with h
        · by_cases he : j = t
          · simp [he]
          · exact h.le.trans (ih j (by omega))
        · by_cases he : j = t
          · simpa only [he] using Nat.le_of_not_gt h
          · exact ih j (by omega)

def chooseEta (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ)
    (group : Fin cfg.groups) (shift : Fin cfg.shifts) : ℕ :=
  let start := cfg.lambda + cfg.width * group.val
  let score := fun j => (fringe cfg r (start + j) shift.val S reply forward backward).card
  start + argmin score cfg.width

theorem chooseEta_range (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ)
    (group : Fin cfg.groups) (shift : Fin cfg.shifts) :
    cfg.lambda + cfg.width * group.val ≤ chooseEta cfg r S reply forward backward group shift ∧
      chooseEta cfg r S reply forward backward group shift <
        cfg.lambda + cfg.width * group.val + cfg.width := by
  have h := argmin_lt
    (fun j => (fringe cfg r (cfg.lambda + cfg.width * group.val + j) shift.val
      S reply forward backward).card) cfg.width cfg.width_pos
  dsimp only [chooseEta]
  omega

theorem chooseEta_minimal (cfg : Config) (r : ℕ) (S : Finset (Fin n))
    (reply : Core.BatchAPI.SparseReply n) (forward backward : ℕ)
    (group : Fin cfg.groups) (shift : Fin cfg.shifts) :
    ∀ j < cfg.width,
      (fringe cfg r (chooseEta cfg r S reply forward backward group shift) shift.val
        S reply forward backward).card ≤
      (fringe cfg r (cfg.lambda + cfg.width * group.val + j) shift.val
        S reply forward backward).card := by
  dsimp only [chooseEta]
  exact argmin_minimal
    (fun j => (fringe cfg r (cfg.lambda + cfg.width * group.val + j) shift.val
      S reply forward backward).card) cfg.width

def pivotWanted (cfg : Config) (r encoded : ℕ) : Bool :=
  decide (encoded < cfg.earlyLevel ∧ encoded = r)

def advanceWanted (cfg : Config) (r encoded : ℕ) : Bool :=
  decide (encoded < cfg.earlyLevel ∧ encoded = r + cfg.advance)

def globalWanted (cfg : Config) (encoded : ℕ) : Bool :=
  decide (encoded < cfg.earlyLevel ∧ encoded < cfg.advance)

@[simp] theorem pivotWanted_none (cfg : Config) (r : ℕ) :
    pivotWanted cfg r cfg.earlyLevel = false := by simp [pivotWanted]

@[simp] theorem advanceWanted_none (cfg : Config) (r : ℕ) :
    advanceWanted cfg r cfg.earlyLevel = false := by simp [advanceWanted]

@[simp] theorem globalWanted_none (cfg : Config) :
    globalWanted cfg cfg.earlyLevel = false := by simp [globalWanted]

def star (scale : ℕ) (reply : Core.BatchAPI.SparseReply n) (query : ℕ)
    (source : Fin n) (backward : Bool) : List (Edge n) :=
  reply.filterMap fun record =>
    if record.queryId = query ∧ record.vertex ≠ source then
      some ⟨if backward then record.vertex else source,
        if backward then source else record.vertex, scale * record.distance⟩
    else none

theorem star_length (scale : ℕ) (reply : Core.BatchAPI.SparseReply n) (query : ℕ)
    (source : Fin n) (backward : Bool) :
    (star scale reply query source backward).length ≤ reply.length :=
  List.length_filterMap_le _ _

inductive TargetKind where
  | globalStar
  | advanceStar
  | pivot
  deriving DecidableEq, Repr

structure Target (n ns : ℕ) where
  setId : Fin ns
  vertex : Fin n
  kind : TargetKind
  deriving DecidableEq, Repr

def earlyTargets (cfg : Config) (r : ℕ) (rank : Vector ℕ n)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) : List (Target n ns) :=
  (List.finRange ns).flatMap fun i =>
    ((members (sets.get i)).filter fun v => advanceWanted cfg r (rank.get v)).map
        (fun v => ⟨i, v, .advanceStar⟩) ++
      ((members (sets.get i)).filter fun v => pivotWanted cfg r (rank.get v)).map
        (fun v => ⟨i, v, .pivot⟩)

def globalTargets (cfg : Config) (rank : Vector ℕ n) : List (Target n 1) :=
  ((List.finRange n).filter fun v => globalWanted cfg (rank.get v)).map
    (fun v => ⟨0, v, .globalStar⟩)

def targetRadius (cfg : Config) (r : ℕ) (kind : TargetKind) : ℕ :=
  match kind with
  | .globalStar => cfg.globalRadius
  | .advanceStar => cfg.searchRadius r
  | .pivot => cfg.searchRadius r

def queries (cfg : Config) (r : ℕ) {ns : ℕ} (targets : List (Target n ns)) :
    List (Core.BatchAPI.Query n ns) :=
  targets.flatMap fun target =>
    [⟨target.setId, target.vertex, false, targetRadius cfg r target.kind⟩,
      ⟨target.setId, target.vertex, true, targetRadius cfg r target.kind⟩]

def catalog (cfg : Config) (r : ℕ) (blocks : List (Finset (Fin n)))
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) (targets : List (Target n ns)) :
    Core.BatchAPI.Catalog n blocks.length ns (queries cfg r targets).length :=
  ⟨cfg.inputScale, blocks.toArray.toVector, sets, (queries cfg r targets).toArray.toVector⟩

@[simp] theorem queries_length (cfg : Config) (r : ℕ) {ns : ℕ}
    (targets : List (Target n ns)) : (queries cfg r targets).length = 2 * targets.length := by
  induction targets with
  | nil => simp [queries]
  | cons target targets ih =>
      simp only [queries, List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil] at *
      omega

theorem earlyTargets_inside (cfg : Config) (r : ℕ) (rank : Vector ℕ n)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns) :
    ∀ target ∈ earlyTargets cfg r rank sets,
      target.vertex ∈ sets.get target.setId := by
  intro target ht
  obtain ⟨i, _, ht⟩ := List.mem_flatMap.mp ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    exact (mem_members _ _).mp (List.mem_filter.mp hv).1
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    exact (mem_members _ _).mp (List.mem_filter.mp hv).1

end StreamingReachability.Hopset
