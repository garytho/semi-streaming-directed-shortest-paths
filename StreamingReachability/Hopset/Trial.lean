module

public import StreamingReachability.Hopset.Program
public import StreamingReachability.Hopset.Profile
public import StreamingReachability.Hopset.Representation

@[expose] public section

namespace StreamingReachability.Hopset

open StoredEdges

variable {n : ℕ}

structure Output (n : ℕ) where
  explicit : List (Edge n) := []
  blocks : List (Finset (Fin n)) := []

structure State (n : ℕ) where
  output : Output n
  copies : ℕ
  records : ℕ

def volume (blocks : List (Finset (Fin n))) : ℕ := (blocks.map Finset.card).sum

def recordCharge (blocks : List (Finset (Fin n))) (reply : Core.BatchAPI.SparseReply n) : ℕ :=
  (reply.map fun record =>
    1 + (blocks.filter fun B => decide (record.vertex ∈ B)).length).sum

theorem reply_length_le_charge (blocks : List (Finset (Fin n)))
    (reply : Core.BatchAPI.SparseReply n) :
    reply.length ≤ recordCharge blocks reply := by
  induction reply with
  | nil => simp [recordCharge]
  | cons record reply ih =>
      simp only [recordCharge, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

def emittedStars (cfg : Config) {ns : ℕ} (targets : List (Target n ns))
    (reply : Core.BatchAPI.SparseReply n) : List (Edge n) :=
  reply.filterMap fun record =>
    match targets[record.queryId / 2]? with
    | none => none
    | some target =>
        if target.kind = .pivot ∨ record.vertex = target.vertex then none else
          some ⟨if record.queryId % 2 = 1 then record.vertex else target.vertex,
            if record.queryId % 2 = 1 then target.vertex else record.vertex,
            cfg.inputScale * record.distance⟩

theorem emittedStars_length (cfg : Config) {ns : ℕ} (targets : List (Target n ns))
    (reply : Core.BatchAPI.SparseReply n) :
    (emittedStars cfg targets reply).length ≤ reply.length :=
  List.length_filterMap_le _ _

def batch (cfg : Config) (r : ℕ) (stored : Implicit.Representation n)
    {ns : ℕ} (sets : Vector (Finset (Fin n)) ns)
    (targets : List (Target n ns)) (state : State n) :
    Code n (Core.BatchAPI.SparseReply n × State n) :=
  let request := Core.BatchAPI.Request.ofCatalog stored.explicit
    (catalog cfg r stored.blocks sets targets) cfg.blockSize
  .batch request (cfg.recordCap - state.records) fun reply =>
    let charge := recordCharge stored.blocks reply
    if state.records + charge ≤ cfg.recordCap then
      .pure (reply, { state with
        records := state.records + charge
        output := { state.output with
          explicit := state.output.explicit ++ emittedStars cfg targets reply } })
    else .abort

def pivotLoop (cfg : Config) (r : ℕ) {ns : ℕ} (sets : Vector (Finset (Fin n)) ns)
    (reply : Core.BatchAPI.SparseReply n) :
    List (Target n ns) → ℕ → Code n (List (Pivot n ns))
  | [], _ => .pure []
  | target :: targets, index =>
      if target.kind = .pivot then
        (Code.drawPair cfg.groups cfg.shifts cfg.groups_pos cfg.shifts_pos).bind fun owner =>
          let eta := chooseEta cfg r (sets.get target.setId) reply
            (2 * index) (2 * index + 1) owner.1 owner.2
          (pivotLoop cfg r sets reply targets (index + 1)).map fun ps =>
            ⟨target.setId, target.vertex, eta, owner.2.val, 2 * index, 2 * index + 1⟩ :: ps
      else pivotLoop cfg r sets reply targets (index + 1)

def lateTargetLoop (cfg : Config) (hn : 0 < n) (r : ℕ) {ns : ℕ}
    (sets : Vector (Finset (Fin n)) ns) :
    List (Fin ns) → Code n (List (Target n ns))
  | [] => .pure []
  | i :: is =>
      let chosen : Code n (Finset (Fin n)) :=
        if r < cfg.maximumLevel then
          Code.subset (PivotProfile.rate n hn cfg.k cfg.logarithm r) (members (sets.get i))
        else .pure (sets.get i)
      chosen.bind fun pivots =>
        (lateTargetLoop cfg hn r sets is).map fun rest =>
          ((members pivots).map fun v => ⟨i, v, .pivot⟩) ++ rest

def levels (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n)
    (rank : Vector ℕ n) :
    ℕ → ℕ → List (Finset (Fin n)) → State n → Code n (Output n)
  | 0, _, _, state => .pure state.output
  | fuel + 1, r, queue, state =>
      let sets := queue.toArray.toVector
      if r < cfg.earlyLevel then
        let targets := earlyTargets cfg r rank sets
        (batch cfg r stored sets targets state).bind fun result =>
          (pivotLoop cfg r sets result.1 targets 0).bind fun pivots =>
            let children := earlyFringes cfg r sets pivots result.1 ++
              earlyCore cfg r sets pivots result.1
            let copied := result.2.copies + volume children
            if copied ≤ cfg.copyCap then
              levels cfg hn stored rank fuel (r + 1) children { result.2 with copies := copied }
            else .abort
      else
        (lateTargetLoop cfg hn r sets (List.finRange _)).bind fun targets =>
          (batch cfg r stored sets targets state).bind fun result =>
            (pivotLoop cfg r sets result.1 targets 0).bind fun pivots =>
              let blocks := lateBlocks cfg r sets pivots result.1
              let combined := result.2.output.blocks ++ blocks
              if blocks.all (fun B => decide (B.card ≤ cfg.blockSize)) &&
                  decide (volume combined ≤ cfg.blockCap) then
                let children := if r < cfg.maximumLevel
                  then lateCore cfg r sets pivots result.1 else []
                let copied := result.2.copies + volume children
                if copied ≤ cfg.copyCap then
                  levels cfg hn stored rank fuel (r + 1) children
                    { result.2 with
                      copies := copied
                      output := { result.2.output with blocks := combined } }
                else .abort
              else .abort

def fixedGuess (cfg : Config) (hn : 0 < n) (stored : Implicit.Representation n) :
    Code n (Output n) :=
  if n ≤ cfg.copyCap then
    (Code.ranks (PivotProfile.rates n hn cfg.k cfg.logarithm cfg.earlyLevel)).bind fun rank =>
      let state : State n := ⟨{}, n, 0⟩
      let sets : Vector (Finset (Fin n)) 1 := Vector.replicate 1 Finset.univ
      let targets := globalTargets cfg rank
      (batch cfg 0 stored sets targets state).bind fun result =>
        levels cfg hn stored rank (cfg.maximumLevel + 1) 0 [Finset.univ] result.2
  else .abort

end StreamingReachability.Hopset
