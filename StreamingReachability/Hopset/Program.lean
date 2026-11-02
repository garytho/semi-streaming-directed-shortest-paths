module

public import StreamingReachability.Hopset.Partition
public import StreamingReachability.Hopset.Rank
public import StreamingReachability.Probability.Family
public import StreamingReachability.Probability.Independent

@[expose] public section

namespace StreamingReachability.Hopset

inductive Code (n : ℕ) (A : Type*) where
  | pure (value : A)
  | abort
  | uniform (bound : ℕ) (positive : 0 < bound) (next : Fin bound → Code n A)
  | batch (request : Core.BatchAPI.Request n) (recordAllowance : ℕ)
      (next : Core.BatchAPI.SparseReply n → Code n A)

namespace Code

variable {n : ℕ} {A B : Type*}

def bind : Code n A → (A → Code n B) → Code n B
  | .pure a, f => f a
  | .abort, _ => .abort
  | .uniform d hd next, f => .uniform d hd fun i => bind (next i) f
  | .batch request budget next, f => .batch request budget fun reply => bind (next reply) f

def map (p : Code n A) (f : A → B) : Code n B := p.bind fun a => .pure (f a)

def Ensures : Code n A → (A → Prop) → Prop
  | .pure a, P => P a
  | .abort, _ => True
  | .uniform _ _ next, P => ∀ i, Ensures (next i) P
  | .batch _ _ next, P => ∀ reply, Ensures (next reply) P

theorem ensures_true (p : Code n A) : p.Ensures (fun _ => True) := by
  induction p with
  | pure a => trivial
  | abort => trivial
  | uniform d hd next ih => exact ih
  | batch request budget next ih => exact ih

theorem ensures_mono (p : Code n A) (P Q : A → Prop)
    (hp : p.Ensures P) (h : ∀ a, P a → Q a) : p.Ensures Q := by
  induction p with
  | pure a => exact h a hp
  | abort => trivial
  | uniform d hd next ih => exact fun i => ih i (hp i)
  | batch request budget next ih => exact fun reply => ih reply (hp reply)

theorem ensures_bind (p : Code n A) (f : A → Code n B) (P : A → Prop) (Q : B → Prop)
    (hp : p.Ensures P) (hf : ∀ a, P a → (f a).Ensures Q) :
    (p.bind f).Ensures Q := by
  induction p with
  | pure a => exact hf a hp
  | abort => trivial
  | uniform d hd next ih => exact fun i => ih i (hp i)
  | batch request budget next ih => exact fun reply => ih reply (hp reply)

theorem ensures_map (p : Code n A) (f : A → B) (Q : B → Prop)
    (hp : p.Ensures fun a => Q (f a)) : (p.map f).Ensures Q :=
  ensures_bind p (fun a => .pure (f a)) (fun a => Q (f a)) Q hp (by tauto)

abbrev Handler (n : ℕ) :=
  Core.BatchAPI.Request n → ℕ → Law (Option (Core.BatchAPI.SparseReply n))

noncomputable def evaluate (handler : Handler n) : Code n A → Law (Option A)
  | .pure a => Law.pure (some a)
  | .abort => Law.pure none
  | .uniform d hd next => (Law.uniform d hd).bind fun i => evaluate handler (next i)
  | .batch request budget next =>
      (handler request budget).bind fun result =>
        match result with
        | none => Law.pure none
        | some reply => evaluate handler (next reply)

theorem probability_ensures (handler : Handler n) (p : Code n A) (P : A → Prop)
    (hp : p.Ensures P) :
    (evaluate handler p).prob (fun result =>
      match result with
      | none => True
      | some a => P a) = 1 := by
  induction p with
  | pure a =>
      change P a at hp
      simp [evaluate, Law.prob, hp]
  | abort => simp [evaluate, Law.prob]
  | uniform d hd next ih =>
      rw [evaluate, Law.prob_bind]
      have he : (fun i => (evaluate handler (next i)).prob
          (fun result => match result with | none => True | some a => P a)) =
          fun _ => (1 : ℝ) := by
        funext i
        exact ih i (hp i)
      rw [he, Law.expect_const]
  | batch request budget next ih =>
      rw [evaluate, Law.prob_bind]
      calc
        _ = (handler request budget).expect (fun _ => 1) := by
          congr 1
          funext result
          cases result with
          | none => simp [Law.prob]
          | some reply => exact ih reply (hp reply)
        _ = 1 := Law.expect_const _ _

theorem expect_bind (handler : Handler n) (p : Code n A) (f : A → Code n B)
    (g : Option B → ℝ) :
    (evaluate handler (p.bind f)).expect g =
      (evaluate handler p).expect (fun result =>
        match result with
        | none => g none
        | some a => (evaluate handler (f a)).expect g) := by
  induction p with
  | pure a => simp [bind, evaluate]
  | abort => simp [bind, evaluate]
  | uniform d hd next ih =>
      simp only [bind, evaluate, Law.expect_bind]
      apply congrArg (Law.expect (Law.uniform d hd))
      funext i
      exact ih i
  | batch request budget next ih =>
      simp only [bind, evaluate, Law.expect_bind]
      apply congrArg (Law.expect (handler request budget))
      funext result
      cases result with
      | none => simp
      | some reply => exact ih reply

theorem expect_map (handler : Handler n) (p : Code n A) (f : A → B)
    (g : Option B → ℝ) :
    (evaluate handler (p.map f)).expect g =
      (evaluate handler p).expect (fun result => g (result.map f)) := by
  rw [map, expect_bind]
  congr 1
  funext result
  cases result <;> simp [evaluate]

def drawRate (p : Rate) : Code n Bool :=
  .uniform p.denominator p.denominator_pos fun i => .pure (decide (i.val < p.numerator))

theorem expect_drawRate (handler : Handler n) (p : Rate) (f : Option Bool → ℝ) :
    (evaluate handler (drawRate p)).expect f =
      p.draw.expect (fun b => f (some b)) := by
  simp only [drawRate, evaluate, Law.expect_bind, Law.expect_pure, Rate.draw, Law.expect_map]

def drawPair (m d : ℕ) (hm : 0 < m) (hd : 0 < d) : Code n (Fin m × Fin d) :=
  .uniform m hm fun i => .uniform d hd fun j => .pure (i, j)

theorem expect_drawPair (handler : Handler n) (m d : ℕ) (hm : 0 < m) (hd : 0 < d)
    (f : Option (Fin m × Fin d) → ℝ) :
    (evaluate handler (drawPair m d hm hd)).expect f =
      (Law.uniformPair m d hm hd).expect (fun z => f (some z)) := by
  simp only [drawPair, evaluate, Law.expect_bind, Law.expect_pure, Law.uniformPair,
    Law.expect_map]

def subset (p : Rate) : List (Fin n) → Code n (Finset (Fin n))
  | [] => .pure ∅
  | v :: vs =>
      (drawRate p).bind fun hit =>
        if hit then (subset p vs).map (insert v) else subset p vs

theorem expect_subset (handler : Handler n) (p : Rate) (vs : List (Fin n))
    (f : Option (Finset (Fin n)) → ℝ) :
    (evaluate handler (subset p vs)).expect f =
      (Law.subset (fun _ : Fin n => p.value) (fun _ => p.value_nonneg)
        (fun _ => p.value_le_one) vs).expect (fun S => f (some S)) := by
  induction vs generalizing f with
  | nil => simp [subset, evaluate, Law.subset]
  | cons v vs ih =>
      rw [subset, expect_bind, expect_drawRate, Rate.expect_as_coin,
        Law.subset, Law.expect_bind]
      apply congrArg (Law.coin p.value p.value_nonneg p.value_le_one).expect
      funext b
      cases b with
      | false =>
          dsimp only
          simpa only [Bool.false_eq_true, ↓reduceIte] using ih f
      | true =>
          dsimp only
          simp only [↓reduceIte]
          rw [expect_map, Law.expect_map]
          rw [ih (fun result => f (result.map (insert v)))]
          congr 1
          funext S
          apply congrArg f
          apply congrArg some
          exact congrArg (fun d : DecidableEq (Fin n) =>
            @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert _ d) v S)
            (Subsingleton.elim _ _)

def firstRank : List Rate → Code n ℕ
  | [] => .pure 0
  | p :: ps =>
      (drawRate p).bind fun b =>
        if b then .pure 0 else (firstRank ps).map Nat.succ

theorem expect_firstRank (handler : Handler n) (ps : List Rate) (f : Option ℕ → ℝ) :
    (evaluate handler (firstRank ps)).expect f =
      (Ranks.firstHit ps).expect (fun r => f (some r)) := by
  induction ps generalizing f with
  | nil => simp [firstRank, evaluate, Ranks.firstHit]
  | cons p ps ih =>
      rw [firstRank, expect_bind, expect_drawRate]
      rw [Ranks.firstHit, Law.expect_bind]
      apply congrArg p.draw.expect
      funext b
      cases b with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [expect_map, Law.expect_map]
          simpa using ih (fun r => f (r.map Nat.succ))
      | true => simp [evaluate]

def rankVector (ps : List Rate) : (m : ℕ) → Code n (Vector ℕ m)
  | 0 => .pure (Vector.ofFn Fin.elim0)
  | m + 1 =>
      (firstRank ps).bind fun r =>
        (rankVector ps m).map fun tail => Vector.ofFn (Fin.cases r (fun i => tail.get i))

def ranks (ps : List Rate) : Code n (Vector ℕ n) := rankVector ps n

theorem expect_rankVector (handler : Handler n) (ps : List Rate) (m : ℕ)
    (f : Option (Vector ℕ m) → ℝ) :
    (evaluate handler (rankVector ps m)).expect f =
      (Law.family m (fun _ => Ranks.firstHit ps)).expect
        (fun xs => f (some (Vector.ofFn xs))) := by
  induction m with
  | zero => simp [rankVector, evaluate, Law.family]
  | succ m ih =>
      rw [rankVector, expect_bind, expect_firstRank, Law.expect_family_succ]
      apply congrArg (Ranks.firstHit ps).expect
      funext r
      dsimp only
      rw [expect_map]
      simpa using ih
        (fun result => f (result.map fun tail => Vector.ofFn (Fin.cases r (fun i => tail.get i))))

end Code

end StreamingReachability.Hopset
