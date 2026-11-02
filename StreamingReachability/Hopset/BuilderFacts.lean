module

public import StreamingReachability.Hopset.RelativeTrial

@[expose] public section

namespace StreamingReachability.Hopset

namespace Builder

variable {n : ℕ} {A B : Type*}

def Ensures : Builder n A → (A → Prop) → Prop
  | .pure a, P => P a
  | .trial _ _ _ next, P => ∀ result, Ensures (next result) P

theorem ensures_mono (program : Builder n A) (P Q : A → Prop)
    (hP : program.Ensures P) (h : ∀ a, P a → Q a) : program.Ensures Q := by
  induction program with
  | pure a => exact h a hP
  | trial cfg hn stored next ih => exact fun result => ih result (hP result)

theorem ensures_bind (program : Builder n A) (next : A → Builder n B) (P : A → Prop) (Q : B → Prop)
    (hP : program.Ensures P) (hnext : ∀ a, P a → (next a).Ensures Q) :
    (program.bind next).Ensures Q := by
  induction program with
  | pure a => exact hnext a hP
  | trial cfg hn stored resume ih => exact fun result => ih result (hP result)

theorem ensures_evaluate (handler : Code.Handler n) (program : Builder n A) (P : A → Prop)
    (h : program.Ensures P) : Early.Sampling.Holds (evaluate handler program) P := by
  induction program with
  | pure a => exact Early.Sampling.holds_pure a P h
  | trial cfg hn stored next ih =>
      apply Early.Sampling.holds_bind
      intro result
      exact ih result (h result)

theorem prob_bind (handler : Code.Handler n) (program : Builder n A) (next : A → Builder n B) (P : B → Prop) :
    (evaluate handler (program.bind next)).prob P =
      (evaluate handler program).expect (fun a => (evaluate handler (next a)).prob P) := by
  classical
  exact expect_bind handler program next (fun b => if P b then 1 else 0)

end Builder

variable {n : ℕ}

theorem executeGuesses_extends (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (frozen : Implicit.Representation n) (deltas : List {delta : ℕ // 0 < delta})
    (committed : Implicit.Representation n) :
    (executeGuesses hn accuracy x ha frozen deltas committed).Ensures (fun out => out.Extends committed) := by
  induction deltas generalizing committed with
  | nil => exact .refl committed
  | cons delta deltas ih =>
      change ∀ result, _
      intro result
      cases result with
      | none => exact ih committed
      | some out =>
          exact Builder.ensures_mono _ _ _ (ih (commit committed out))
            (fun result h => h.trans (commit_extends committed out))

theorem repeatTrials_extends (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (deltas : List {delta : ℕ // 0 < delta}) (frozen : Implicit.Representation n)
    (count : ℕ) (committed : Implicit.Representation n) :
    (repeatTrials hn accuracy x ha deltas frozen count committed).Ensures (fun out => out.Extends committed) := by
  induction count generalizing committed with
  | zero => exact .refl committed
  | succ count ih =>
      apply Builder.ensures_bind _ _ _ _ (executeGuesses_extends hn accuracy x ha frozen deltas committed)
      intro next hnext
      exact Builder.ensures_mono _ _ _ (ih next) (fun out h => h.trans hnext)

theorem stages_extends (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (deltas : List {delta : ℕ // 0 < delta}) (trials count : ℕ) (stored : Implicit.Representation n) :
    (stages hn accuracy x ha deltas trials count stored).Ensures (fun out => out.Extends stored) := by
  induction count generalizing stored with
  | zero => exact .refl stored
  | succ count ih =>
      apply Builder.ensures_bind _ _ _ _ (repeatTrials_extends hn accuracy x ha deltas stored trials stored)
      intro next hnext
      exact Builder.ensures_mono _ _ _ (ih next) (fun out h => h.trans hnext)

theorem ShortRoute.extends {new old : Implicit.Representation n} (G : Graph (Fin n)) {s t : Fin n}
    {hops : ℕ} {budget : ℝ} (h : ShortRoute (old.graph G) s t hops budget) (he : new.Extends old) :
    ShortRoute (new.graph G) s t hops budget :=
  h.mono_graph (he.graph_le G)

end StreamingReachability.Hopset
