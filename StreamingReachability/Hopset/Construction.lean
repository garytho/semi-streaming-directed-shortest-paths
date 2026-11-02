module

public import StreamingReachability.Hopset.Calibration
public import StreamingReachability.Hopset.TrialBounds
public import StreamingReachability.Hopset.TrialSound

@[expose] public section

namespace StreamingReachability.Hopset

inductive Builder (n : ℕ) (A : Type*) where
  | pure (value : A)
  | trial (cfg : Config) (positive : 0 < n) (stored : Implicit.Representation n)
      (next : Option (Output n) → Builder n A)

namespace Builder

variable {n : ℕ} {A B : Type*}

def bind : Builder n A → (A → Builder n B) → Builder n B
  | .pure a, f => f a
  | .trial cfg hn stored next, f => .trial cfg hn stored fun result => bind (next result) f

def map (p : Builder n A) (f : A → B) : Builder n B := p.bind fun a => .pure (f a)

noncomputable def evaluate (handler : Code.Handler n) : Builder n A → Law A
  | .pure a => Law.pure a
  | .trial cfg hn stored next =>
      (Code.evaluate handler (fixedGuess cfg hn stored)).bind fun result =>
        evaluate handler (next result)

theorem expect_bind (handler : Code.Handler n) (p : Builder n A) (f : A → Builder n B)
    (g : B → ℝ) :
    (evaluate handler (p.bind f)).expect g =
      (evaluate handler p).expect (fun a => (evaluate handler (f a)).expect g) := by
  induction p with
  | pure a => simp [bind, evaluate]
  | trial cfg hn stored next ih =>
      simp only [bind, evaluate, Law.expect_bind]
      apply congrArg (Code.evaluate handler (fixedGuess cfg hn stored)).expect
      funext result
      exact ih result

end Builder

def guessExponent (n wmin wmax : ℕ) : ℕ :=
  Parameters.firstCross wmin 2 (2 * n * wmax) (2 * n * wmax)

def guesses (n wmin wmax : ℕ) (hwmin : 0 < wmin) : List { delta : ℕ // 0 < delta } :=
  (List.range (guessExponent n wmin wmax + 1)).map fun j =>
    ⟨wmin * 2 ^ j, by positivity⟩

def executeGuesses {n : ℕ} (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (frozen : Implicit.Representation n) :
    List { delta : ℕ // 0 < delta } → Implicit.Representation n → Builder n (Implicit.Representation n)
  | [], committed => .pure committed
  | delta :: rest, committed =>
      let cfg := Parameters.configuration n accuracy x delta.val
        (volume frozen.blocks) ha delta.property
      .trial cfg hn frozen fun result =>
        executeGuesses hn accuracy x ha frozen rest
          (match result with | none => committed | some out => commit committed out)

def repeatTrials {n : ℕ} (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (deltas : List { delta : ℕ // 0 < delta }) (frozen : Implicit.Representation n) :
    ℕ → Implicit.Representation n → Builder n (Implicit.Representation n)
  | 0, committed => .pure committed
  | count + 1, committed =>
      (executeGuesses hn accuracy x ha frozen deltas committed).bind fun next =>
        repeatTrials hn accuracy x ha deltas frozen count next

def stages {n : ℕ} (hn : 0 < n) (accuracy x : ℕ) (ha : 0 < accuracy)
    (deltas : List { delta : ℕ // 0 < delta }) (trials : ℕ) :
    ℕ → Implicit.Representation n → Builder n (Implicit.Representation n)
  | 0, stored => .pure stored
  | count + 1, stored =>
      (repeatTrials hn accuracy x ha deltas stored trials stored).bind fun next =>
        stages hn accuracy x ha deltas trials count next

def construct {n : ℕ} (hn : 0 < n) (accuracy x confidence wmin wmax : ℕ)
    (ha : 0 < accuracy) (hwmin : 0 < wmin) (initial : Implicit.Representation n) :
    Builder n (Implicit.Representation n) :=
  stages hn accuracy x ha (guesses n wmin wmax hwmin)
    ((confidence + 16) * Parameters.ell n) (Parameters.ell n) initial

theorem guessExponent_large (n wmin wmax : ℕ) (hwmin : 0 < wmin) :
    2 * n * wmax ≤ wmin * 2 ^ guessExponent n wmin wmax := by
  apply Parameters.firstCross_large
  exact (Parameters.nat_le_two_pow _).trans (Nat.le_mul_of_pos_left _ hwmin)

theorem guessExponent_le_logarithm (n wmin wmax : ℕ) (hwmin : 0 < wmin) :
    guessExponent n wmin wmax ≤ Parameters.ell (2 * n * wmax) := by
  by_contra h
  unfold guessExponent at h
  have hsmall := Parameters.firstCross_small wmin 2 (2 * n * wmax) (2 * n * wmax)
    (Parameters.ell (2 * n * wmax)) (by omega)
  have hlarge := (Parameters.lt_two_pow_ell (2 * n * wmax)).trans_le
    (Nat.le_mul_of_pos_left _ hwmin)
  omega

theorem guesses_length (n wmin wmax : ℕ) (hwmin : 0 < wmin) :
    (guesses n wmin wmax hwmin).length = guessExponent n wmin wmax + 1 := by
  unfold guesses
  rw [List.length_map, List.length_range]

end StreamingReachability.Hopset
