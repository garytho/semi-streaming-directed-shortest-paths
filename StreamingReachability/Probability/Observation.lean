module

public import StreamingReachability.Probability.ConditionalFamily
public import StreamingReachability.Probability.Projection

@[expose] public section

namespace StreamingReachability.Law

open scoped Classical BigOperators

variable {A B : Type*}

theorem given_restrict_factor (mu : Law A) (P Q R : A → Prop) (hp : 0 < mu.prob P)
    (he : ∀ a, (P a ∧ Q a) ↔ R a) (f : A → ℝ) :
    (mu.given P).expect (masked Q f) =
      (mu.given P).prob Q * (mu.given R).expect f := by
  have hpred : (fun a => P a ∧ Q a) = R := funext (fun a => propext (he a))
  have hmain (g : A → ℝ) :
      mu.prob P * (mu.given P).expect (masked Q g) = mu.prob R * (mu.given R).expect g := by
    calc
      _ = mu.expect (masked P (masked Q g)) := (expect_mask_eq mu P (masked Q g)).symm
      _ = mu.expect (masked R g) := by rw [masked_mask, hpred]
      _ = _ := expect_mask_eq mu R g
  have hmass := hmain (fun _ => 1)
  simp only [← prob_eq_mask, expect_const, mul_one] at hmass
  apply mul_left_cancel₀ (ne_of_gt hp)
  calc
    _ = mu.prob R * (mu.given R).expect f := hmain f
    _ = (mu.prob P * (mu.given P).prob Q) * (mu.given R).expect f := by rw [hmass]
    _ = _ := by ring

theorem family_observation [Fintype B] (n : ℕ) (mu : Fin n → Law A)
    (signal : Fin n → Law B) (observe : Fin n → A → B) (posterior : Fin n → B → Law A)
    (hcomponent : ∀ i b g, (mu i).expect (masked (fun a => observe i a = b) g) =
      (signal i).prob (· = b) * (posterior i b).expect g)
    (f : (Fin n → B) → (Fin n → A) → ℝ) :
    (family n mu).expect (fun xs => f (fun i => observe i (xs i)) xs) =
      (family n signal).expect (fun bs => (family n (fun i => posterior i (bs i))).expect (f bs)) := by
  rw [expect_partition (family n mu) Finset.univ (fun xs => fun i => observe i (xs i))
    (fun _ => Finset.mem_univ _) f, expect_finite]
  apply Finset.sum_congr rfl
  intro bs _
  have he :
      (fun xs : Fin n → A => (fun i => observe i (xs i)) = bs) =
        fun xs => ∀ i, observe i (xs i) = bs i := by
    funext xs
    apply propext
    constructor
    · intro h i; exact congrFun h i
    · intro h; exact funext h
  rw [he, family_mask_transfer n mu (fun i => posterior i (bs i))
    (fun i a => observe i a = bs i) (fun i => (signal i).prob (· = bs i))
    (fun i g => hcomponent i (bs i) g) (f bs)]
  rw [family_projection_probability n n signal (fun i => i) Function.injective_id bs]

theorem family_observation_tower [Fintype B] (n : ℕ) (mu : Fin n → Law A)
    (signal : Fin n → Law B) (observe : Fin n → A → B) (posterior : Fin n → B → Law A)
    (hcomponent : ∀ i b g, (mu i).expect (masked (fun a => observe i a = b) g) =
      (signal i).prob (· = b) * (posterior i b).expect g)
    (f : (Fin n → A) → ℝ) :
    (family n mu).expect f =
      (family n signal).expect (fun bs => (family n (fun i => posterior i (bs i))).expect f) :=
  family_observation n mu signal observe posterior hcomponent (fun _ => f)

end StreamingReachability.Law
