module

public import StreamingSSSP.Hopset.ConstructionMemory

@[expose] public section

namespace StreamingSSSP.Hopset.Measured

open Parameters

def valueCapacity (n coefficient exponent confidence : ℕ) : ℕ :=
  (2 * n) ^ (exponent + 100) * envelope n coefficient exponent confidence ^ 100

def registerBits (n coefficient exponent confidence : ℕ) : ℕ :=
  1000 * (envelopeBase coefficient exponent confidence).log2 + 1001 +
    2 * (exponent + 100 + 100 * envelopeDegree coefficient) * ell n

theorem ell_le_vertices (n : ℕ) (hn : 0 < n) : ell n ≤ n := by
  have h := Nat.log_lt_self 2 (Nat.ne_of_gt hn)
  rw [← Nat.log2_eq_log_two] at h
  unfold ell
  omega

theorem capacity_binary (n coefficient exponent confidence : ℕ) (hn : 0 < n) :
    valueCapacity n coefficient exponent confidence < 2 ^ registerBits n coefficient exponent confidence := by
  let B := envelopeBase coefficient exponent confidence
  let d := envelopeDegree coefficient
  have hb : B ≤ 2 ^ (B.log2 + 1) := (Nat.lt_log2_self (n := B)).le
  have hlog : ell n ≤ 2 * n := (ell_le_vertices n hn).trans (by omega)
  have hn2 : 2 * n ≤ 2 ^ (2 * ell n) := by
    have he := ell_pos n
    have h := lt_two_pow_ell n
    have hp : 2 ^ (ell n + 1) ≤ 2 ^ (2 * ell n) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ] at hp
    omega
  have hval : valueCapacity n coefficient exponent confidence ≤
      B ^ 1000 * (2 * n) ^ (exponent + 100 + 100 * d) := by
    change (2 * n) ^ (exponent + 100) * (B ^ 10 * ell n ^ d) ^ 100 ≤ _
    rw [mul_pow (B ^ 10) (ell n ^ d) 100, ← pow_mul, ← pow_mul]
    have he := Nat.pow_le_pow_left hlog (d * 100)
    calc
      _ ≤ (2 * n) ^ (exponent + 100) * (B ^ 1000 * (2 * n) ^ (d * 100)) := by gcongr
      _ = _ := by rw [Nat.mul_comm d 100, pow_add]; ring
  have hp : B ^ 1000 * (2 * n) ^ (exponent + 100 + 100 * d) ≤
      2 ^ (1000 * (B.log2 + 1) + 2 * (exponent + 100 + 100 * d) * ell n) := by
    calc
      _ ≤ (2 ^ (B.log2 + 1)) ^ 1000 * (2 ^ (2 * ell n)) ^ (exponent + 100 + 100 * d) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hb _) (Nat.pow_le_pow_left hn2 _)
      _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  apply (hval.trans hp).trans_lt
  unfold registerBits
  have he : 1000 * (B.log2 + 1) + 2 * (exponent + 100 + 100 * d) * ell n <
      1000 * B.log2 + 1001 + 2 * (exponent + 100 + 100 * d) * ell n := by omega
  exact Nat.pow_lt_pow_right (by decide) he

theorem register_width (n coefficient exponent confidence : ℕ) :
    registerBits n coefficient exponent confidence ≤
      (1000 * (envelopeBase coefficient exponent confidence).log2 + 1001 +
        2 * (exponent + 100 + 100 * envelopeDegree coefficient)) * ell n := by
  have he := ell_pos n
  unfold registerBits
  nlinarith

theorem capacity_monomial (n coefficient exponent confidence i j : ℕ) (hn : 0 < n)
    (hi : i ≤ exponent + 100) (hj : j ≤ 100) :
    n ^ i * envelope n coefficient exponent confidence ^ j ≤ valueCapacity n coefficient exponent confidence := by
  have hE : 1 ≤ envelope n coefficient exponent confidence :=
    le_trans (by norm_num : 1 ≤ 1024) (envelope_large n coefficient exponent confidence)
  have hp : n ^ i ≤ (2 * n) ^ (exponent + 100) :=
    (Nat.pow_le_pow_left (by omega : n ≤ 2 * n) i).trans
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2 * n) hi)
  exact Nat.mul_le_mul hp (Nat.pow_le_pow_right hE hj)

theorem encode_capacity (n coefficient exponent confidence : ℕ) (hn : 0 < n) (values : List ℕ)
    (h : ∀ value ∈ values, value ≤ valueCapacity n coefficient exponent confidence) :
    ∃ encoded : List (Fin (2 ^ registerBits n coefficient exponent confidence)),
      encoded.map Fin.val = values ∧ encoded.length = values.length := by
  induction values with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons value values ih =>
      obtain ⟨encoded, he, hl⟩ := ih (by intro v hv; exact h v (List.mem_cons_of_mem _ hv))
      have hv := (h value (by simp)).trans_lt (capacity_binary n coefficient exponent confidence hn)
      exact ⟨⟨value, hv⟩ :: encoded, by simp [he], by simp [hl]⟩

end StreamingSSSP.Hopset.Measured
