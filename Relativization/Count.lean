import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-!
# Counting (B3)

* `exists_free` (B3a): a set of fewer than `2^n` binary strings misses some `u ++ 0^n` with
  `|u| = n`;
* `eventually_eval_lt_two_pow` (B3b): every polynomial over `ℕ` is eventually below `2^n`;
  `exists_len` is the form the stage construction uses (a length above any bound with
  `p.eval n < 2^n`).
-/

namespace Relativization

open Finset

/-! ### B3a: the free string -/

/-- The `2^n` strings `u ++ 0^n` with `|u| = n`. -/
def padded (n : ℕ) : Finset (List Bool) :=
  univ.image fun f : Fin n → Bool => List.ofFn f ++ List.replicate n false

theorem card_padded (n : ℕ) : (padded n).card = 2 ^ n := by
  rw [padded, card_image_of_injective _ fun f g h => List.ofFn_injective (List.append_cancel_right h),
    card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **B3a.** Fewer than `2^n` strings miss some `u ++ 0^n` with `|u| = n`. -/
theorem exists_free (n : ℕ) (S : Finset (List Bool)) (h : S.card < 2 ^ n) :
    ∃ u : List Bool, u.length = n ∧ u ++ List.replicate n false ∉ S := by
  by_contra hcon
  have hsub : padded n ⊆ S := by
    intro z hz
    obtain ⟨f, -, rfl⟩ := mem_image.mp hz
    by_contra hz'
    exact hcon ⟨List.ofFn f, List.length_ofFn, hz'⟩
  have := card_le_card hsub
  rw [card_padded] at this
  omega

/-! ### B3b: polynomials against `2^n` -/

/-- `p(n) ≤ p(1) · n^(deg p)` for `n ≥ 1`; `p(1)` is the sum of the coefficients. -/
theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, sum_mul]
  refine sum_le_sum fun i hi => ?_
  rw [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn (Nat.lt_succ_iff.mp (mem_range.mp hi)))

/-- `C · n^d < 2^n` once `n ≥ C · (d+1)^(d+1)`. With `m = n / (d+1)`:
`C n^d ≤ C (d+1)^d (m+1)^d ≤ m (m+1)^d < (m+1)^(d+1) ≤ (2^m)^(d+1) ≤ 2^n`. -/
theorem mul_pow_lt_two_pow (C d : ℕ) {n : ℕ} (hn : C * (d + 1) ^ (d + 1) ≤ n) :
    C * n ^ d < 2 ^ n := by
  set m := n / (d + 1) with hm
  have hd : 0 < d + 1 := Nat.succ_pos d
  have h₁ : C * (d + 1) ^ d ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le hd, mul_assoc, ← pow_succ]
    exact hn
  have h₂ : n < (d + 1) * (m + 1) := Nat.lt_mul_div_succ n hd
  have h₃ : m * (d + 1) ≤ n := Nat.div_mul_le_self n (d + 1)
  have h₄ : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h₅ : 0 < (m + 1) ^ d := Nat.pow_pos (Nat.succ_pos m)
  calc C * n ^ d ≤ C * ((d + 1) * (m + 1)) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h₂.le d)
    _ = C * (d + 1) ^ d * (m + 1) ^ d := by rw [mul_pow, mul_assoc]
    _ ≤ m * (m + 1) ^ d := Nat.mul_le_mul_right _ h₁
    _ < (m + 1) * (m + 1) ^ d := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self m) h₅
    _ = (m + 1) ^ (d + 1) := by rw [pow_succ, mul_comm]
    _ ≤ (2 ^ m) ^ (d + 1) := Nat.pow_le_pow_left h₄ _
    _ = 2 ^ (m * (d + 1)) := by rw [← pow_mul]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h₃

/-- **B3b.** Every polynomial over `ℕ` is eventually below `2^n`. -/
theorem eventually_eval_lt_two_pow (p : Polynomial ℕ) : ∃ N, ∀ n, N ≤ n → p.eval n < 2 ^ n :=
  ⟨p.eval 1 * (p.natDegree + 1) ^ (p.natDegree + 1) + 1, fun n hn =>
    calc p.eval n ≤ p.eval 1 * n ^ p.natDegree := eval_le_eval_one_mul_pow p (by omega)
      _ < 2 ^ n := mul_pow_lt_two_pow _ _ (by omega)⟩

/-- **B3b**, the form the stages use: a length above any bound with `p(n) < 2^n`. -/
theorem exists_len (ℓ : ℕ) (p : Polynomial ℕ) : ∃ n, ℓ < n ∧ p.eval n < 2 ^ n :=
  let ⟨N, hN⟩ := eventually_eval_lt_two_pow p
  ⟨max ℓ N + 1, by omega, hN _ (by omega)⟩

end Relativization
