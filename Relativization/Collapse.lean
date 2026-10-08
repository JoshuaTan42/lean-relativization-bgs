import Relativization.Univ
import Relativization.Pad
import Relativization.Halt
import Relativization.Self
import Relativization.Comp

/-!
# The collapse: `P^A = NP^A` for `A = univOracle` (A5, A6)

Theorem 7 of `NOTES.md` §5.7, in the form of §4.13. For `L ∈ NP^A` with verifier code `i`
(N4v') and polynomial `p`, choose `c', d` with `(n + c')^d ≥ μ_i(n) + (D_i + 1) · p(μ_i(n))`
(`eval_le_pow`, ported from PvsNP). Then the budget of `padFun i c' d w = frame i ((|w| + c')^d)
w.reverse` is at least `p(μ_i(|w|))`, so under `A` the coded verifier halts within the budget on
every short certificate with the verifier's answer, and by unique output (F4')

* `exists_pad_reduction` (**A5**): `L w ↔ padFun i c' d w ∈ univOracle` for all `w`.

The pad is a plain polynomial-time function (A4) and `A ∈ P^A` (T3), so `oracleComp` (F7) gives
`L ∈ P^A` (`inP_of_pad_reduction`, `inNP_subset_inP`); with T4,

* `univOracle_pEqNP` (**A6**): `PEqNP univOracle`.

`pow_weaken` and `eval_le_pow` are PvsNP `Pkg.lean` 391–416, verbatim.
-/

namespace Relativization

open Turing Function Computability Millennium Polynomial

/-! ## [POLY] Every polynomial is bounded by some `(j + c)^e` (PvsNP `Pkg.lean`, verbatim) -/

theorem pow_weaken {j c e c' e' : ℕ} (hc : 1 ≤ c) (h1 : c ≤ c') (h2 : e ≤ e') :
    (j + c) ^ e ≤ (j + c') ^ e' :=
  (Nat.pow_le_pow_left (by omega) e).trans (Nat.pow_le_pow_right (by omega) h2)

theorem eval_le_pow (p : Polynomial ℕ) : ∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c) ^ e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨c1, e1, hc1, h1⟩ := hp
      obtain ⟨c2, e2, hc2, h2⟩ := hq
      refine ⟨c1 + c2, e1 + e2 + 1, by omega, fun j => ?_⟩
      have a1 := (h1 j).trans
        (pow_weaken (j := j) hc1 (Nat.le_add_right c1 c2) (Nat.le_add_right e1 e2))
      have a2 := (h2 j).trans
        (pow_weaken (j := j) hc2 (Nat.le_add_left c2 c1) (Nat.le_add_left e2 e1))
      have h2le : 2 ≤ j + (c1 + c2) := by omega
      rw [Polynomial.eval_add, pow_succ]
      calc p.eval j + q.eval j
          ≤ (j + (c1 + c2)) ^ (e1 + e2) + (j + (c1 + c2)) ^ (e1 + e2) := Nat.add_le_add a1 a2
        _ = (j + (c1 + c2)) ^ (e1 + e2) * 2 := by ring
        _ ≤ (j + (c1 + c2)) ^ (e1 + e2) * (j + (c1 + c2)) := Nat.mul_le_mul_left _ h2le
  | monomial n a =>
      refine ⟨a + 1, n + 1, by omega, fun j => ?_⟩
      rw [Polynomial.eval_monomial, pow_succ]
      calc a * j ^ n ≤ (j + (a + 1)) * (j + (a + 1)) ^ n :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) n)
        _ = _ := mul_comm _ _

/-! ## [TIME] Time weakening -/

/-- An output within `t` steps is an output within any `t' ≥ t` steps. -/
def OTM2OutputsInTime.mono {A : Oracle} {tm : OracleFinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {t t' : ℕ} (h : OTM2OutputsInTime A tm l l' t)
    (ht : t ≤ t') : OTM2OutputsInTime A tm l l' t' :=
  ⟨h.toEvalsTo, h.steps_le_m.trans ht⟩

namespace Collapse

/-! ## [EXP] The exponent pair and the budget -/

/-- `μ_i` as a polynomial: `X + 1 + X^{k_i}`. -/
noncomputable def muPoly (i : ℕ) : Polynomial ℕ := X + 1 + X ^ (vEnum i).k

theorem muPoly_eval (i n : ℕ) : (muPoly i).eval n = Univ.mu i n := by
  simp [muPoly, Univ.mu]

/-- `μ_i + (D_i + 1) · (p ∘ μ_i)`: the polynomial the time parameter `T` must dominate (§5.7). -/
noncomputable def padPoly (i : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  muPoly i + C ((Univ.M i).depth + 1) * p.comp (muPoly i)

theorem padPoly_eval (i : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    (padPoly i p).eval n = Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n) := by
  simp [padPoly, muPoly_eval]

/-- The exponent pair: `T(n) = (n + c')^d ≥ μ_i(n) + (D_i + 1) · p(μ_i(n))` for every `n`. -/
theorem exists_exponents (i : ℕ) (p : Polynomial ℕ) :
    ∃ c' d : ℕ, ∀ n,
      Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n) ≤ (n + c') ^ d := by
  obtain ⟨c', d, -, h⟩ := eval_le_pow (padPoly i p)
  exact ⟨c', d, fun n => by rw [← padPoly_eval]; exact h n⟩

/-- With such `c', d`, the budget of `frame i ((n + c')^d) v`, `|v| = n`, is at least
`p(μ_i(n))`. -/
theorem eval_le_budget {i c' d : ℕ} {p : Polynomial ℕ}
    (hT : ∀ n, Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n) ≤ (n + c') ^ d)
    (n : ℕ) : p.eval (Univ.mu i n) ≤ Univ.budget i ((n + c') ^ d) n := by
  unfold Univ.budget
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos _), mul_comm]
  exact Nat.le_sub_of_add_le' (hT n)

/-! ## [ACC] Membership of the pad in `A` -/

/-- `Acc` at a reversed string, the double reversal removed. -/
theorem Acc_reverse (O : Oracle) (i T : ℕ) (w : List Bool) :
    Univ.Acc O i T w.reverse ↔ ∃ y : List (Fin (vEnum i).g), y.length ≤ w.length ^ (vEnum i).k ∧
      Nonempty (OTM2OutputsInTime O (Univ.M i) (Univ.input i w y)
        (some [(vEnum i).outE.symm true]) (Univ.budget i T w.length)) := by
  simp only [Univ.Acc, List.reverse_reverse, List.length_reverse]

/-- Membership of the pad in `A`: (†) `Univ.mem_univOracle`, `Univ.Phi_frame`, `Acc_reverse`. -/
theorem padFun_mem_iff (i c' d : ℕ) (w : List Bool) :
    padFun i c' d w ∈ univOracle ↔ ∃ y : List (Fin (vEnum i).g),
      y.length ≤ w.length ^ (vEnum i).k ∧
      Nonempty (OTM2OutputsInTime univOracle (Univ.M i) (Univ.input i w y)
        (some [(vEnum i).outE.symm true]) (Univ.budget i ((w.length + c') ^ d) w.length)) := by
  rw [Univ.mem_univOracle, padFun, Univ.Phi_frame, Acc_reverse]

end Collapse

open Collapse

/-! ## [RED] The reduction (A5) -/

/-- **A5** (the claim of Theorem 7, §5.7). Every `L ∈ NP^A`, `A = univOracle`, is reduced to
`A` by some pad: `L w ↔ padFun i c' d w ∈ A`. -/
theorem exists_pad_reduction (L : Language (List Bool))
    (hL : InNP univOracle (fin_encoding_string Bool) L) :
    ∃ i c' d : ℕ, ∀ w, L w ↔ padFun i c' d w ∈ univOracle := by
  obtain ⟨Γ₁, _, R, k, ⟨f, h, hR⟩, hLR⟩ := hL
  obtain ⟨i, ρ, hk, hsim⟩ := exists_vcode_of_verifier h k
  subst hk
  obtain ⟨c', d, hT⟩ := exists_exponents i h.time
  refine ⟨i, c', d, fun w => ?_⟩
  -- item 3: under `A`, the coded verifier outputs `[f (w, y)]` on `w # ρ(y)` within the budget
  have hout : ∀ y : List Γ₁, y.length ≤ w.length ^ (vEnum i).k →
      Nonempty (OTM2OutputsInTime univOracle (Univ.M i) (Univ.input i w (y.map ρ))
        (some [(vEnum i).outE.symm (f (w, y))])
        (Univ.budget i ((w.length + c') ^ d) w.length)) := by
    intro y hy
    refine (hsim univOracle w y (f (w, y)) _).mp ⟨(h.outputsFun (w, y)).mono ?_⟩
    refine (Comp.eval_mono h.time ?_).trans (eval_le_budget hT w.length)
    refine (pair_encoding.length_eq _ _ _).le.trans ?_
    show w.length + 1 + y.length ≤ Univ.mu i w.length
    unfold Univ.mu
    omega
  -- F4': it outputs `[true]` within the budget iff `R w y`
  have hacc : ∀ y : List Γ₁, y.length ≤ w.length ^ (vEnum i).k →
      (Nonempty (OTM2OutputsInTime univOracle (Univ.M i) (Univ.input i w (y.map ρ))
        (some [(vEnum i).outE.symm true])
        (Univ.budget i ((w.length + c') ^ d) w.length)) ↔ R w y) := by
    intro y hy
    obtain ⟨hB⟩ := hout y hy
    have hR' : R w y ↔ f (w, y) = true := hR (w, y)
    rw [OTM2OutputsInTime.bool_iff (tm := Univ.M i) (vEnum i).outE hB true, hR']
    exact eq_comm
  -- items 4–5: transport the certificate along `ρ`
  have hLR' : L w ↔ ∃ y : List Γ₁, y.length ≤ w.length ^ (vEnum i).k ∧ R w y := hLR w
  rw [padFun_mem_iff, hLR']
  constructor
  · rintro ⟨y, hy, hRy⟩
    exact ⟨y.map ρ, by simpa using hy, (hacc y hy).mpr hRy⟩
  · rintro ⟨y', hy', hB⟩
    refine ⟨y'.map ρ.symm, by simpa using hy', ?_⟩
    have e : (y'.map ρ.symm).map ρ = y' := by simp
    rw [← hacc (y'.map ρ.symm) (by simpa using hy'), e]
    exact hB

/-! ## [COL] `NP^A ⊆ P^A` and `P^A = NP^A` (A6) -/

/-- A pad reduction puts `L` in `P^A`: the pad machine (A4) followed by the self-decider (T3),
composed by F7. -/
theorem inP_of_pad_reduction {L : Language (List Bool)} {i c' d : ℕ}
    (h : ∀ w, L w ↔ padFun i c' d w ∈ univOracle) :
    InP univOracle (fin_encoding_string Bool) L := by
  obtain ⟨g, hg, hgA⟩ := oracle_inP univOracle
  exact ⟨g ∘ padFun i c' d, oracleComp univOracle (Pad.padComputable i c' d) hg,
    fun w => (h w).trans (hgA _)⟩

/-- Theorem 7 of §5.7: `NP^A ⊆ P^A` for `A = univOracle`. -/
theorem inNP_subset_inP (L : Language (List Bool)) :
    InNP univOracle (fin_encoding_string Bool) L → InP univOracle (fin_encoding_string Bool) L :=
  fun hL => (exists_pad_reduction L hL).elim fun _ h => h.elim fun _ h => h.elim fun _ h =>
    inP_of_pad_reduction h

/-- **A6.** `P^A = NP^A` for `A = univOracle`. -/
theorem univOracle_pEqNP : PEqNP univOracle :=
  fun L => ⟨inP_subset_inNP univOracle Bool L, inNP_subset_inP L⟩

end Relativization
