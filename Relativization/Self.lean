import Relativization.Classes

/-!
# `A ∈ P^A`

The only oracle machine written by hand: `selfTM` has a single binary stack that is the input,
output and query stack at once. Its first step sees the oracle's verdict on the input itself and
records it in the label; it then empties the stack and pushes the verdict.

* `Self.selfTM_outputs`: on input `w` with oracle `A` the machine outputs `[decide (w ∈ A)]` in
  `w.length + 3` steps;
* `oracle_inP` (T3): `A ∈ P^A`.
-/

namespace Relativization

open Turing StateTransition Function Computability Millennium

namespace Self

/-- Labels: `none` = start; `some (inl a)` = empty the stack, verdict `a`; `some (inr a)` = write
the verdict `a`. -/
abbrev QΛ := Option (Bool ⊕ Bool)

/-- The program. The state is a flag: "the last pop found a symbol". -/
def prog : QΛ → Bool → TM2.Stmt (fun _ : Unit => Bool) QΛ Bool
  | none, b => .goto fun _ => some (.inl b)
  | some (.inl a), _ =>
      .pop () (fun _ o => o.isSome)
        (.goto fun s => if s then some (.inl a) else some (.inr a))
  | some (.inr a), _ => .push () (fun _ => a) .halt

/-- The machine deciding its own oracle. -/
def selfTM : OracleFinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := QΛ
  main := none
  σ := Bool
  initialState := false
  kq := ()
  queryAlphabet := Equiv.refl Bool
  m := prog

/-- A configuration of `selfTM`. -/
abbrev cfg (l : Option QΛ) (s : Bool) (w : List Bool) : selfTM.Cfg :=
  ⟨l, s, fun _ => w⟩

theorem initList_eq (w : List Bool) : selfTM.initList w = cfg (some none) false w := by
  rfl

theorem haltList_eq (w : List Bool) : selfTM.haltList w = cfg none false w := by
  rfl

open Classical in
/-- The first step records the oracle's verdict on the input. -/
theorem step_start (A : Oracle) (w : List Bool) :
    selfTM.step A (cfg (some none) false w) =
      some (cfg (some (some (.inl (decide (w ∈ A))))) false w) := by
  have hq : selfTM.query (cfg (some none) false w) = w := List.map_id w
  simp only [OracleFinTM2.step, hq]
  rfl

theorem step_drain_cons (A : Oracle) (a s x : Bool) (w : List Bool) :
    selfTM.step A (cfg (some (some (.inl a))) s (x :: w)) =
      some (cfg (some (some (.inl a))) true w) := by
  rfl

theorem step_drain_nil (A : Oracle) (a s : Bool) :
    selfTM.step A (cfg (some (some (.inl a))) s []) =
      some (cfg (some (some (.inr a))) false []) := by
  rfl

theorem step_emit (A : Oracle) (a s : Bool) :
    selfTM.step A (cfg (some (some (.inr a))) s []) = some (cfg none s [a]) := by
  rfl

/-- Emptying the stack takes one step per symbol. -/
theorem drain (A : Oracle) (a : Bool) (w : List Bool) (s : Bool) :
    (flip bind (selfTM.step A))^[w.length + 1] (some (cfg (some (some (.inl a))) s w)) =
      some (cfg (some (some (.inr a))) false []) := by
  induction w generalizing s with
  | nil => rw [List.length_nil, iter_step (step_drain_nil A a s)]; rfl
  | cons x w ih => rw [List.length_cons, iter_step (step_drain_cons A a s x w), ih]

open Classical in
/-- `selfTM` with oracle `A` outputs `[decide (w ∈ A)]` on input `w` in `w.length + 3` steps. -/
theorem selfTM_run (A : Oracle) (w : List Bool) :
    (flip bind (selfTM.step A))^[w.length + 3] (some (selfTM.initList w)) =
      some (selfTM.haltList [decide (w ∈ A)]) := by
  rw [initList_eq, haltList_eq,
    show w.length + 3 = 1 + ((w.length + 1) + 1) by omega, iterate_add_apply,
    iterate_add_apply, iter_step (step_start A w), iterate_zero, id, drain,
    iter_step (step_emit A _ _)]
  rfl

open Classical in
/-- Time-bounded form of `selfTM_run`. -/
noncomputable def selfTM_outputs (A : Oracle) (w : List Bool) :
    OTM2OutputsInTime A selfTM w (some [decide (w ∈ A)]) (w.length + 3) where
  steps := w.length + 3
  evals_in_steps := selfTM_run A w
  steps_le_m := le_rfl

end Self

open Classical in
/-- **T3.** Every oracle is in `P` relative to itself. -/
theorem oracle_inP (A : Oracle) : InP A (fin_encoding_string Bool) (· ∈ A) := by
  refine ⟨fun w => decide (w ∈ A),
    { tm := Self.selfTM
      inputAlphabet := Equiv.refl Bool
      outputAlphabet := Equiv.refl Bool
      time := Polynomial.X + Polynomial.C 3
      outputsFun := fun w => ?_ }, fun w => by simp⟩
  have h := Self.selfTM_outputs A w
  have key : ∀ (l l' : List Bool) (n : ℕ), l = w → l' = [decide (w ∈ A)] → w.length + 3 ≤ n →
      OTM2OutputsInTime A Self.selfTM l (some l') n := by
    rintro l l' n rfl rfl hn
    exact ⟨h.toEvalsTo, h.steps_le_m.trans hn⟩
  refine key _ _ _ ?_ ?_ ?_
  · exact List.map_id w
  · rfl
  · simp [fin_encoding_string]

end Relativization
