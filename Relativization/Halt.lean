import Relativization.Oracle

/-!
# Unique output

Halting configurations are terminal, so a machine has at most one output on an input, whatever
the time bounds (F4; Lemma 4 of `NOTES.md` §5.2).

* `OracleFinTM2.step_haltList`: a halting configuration has no successor;
* `OracleFinTM2.haltList_injective`;
* `OTM2OutputsInTime.output_unique` (F4): two outputs on the same input are equal, and are
  reached at the same step;
* `OTM2OutputsInTime.outputs_iff_eq`, `OTM2OutputsInTime.bool_iff` (F4'): given one output,
  another candidate is an output iff it is that one.
-/

namespace Relativization

open Turing StateTransition Function

namespace OracleFinTM2

variable (tm : OracleFinTM2)

/-- Halting configurations are terminal. -/
theorem step_haltList (A : Oracle) (o : List (tm.Γ tm.k₁)) : tm.step A (tm.haltList o) = none :=
  rfl

theorem haltList_stk_self (o : List (tm.Γ tm.k₁)) : (tm.haltList o).stk tm.k₁ = o := by
  simp [haltList, Turing.haltList, toFinTM2]

theorem haltList_injective : Injective tm.haltList := by
  intro o o' h
  have := congrArg (fun c : tm.Cfg => c.stk tm.k₁) h
  simpa only [haltList_stk_self] using this

end OracleFinTM2

/-- A run that has reached a terminal configuration cannot go on. -/
theorem iter_eq_some_of_terminal {α : Type} {f : α → Option α} {c d : α} (hc : f c = none)
    {n : ℕ} (h : (flip bind f)^[n] (some c) = some d) : n = 0 ∧ d = c := by
  cases n with
  | zero => exact ⟨rfl, (Option.some.inj h).symm⟩
  | succ n =>
      rw [iterate_succ_apply] at h
      change (flip bind f)^[n] (f c) = some d at h
      rw [hc, iter_none] at h
      cases h

section unique

variable {A : Oracle} {tm : OracleFinTM2} {l : List (tm.Γ tm.k₀)}

theorem OracleFinTM2.run_unique_aux {o o' : List (tm.Γ tm.k₁)} {s s' : ℕ}
    (hs : (flip bind (tm.step A))^[s] (some (tm.initList l)) = some (tm.haltList o))
    (hs' : (flip bind (tm.step A))^[s'] (some (tm.initList l)) = some (tm.haltList o'))
    (hle : s ≤ s') : o = o' ∧ s = s' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.add_comm, iterate_add_apply, hs] at hs'
  obtain ⟨hd, hdo⟩ := iter_eq_some_of_terminal (tm.step_haltList A o) hs'
  exact ⟨(tm.haltList_injective hdo).symm, by omega⟩

/-- **F4.** A machine has at most one output on an input, whatever the time bounds; and it is
reached at the same step. -/
theorem OTM2OutputsInTime.output_unique {o o' : List (tm.Γ tm.k₁)} {t t' : ℕ}
    (h : OTM2OutputsInTime A tm l (some o) t) (h' : OTM2OutputsInTime A tm l (some o') t') :
    o = o' ∧ h.steps = h'.steps := by
  have hs : (flip bind (tm.step A))^[h.steps] (some (tm.initList l)) = some (tm.haltList o) :=
    h.evals_in_steps
  have hs' : (flip bind (tm.step A))^[h'.steps] (some (tm.initList l)) =
      some (tm.haltList o') := h'.evals_in_steps
  rcases le_total h.steps h'.steps with hle | hle
  · exact OracleFinTM2.run_unique_aux hs hs' hle
  · obtain ⟨h1, h2⟩ := OracleFinTM2.run_unique_aux hs' hs hle
    exact ⟨h1.symm, h2.symm⟩

/-- **F4'.** Given one output within `t` steps, a candidate is an output within `t' ≥ t` steps
iff it is that output. -/
theorem OTM2OutputsInTime.outputs_iff_eq {o : List (tm.Γ tm.k₁)} {t : ℕ}
    (h : OTM2OutputsInTime A tm l (some o) t) (o' : List (tm.Γ tm.k₁)) {t' : ℕ} (ht : t ≤ t') :
    Nonempty (OTM2OutputsInTime A tm l (some o') t') ↔ o' = o := by
  constructor
  · rintro ⟨h'⟩
    exact (h'.output_unique h).1
  · rintro rfl
    exact ⟨⟨h.toEvalsTo, h.steps_le_m.trans ht⟩⟩

/-- **F4'**, for one-symbol outputs through an output alphabet equivalence: the form the
collapse proof uses. -/
theorem OTM2OutputsInTime.bool_iff {t : ℕ} {βΓ : Type} (ι : tm.Γ tm.k₁ ≃ βΓ) {b : βΓ}
    (h : OTM2OutputsInTime A tm l (some [ι.symm b]) t) (b' : βΓ) :
    Nonempty (OTM2OutputsInTime A tm l (some [ι.symm b']) t) ↔ b' = b := by
  rw [h.outputs_iff_eq _ le_rfl]
  constructor
  · intro e
    simp only [List.cons.injEq, and_true] at e
    exact ι.symm.injective e
  · rintro rfl
    rfl

end unique

end Relativization
