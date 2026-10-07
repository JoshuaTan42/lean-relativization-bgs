import Relativization.Oracle

/-!
# The queries of a run

`OracleFinTM2.queries A l t` is the finite set of query strings asked during the first `t` steps
of the run on `l` under `A` (at most `t` of them, `card_queries_le`); each has length at most
`l.length + t * tm.depth` (`length_le_of_mem_queries`, L3).

`iter_congr_queries` (L4') is the instance of the sharp locality lemma L4
(`OracleFinTM2.iter_congr`) the stage construction uses: two oracles that agree on
`tm.queries A l t` give the same run for every `n ≤ t` steps, and the same outputs within `t`
steps (`outputsInTime_congr_queries`, L6').
-/

namespace Relativization

open Turing Function

namespace OracleFinTM2

variable (tm : OracleFinTM2)

/-- The query asked at step `j` of the run on `l` under `A` (`[]` once the run has stopped). -/
noncomputable def queryAt (A : Oracle) (l : List (tm.Γ tm.k₀)) (j : ℕ) : List Bool :=
  (((flip bind (tm.step A))^[j] (some (tm.initList l))).map tm.query).getD []

/-- The queries asked during the first `t` steps of the run on `l` under `A` (together with the
junk value `[]`): at most `t` strings. -/
noncomputable def queries (A : Oracle) (l : List (tm.Γ tm.k₀)) (t : ℕ) : Finset (List Bool) :=
  (Finset.range t).image (tm.queryAt A l)

theorem card_queries_le (A : Oracle) (l : List (tm.Γ tm.k₀)) (t : ℕ) :
    (tm.queries A l t).card ≤ t :=
  Finset.card_image_le.trans (by rw [Finset.card_range])

theorem query_mem_queries {A : Oracle} {l : List (tm.Γ tm.k₀)} {t j : ℕ} (hj : j < t) {d : tm.Cfg}
    (hd : (flip bind (tm.step A))^[j] (some (tm.initList l)) = some d) :
    tm.query d ∈ tm.queries A l t :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, by rw [queryAt, hd]; rfl⟩

/-- **L3** for the query set: every query asked during the first `t` steps has length at most
`l.length + t * tm.depth`. -/
theorem length_le_of_mem_queries {A : Oracle} {l : List (tm.Γ tm.k₀)} {t : ℕ} {z : List Bool}
    (hz : z ∈ tm.queries A l t) : z.length ≤ l.length + t * tm.depth := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
  have hj' := Finset.mem_range.mp hj
  unfold queryAt
  cases hd : (flip bind (tm.step A))^[j] (some (tm.initList l)) with
  | none => simp
  | some d =>
      rw [Option.map_some, Option.getD_some]
      have h₁ := tm.query_length_iter A j _ d hd
      have h₂ := tm.query_initList_length_le l
      have h₃ : j * tm.depth ≤ t * tm.depth := Nat.mul_le_mul_right _ hj'.le
      omega

/-- **L4'.** Two oracles that agree on every query asked during the first `t` steps of the run
under `A` give the same run for every `n ≤ t` steps. -/
theorem iter_congr_queries {A A' : Oracle} (l : List (tm.Γ tm.k₀)) (t : ℕ)
    (h : ∀ z ∈ tm.queries A l t, (z ∈ A ↔ z ∈ A')) {n : ℕ} (hn : n ≤ t) :
    (flip bind (tm.step A))^[n] (some (tm.initList l)) =
      (flip bind (tm.step A'))^[n] (some (tm.initList l)) :=
  tm.iter_congr n _ fun _ hj _ hd => h _ (tm.query_mem_queries (lt_of_lt_of_le hj hn) hd)

/-- **L6'.** Under the hypothesis of L4', the machine outputs `l'` on `l` within `t` steps under
`A` iff it does under `A'`. -/
theorem outputsInTime_congr_queries {A A' : Oracle} (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) (t : ℕ) (h : ∀ z ∈ tm.queries A l t, (z ∈ A ↔ z ∈ A')) :
    Nonempty (OTM2OutputsInTime A tm l l' t) ↔ Nonempty (OTM2OutputsInTime A' tm l l' t) :=
  ⟨fun ⟨o⟩ => ⟨{ steps := o.steps
                 evals_in_steps :=
                   (tm.iter_congr_queries l t h o.steps_le_m).symm.trans o.evals_in_steps
                 steps_le_m := o.steps_le_m }⟩,
    fun ⟨o⟩ => ⟨{ steps := o.steps
                  evals_in_steps :=
                    (tm.iter_congr_queries l t h o.steps_le_m).trans o.evals_in_steps
                  steps_le_m := o.steps_le_m }⟩⟩

end OracleFinTM2

end Relativization
