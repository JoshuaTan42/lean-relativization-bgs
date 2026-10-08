import Relativization.Collapse
import Relativization.Stage

/-!
# The Baker-Gill-Solovay theorem (T5, T6, T7)

* `collapse` (**T5**): there is an oracle `A` with `P^A = NP^A`; the witness is `univOracle`
  (`univOracle_pEqNP`, A6);
* `separation` (**T6**): there is an oracle `B` with `P^B ≠ NP^B`; the witness is `sepOracle`
  (`sepOracle_not_pEqNP`, B6);
* `baker_gill_solovay` (**T7**): both, with the one predicate `PEqNP : Oracle → Prop` of
  `Relativization/Classes.lean` and the one type `Oracle := Set (List Bool)` in both conjuncts.

`NOTES.md` §4.13 spells the statements out in terms of the definitions of `Classes.lean` and
lists what makes them weaker than, or different from, the textbook theorem.
-/

namespace Relativization

/-- **T5.** There is an oracle `A` with `P^A = NP^A`. -/
theorem collapse : ∃ A : Oracle, PEqNP A :=
  ⟨univOracle, univOracle_pEqNP⟩

/-- **T6.** There is an oracle `B` with `P^B ≠ NP^B`. -/
theorem separation : ∃ B : Oracle, ¬ PEqNP B :=
  ⟨sepOracle, sepOracle_not_pEqNP⟩

/-- **T7 (Baker-Gill-Solovay).** There is an oracle `A` with `P^A = NP^A` and an oracle `B` with
`P^B ≠ NP^B`. -/
theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B) :=
  ⟨collapse, separation⟩

end Relativization
