import Relativization.Oracle
import Problems.PVersusNP.Millennium

/-!
# Relativized `P` and `NP`

Definition D3 of `NOTES.md`: `InP A`, `InNP A`, `PEqNP A`, `ClassEquality A`. They mirror
`Millennium.InPolynomialTime`, `Millennium.InNondeterministicPolynomialTime` and
`Millennium.ClayPVersusNP.Formulations.ClassEquality` word for word, with an oracle machine in
place of a plain one. `Language`, `pair_encoding` and `fin_encoding_string` are the `Millennium`
ones.
-/

namespace Relativization

open Turing Computability Millennium

/-- `L ∈ P^A`: some polynomial-time oracle machine with oracle `A` decides `L`. -/
def InP (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_ : OTM2ComputableInPolyTime A ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

/-- `L ∈ NP^A`: membership has polynomially bounded certificates checked in `P^A`. -/
def InNP (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    InP A (pair_encoding ea (fin_encoding_string Γ₁)) (fun p => R p.1 p.2) ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y

/-- `P^A = NP^A` for languages over the binary alphabet. -/
def PEqNP (A : Oracle) : Prop :=
  ∀ L : Language (List Bool),
    InP A (fin_encoding_string Bool) L ↔ InNP A (fin_encoding_string Bool) L

/-- Relativized `Millennium.ClayPVersusNP.Formulations.ClassEquality`: `P^A = NP^A` for languages
over every finite alphabet with at least two symbols. -/
def ClassEquality (A : Oracle) : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InP A (fin_encoding_string alphabet) L ↔ InNP A (fin_encoding_string alphabet) L

end Relativization
