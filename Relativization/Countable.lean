import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.W.Basic
import Mathlib.Data.Countable.Basic

/-!
# Countability of TM2 statements

`TM2.Stmt.countable` (N1): the statements over countable stack indices and labels, finitely many
states and finite stack alphabets form a countable type. A statement is a finite tree; `toW`
writes it as a `WType` whose nodes carry the constructor's data, `ofW` reads it back, and Mathlib
provides the encoding of `WType`s.

Finiteness of the alphabets is needed: `pop k f q` carries `f : σ → Option (Γ k) → σ`, and
`Option ℕ → Bool` is uncountable.
-/

namespace Relativization

open Turing Function

namespace StmtCountable

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Node labels of the tree of a statement: the data of each constructor. -/
abbrev Node (Γ : K → Type) (Λ σ : Type) : Type :=
  (Σ k, σ → Γ k) ⊕ (Σ k, σ → Option (Γ k) → σ) ⊕ (Σ k, σ → Option (Γ k) → σ) ⊕ (σ → σ) ⊕
    (σ → Bool) ⊕ (σ → Λ) ⊕ Unit

/-- Number of children of each node. -/
def arity : Node Γ Λ σ → Type
  | .inl _ => Unit
  | .inr (.inl _) => Unit
  | .inr (.inr (.inl _)) => Unit
  | .inr (.inr (.inr (.inl _))) => Unit
  | .inr (.inr (.inr (.inr (.inl _)))) => Bool
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => Empty
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => Empty

instance arityFintype : ∀ n : Node Γ Λ σ, Fintype (arity n)
  | .inl _ => inferInstanceAs (Fintype Unit)
  | .inr (.inl _) => inferInstanceAs (Fintype Unit)
  | .inr (.inr (.inl _)) => inferInstanceAs (Fintype Unit)
  | .inr (.inr (.inr (.inl _))) => inferInstanceAs (Fintype Unit)
  | .inr (.inr (.inr (.inr (.inl _)))) => inferInstanceAs (Fintype Bool)
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => inferInstanceAs (Fintype Empty)
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => inferInstanceAs (Fintype Empty)

instance arityEncodable : ∀ n : Node Γ Λ σ, Encodable (arity n)
  | .inl _ => inferInstanceAs (Encodable Unit)
  | .inr (.inl _) => inferInstanceAs (Encodable Unit)
  | .inr (.inr (.inl _)) => inferInstanceAs (Encodable Unit)
  | .inr (.inr (.inr (.inl _))) => inferInstanceAs (Encodable Unit)
  | .inr (.inr (.inr (.inr (.inl _)))) => inferInstanceAs (Encodable Bool)
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => inferInstanceAs (Encodable Empty)
  | .inr (.inr (.inr (.inr (.inr (.inr _))))) => inferInstanceAs (Encodable Empty)

/-- A statement as a tree. -/
def toW : TM2.Stmt Γ Λ σ → WType (arity (Γ := Γ) (Λ := Λ) (σ := σ))
  | .push k f q => ⟨.inl ⟨k, f⟩, fun _ => toW q⟩
  | .peek k f q => ⟨.inr (.inl ⟨k, f⟩), fun _ => toW q⟩
  | .pop k f q => ⟨.inr (.inr (.inl ⟨k, f⟩)), fun _ => toW q⟩
  | .load a q => ⟨.inr (.inr (.inr (.inl a))), fun _ => toW q⟩
  | .branch f q₁ q₂ =>
      ⟨.inr (.inr (.inr (.inr (.inl f)))), fun b => cond b (toW q₁) (toW q₂)⟩
  | .goto f => ⟨.inr (.inr (.inr (.inr (.inr (.inl f))))), Empty.elim⟩
  | .halt => ⟨.inr (.inr (.inr (.inr (.inr (.inr ()))))), Empty.elim⟩

/-- A tree as a statement. -/
def ofW : WType (arity (Γ := Γ) (Λ := Λ) (σ := σ)) → TM2.Stmt Γ Λ σ
  | ⟨.inl ⟨k, f⟩, g⟩ => .push k f (ofW (g ()))
  | ⟨.inr (.inl ⟨k, f⟩), g⟩ => .peek k f (ofW (g ()))
  | ⟨.inr (.inr (.inl ⟨k, f⟩)), g⟩ => .pop k f (ofW (g ()))
  | ⟨.inr (.inr (.inr (.inl a))), g⟩ => .load a (ofW (g ()))
  | ⟨.inr (.inr (.inr (.inr (.inl f)))), g⟩ => .branch f (ofW (g true)) (ofW (g false))
  | ⟨.inr (.inr (.inr (.inr (.inr (.inl f))))), _⟩ => .goto f
  | ⟨.inr (.inr (.inr (.inr (.inr (.inr _))))), _⟩ => .halt

theorem ofW_toW (q : TM2.Stmt Γ Λ σ) : ofW (toW q) = q := by
  induction q with
  | push k f q ih => rw [toW, ofW, ih]
  | peek k f q ih => rw [toW, ofW, ih]
  | pop k f q ih => rw [toW, ofW, ih]
  | load a q ih => rw [toW, ofW, ih]
  | branch f q₁ q₂ ih₁ ih₂ => rw [toW, ofW]; exact congrArg₂ _ ih₁ ih₂
  | goto f => rfl
  | halt => rfl

theorem toW_injective : Injective (toW (Γ := Γ) (Λ := Λ) (σ := σ)) :=
  LeftInverse.injective ofW_toW

end StmtCountable

open StmtCountable in
/-- **N1.** Statements over countable stack indices and labels, finitely many states and finite
alphabets form a countable type. -/
instance TM2.Stmt.countable {K : Type} {Γ : K → Type} {Λ σ : Type} [Countable K]
    [∀ k, Finite (Γ k)] [Countable Λ] [Finite σ] : Countable (TM2.Stmt Γ Λ σ) :=
  haveI : Encodable (Node Γ Λ σ) := Encodable.ofCountable _
  toW_injective.countable

end Relativization
