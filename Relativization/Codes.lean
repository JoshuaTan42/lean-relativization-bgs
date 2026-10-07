import Relativization.Classes
import Relativization.Normal
import Relativization.Countable
import Mathlib.Data.Finsupp.Encodable

/-!
# Codes: countable enumerations of deciders and verifiers

* `DCode`: a normal-form machine with binary input and output alphabets and a time polynomial
  (the requirements of the separation construction);
* `VCode`: a normal-form machine with input alphabet `Bool ⊕ Option (Fin g)` (the
  `pair_encoding` alphabet of `w#y` with certificates over `Fin g`), output alphabet `Bool`, and
  an exponent `k` (the codes of the collapse oracle, `NOTES.md` §5.3);
* N2: `NFMachine`, `DCode`, `VCode` are countable; `dEnum`, `vEnum` enumerate them;
* N4: every polynomial-time oracle decider has a `DCode` (`exists_dcode`,
  `exists_dcode_decides`), every oracle verifier has a `VCode` (`exists_vcode`,
  `exists_vcode_of_verifier`), running exactly like the original under every oracle.
-/

namespace Relativization

open Turing Function Computability Millennium

/-! ### Countability of the normal-form data -/

/-- Equivalences between types with countably many functions are countable. -/
instance equivCountable {α β : Type} [Countable (α → β)] : Countable (α ≃ β) :=
  Equiv.coe_fn_injective.countable

instance polynomialNatCountable : Countable (Polynomial ℕ) :=
  haveI : Countable (AddMonoidAlgebra ℕ ℕ) := inferInstanceAs (Countable (ℕ →₀ ℕ))
  (Polynomial.toFinsupp_injective (R := ℕ)).countable

namespace NFMachine

/-- The fields of a normal-form machine after the sizes, alphabets and stack indices. -/
abbrev Fiber (nK nΛ nσ : ℕ) (a : Fin nK → ℕ) (kq : Fin nK) : Type :=
  Fin nΛ × Fin nσ × (Fin (a kq) ≃ Bool) ×
    (Fin nΛ → Bool → TM2.Stmt (fun j => Fin (a j)) (Fin nΛ) (Fin nσ))

instance fiberCountable (nK nΛ nσ : ℕ) (a : Fin nK → ℕ) (kq : Fin nK) :
    Countable (Fiber nK nΛ nσ a kq) :=
  inferInstance

/-- The fields of a normal-form machine as a nested dependent pair. -/
abbrev Data : Type :=
  Σ (nK nΛ nσ : ℕ) (a : Fin nK → ℕ) (_ _ kq : Fin nK), Fiber nK nΛ nσ a kq

/-- A machine as its fields. -/
def toData (N : NFMachine) : Data :=
  ⟨N.nK, N.nΛ, N.nσ, N.a, N.k₀, N.k₁, N.kq, N.main, N.init, N.qAlpha, N.m⟩

/-- A machine from its fields. -/
def ofData : Data → NFMachine
  | ⟨nK, nΛ, nσ, a, k₀, k₁, kq, main, init, q, m⟩ => ⟨nK, nΛ, nσ, a, k₀, k₁, kq, main, init, q, m⟩

theorem ofData_toData (N : NFMachine) : ofData (toData N) = N := rfl

/-- **N2.** Normal-form machines form a countable type. -/
instance countable : Countable NFMachine :=
  (LeftInverse.injective ofData_toData).countable

end NFMachine

/-! ### Decider codes -/

/-- A decider code: a normal-form machine with binary input and output alphabets, and a time
polynomial. -/
structure DCode where
  /-- the machine -/
  N : NFMachine
  /-- the input alphabet is binary -/
  inE : Fin (N.a N.k₀) ≃ Bool
  /-- the output alphabet is binary -/
  outE : Fin (N.a N.k₁) ≃ Bool
  /-- the time bound -/
  time : Polynomial ℕ

namespace DCode

/-- The fields of a decider code. -/
abbrev Data : Type :=
  Σ N : NFMachine, (Fin (N.a N.k₀) ≃ Bool) × (Fin (N.a N.k₁) ≃ Bool) × Polynomial ℕ

/-- A code as its fields. -/
def toData (c : DCode) : Data := ⟨c.N, c.inE, c.outE, c.time⟩

/-- A code from its fields. -/
def ofData : Data → DCode
  | ⟨N, inE, outE, time⟩ => ⟨N, inE, outE, time⟩

theorem ofData_toData (c : DCode) : ofData (toData c) = c := rfl

/-- **N2.** Decider codes form a countable type. -/
instance countable : Countable DCode :=
  (LeftInverse.injective ofData_toData).countable

end DCode

/-! ### Verifier codes -/

/-- The alphabet of `pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)`:
`{0,1} ⊔ {#} ⊔ Γ₁`. -/
abbrev pairΓ (Γ₁ : Type) : Type := Bool ⊕ Option Γ₁

theorem pair_encoding_Γ (Γ₁ : Type) [Fintype Γ₁] :
    (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).Γ = pairΓ Γ₁ :=
  rfl

/-- A verifier code: a normal-form machine with input alphabet `pairΓ (Fin g)`, output alphabet
`Bool`, and an exponent `k`. -/
structure VCode where
  /-- the machine -/
  N : NFMachine
  /-- size of the certificate alphabet -/
  g : ℕ
  /-- the exponent of the certificate bound -/
  k : ℕ
  /-- the input alphabet is the pair alphabet over `Fin g` -/
  inE : Fin (N.a N.k₀) ≃ pairΓ (Fin g)
  /-- the output alphabet is binary -/
  outE : Fin (N.a N.k₁) ≃ Bool

namespace VCode

/-- The fields of a verifier code. -/
abbrev Data : Type :=
  Σ (N : NFMachine) (g : ℕ), ℕ × (Fin (N.a N.k₀) ≃ pairΓ (Fin g)) × (Fin (N.a N.k₁) ≃ Bool)

/-- A code as its fields. -/
def toData (c : VCode) : Data := ⟨c.N, c.g, c.k, c.inE, c.outE⟩

/-- A code from its fields. -/
def ofData : Data → VCode
  | ⟨N, g, k, inE, outE⟩ => ⟨N, g, k, inE, outE⟩

theorem ofData_toData (c : VCode) : ofData (toData c) = c := rfl

/-- **N2.** Verifier codes form a countable type. -/
instance countable : Countable VCode :=
  (LeftInverse.injective ofData_toData).countable

end VCode

/-! ### N4: every decider and every verifier has a code -/

/-- **N4d.** Every polynomial-time oracle decider has a code with the same time polynomial that
runs exactly like it under every oracle. -/
theorem exists_dcode {A : Oracle} {f : List Bool → Bool}
    (h : OTM2ComputableInPolyTime A (fin_encoding_string Bool).encode
      finEncodingBoolBool.encode f) :
    ∃ c : DCode, c.time = h.time ∧ ∀ (O : Oracle) (w : List Bool) (b : Bool) (t : ℕ),
      Nonempty (OTM2OutputsInTime O h.tm (w.map h.inputAlphabet.symm)
        (some [h.outputAlphabet.symm b]) t) ↔
      Nonempty (OTM2OutputsInTime O c.N.toOracleFinTM2 (w.map c.inE.symm)
        (some [c.outE.symm b]) t) := by
  obtain ⟨N, e₀, e₁, hN⟩ := exists_nf_equiv h.tm h.inputAlphabet h.outputAlphabet
  exact ⟨⟨N, e₀, e₁, h.time⟩, rfl, fun O w b t => hN O w (some [b]) t⟩

/-- **N4d'.** The code decides `f` under `A` within its own polynomial. -/
theorem exists_dcode_decides {A : Oracle} {f : List Bool → Bool}
    (h : OTM2ComputableInPolyTime A (fin_encoding_string Bool).encode
      finEncodingBoolBool.encode f) :
    ∃ c : DCode, c.time = h.time ∧ ∀ w : List Bool,
      Nonempty (OTM2OutputsInTime A c.N.toOracleFinTM2 (w.map c.inE.symm)
        (some [c.outE.symm (f w)]) (c.time.eval w.length)) := by
  obtain ⟨c, hc, hsim⟩ := exists_dcode h
  refine ⟨c, hc, fun w => (hsim A w (f w) _).1 ⟨?_⟩⟩
  rw [hc]
  exact h.outputsFun w

/-- Translating the certificate alphabet of the pair alphabet. -/
def pairMap {Γ₁ Γ₂ : Type} (ρ : Γ₁ → Γ₂) : pairΓ Γ₁ → pairΓ Γ₂ :=
  Sum.map id (Option.map ρ)

/-- `pairMap` along an equivalence. -/
def pairEquiv {Γ₁ Γ₂ : Type} (ρ : Γ₁ ≃ Γ₂) : pairΓ Γ₁ ≃ pairΓ Γ₂ where
  toFun := pairMap ρ
  invFun := pairMap ρ.symm
  left_inv x := by rcases x with b | _ | y <;> simp [pairMap]
  right_inv x := by rcases x with b | _ | y <;> simp [pairMap]

theorem pairMap_cert {Γ₁ Γ₂ : Type} (ρ : Γ₁ → Γ₂) (y : List Γ₁) :
    (y.map (fun b => (Sum.inr (some b) : pairΓ Γ₁))).map (pairMap ρ) =
      (y.map ρ).map (fun b => (Sum.inr (some b) : pairΓ Γ₂)) := by
  induction y with
  | nil => rfl
  | cons x y ih => exact congrArg (List.cons _) ih

/-- Translating the certificate of `w#y` symbol by symbol. -/
theorem pair_encode_map {Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂] (ρ : Γ₁ → Γ₂) (w : List Bool)
    (y : List Γ₁) :
    ((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode (w, y)).map
        (pairMap ρ) =
      (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₂)).encode (w, y.map ρ) := by
  induction w with
  | cons b w ih => exact congrArg (List.cons (Sum.inl b)) ih
  | nil => exact congrArg (List.cons (Sum.inr none)) (pairMap_cert ρ y)

/-- **N4v**, before the enumeration. -/
theorem exists_vcode_aux {Γ₁ : Type} [Fintype Γ₁] (V : OracleFinTM2) (ι₀ : V.Γ V.k₀ ≃ pairΓ Γ₁)
    (ι₁ : V.Γ V.k₁ ≃ Bool) (k : ℕ) :
    ∃ (c : VCode) (ρ : Γ₁ ≃ Fin c.g), c.k = k ∧
      ∀ (O : Oracle) (w : List Bool) (y : List Γ₁) (b : Bool) (t : ℕ),
        Nonempty (OTM2OutputsInTime O V
          (((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode (w, y)).map
            ι₀.symm) (some [ι₁.symm b]) t) ↔
        Nonempty (OTM2OutputsInTime O c.N.toOracleFinTM2
          (((pair_encoding (fin_encoding_string Bool)
            (fin_encoding_string (Fin c.g))).encode (w, y.map ρ)).map c.inE.symm)
          (some [c.outE.symm b]) t) := by
  let ρ : Γ₁ ≃ Fin (Fintype.card Γ₁) := Fintype.equivFin Γ₁
  obtain ⟨N, e₀, e₁, hN⟩ := exists_nf_equiv V (ι₀.trans (pairEquiv ρ)) ι₁
  refine ⟨⟨N, Fintype.card Γ₁, k, e₀, e₁⟩, ρ, rfl, fun O w y b t => ?_⟩
  have key := hN O ((pair_encoding (fin_encoding_string Bool)
    (fin_encoding_string (Fin (Fintype.card Γ₁)))).encode (w, y.map ρ)) (some [b]) t
  have hu : ((pair_encoding (fin_encoding_string Bool)
      (fin_encoding_string (Fin (Fintype.card Γ₁)))).encode (w, y.map ρ)).map
        (ι₀.trans (pairEquiv ρ)).symm =
      ((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode (w, y)).map
        ι₀.symm := by
    rw [show ⇑(ι₀.trans (pairEquiv ρ)).symm = ⇑ι₀.symm ∘ pairMap ρ.symm from rfl,
      ← List.map_map, pair_encode_map, List.map_map]
    simp
  rw [hu] at key
  exact key

/-! ### The enumerations -/

/-- A one-stack binary machine that halts at once (only used to show `DCode` is inhabited). -/
def d0 : OracleFinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  kq := ()
  queryAlphabet := Equiv.refl Bool
  m := fun _ _ => .halt

/-- A machine with input alphabet `pairΓ (Fin 0)` that halts at once (only used to show `VCode`
is inhabited). -/
def v0 : OracleFinTM2 where
  K := Bool
  k₀ := true
  k₁ := false
  Γ := fun b => cond b (pairΓ (Fin 0)) Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstanceAs (Fintype (pairΓ (Fin 0)))
  kq := false
  queryAlphabet := Equiv.refl Bool
  m := fun _ _ => .halt

instance DCode.nonempty : Nonempty DCode :=
  (exists_nf_equiv d0 (Equiv.refl Bool) (Equiv.refl Bool)).elim fun N h =>
    h.elim fun e₀ h => h.elim fun e₁ _ => ⟨⟨N, e₀, e₁, 0⟩⟩

instance VCode.nonempty : Nonempty VCode :=
  (exists_vcode_aux v0 (Equiv.refl _) (Equiv.refl _) 0).elim fun c _ => ⟨c⟩

/-- **N2.** An enumeration of the decider codes. -/
noncomputable def dEnum : ℕ → DCode :=
  Classical.choose (exists_surjective_nat DCode)

theorem dEnum_surjective : Surjective dEnum :=
  Classical.choose_spec (exists_surjective_nat DCode)

/-- **N2.** An enumeration of the verifier codes. -/
noncomputable def vEnum : ℕ → VCode :=
  Classical.choose (exists_surjective_nat VCode)

theorem vEnum_surjective : Surjective vEnum :=
  Classical.choose_spec (exists_surjective_nat VCode)

/-- **N4v**, statement (N) of `NOTES.md` §5.3: for every oracle verifier with certificate
alphabet `Γ₁` and every exponent `k` there are a code `i` with `k_i = k` and a bijection
`ρ : Γ₁ ≃ Fin g_i` such that, for every oracle `O` and all `w`, `y`, `b`, `t`, `V^O` outputs
`[b]` on `w#y` within `t` steps iff `M_i^O` outputs `[b]` on `w#ρ(y)` within `t` steps. -/
theorem exists_vcode {Γ₁ : Type} [Fintype Γ₁] (V : OracleFinTM2) (ι₀ : V.Γ V.k₀ ≃ pairΓ Γ₁)
    (ι₁ : V.Γ V.k₁ ≃ Bool) (k : ℕ) :
    ∃ (i : ℕ) (ρ : Γ₁ ≃ Fin (vEnum i).g), (vEnum i).k = k ∧
      ∀ (O : Oracle) (w : List Bool) (y : List Γ₁) (b : Bool) (t : ℕ),
        Nonempty (OTM2OutputsInTime O V
          (((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode (w, y)).map
            ι₀.symm) (some [ι₁.symm b]) t) ↔
        Nonempty (OTM2OutputsInTime O (vEnum i).N.toOracleFinTM2
          (((pair_encoding (fin_encoding_string Bool)
            (fin_encoding_string (Fin (vEnum i).g))).encode (w, y.map ρ)).map (vEnum i).inE.symm)
          (some [(vEnum i).outE.symm b]) t) := by
  obtain ⟨c, ρ, hk, hc⟩ := exists_vcode_aux V ι₀ ι₁ k
  obtain ⟨i, rfl⟩ := vEnum_surjective c
  exact ⟨i, ρ, hk, hc⟩

/-- **N4v'.** The same for the verifier structure inside `InNP`, with the output written as
`outputsFun` writes it. -/
theorem exists_vcode_of_verifier {Γ₁ : Type} [Fintype Γ₁] {A : Oracle}
    {f : List Bool × List Γ₁ → Bool}
    (h : OTM2ComputableInPolyTime A
      (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode
      finEncodingBoolBool.encode f) (k : ℕ) :
    ∃ (i : ℕ) (ρ : Γ₁ ≃ Fin (vEnum i).g), (vEnum i).k = k ∧
      ∀ (O : Oracle) (w : List Bool) (y : List Γ₁) (b : Bool) (t : ℕ),
        Nonempty (OTM2OutputsInTime O h.tm
          (((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode (w, y)).map
            h.inputAlphabet.invFun)
          (some ((finEncodingBoolBool.encode b).map h.outputAlphabet.invFun)) t) ↔
        Nonempty (OTM2OutputsInTime O (vEnum i).N.toOracleFinTM2
          (((pair_encoding (fin_encoding_string Bool)
            (fin_encoding_string (Fin (vEnum i).g))).encode (w, y.map ρ)).map (vEnum i).inE.symm)
          (some [(vEnum i).outE.symm b]) t) :=
  exists_vcode h.tm h.inputAlphabet h.outputAlphabet k

end Relativization
