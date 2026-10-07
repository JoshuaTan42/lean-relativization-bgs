import Relativization.Oracle
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The countable normal form of an oracle machine

An `OracleFinTM2` may use arbitrary Lean types for its stack indices, labels, states and work
alphabets, so oracle machines do not form a countable type. `NFMachine` is the same structure
with every type replaced by a `Fin n`; `NFMachine.toOracleFinTM2` reads it back as a machine.

`NF.nf tm X hX` is the normal form of `tm`: labels and states are renumbered along
`Fintype.equivFin`, and each stack alphabet is cut down to the finite set `NF.symSet tm X k` of
symbols that can ever appear on that stack (everything some statement pushes there, the whole
input and query alphabets, and a finite seed `X k`), then renumbered.

Main result: `NF.nf_outputs_iff` (N3a), the normal form outputs `o` on `enc l` within `t`
steps iff `tm` outputs `dec o` on `l` within `t` steps, for every oracle, input, output and
`t`; and its forms with alphabet equivalences `exists_nf` (N3b) and `exists_nf_equiv` (N3c).
The simulation is step for step: the normal form takes exactly the same number of steps.
-/

namespace Relativization

open Turing StateTransition Function

/-- A normal-form oracle machine: `nK` stacks, stack `j` with alphabet `Fin (a j)`, `nΛ` labels,
`nσ` states. -/
structure NFMachine where
  /-- number of stacks -/
  nK : ℕ
  /-- number of labels -/
  nΛ : ℕ
  /-- number of states -/
  nσ : ℕ
  /-- alphabet sizes -/
  a : Fin nK → ℕ
  /-- input stack -/
  k₀ : Fin nK
  /-- output stack -/
  k₁ : Fin nK
  /-- query stack -/
  kq : Fin nK
  /-- initial label -/
  main : Fin nΛ
  /-- initial state -/
  init : Fin nσ
  /-- the query alphabet is binary -/
  qAlpha : Fin (a kq) ≃ Bool
  /-- the program -/
  m : Fin nΛ → Bool → TM2.Stmt (fun j => Fin (a j)) (Fin nΛ) (Fin nσ)

/-- A normal-form machine as an oracle machine. -/
abbrev NFMachine.toOracleFinTM2 (N : NFMachine) : OracleFinTM2 where
  K := Fin N.nK
  k₀ := N.k₀
  k₁ := N.k₁
  Γ := fun j => Fin (N.a j)
  Λ := Fin N.nΛ
  main := N.main
  σ := Fin N.nσ
  initialState := N.init
  kq := N.kq
  queryAlphabet := N.qAlpha
  m := N.m

/-! ### Symbols a statement can push -/

section pushSyms

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- The symbols a statement can push, tagged with their stack. -/
def pushSyms : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => ⟨k, f v⟩) ∪ pushSyms q
  | .peek _ _ q => pushSyms q
  | .pop _ _ q => pushSyms q
  | .load _ q => pushSyms q
  | .branch _ q₁ q₂ => pushSyms q₁ ∪ pushSyms q₂
  | .goto _ => ∅
  | .halt => ∅

theorem pushSyms_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (pushSyms q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek _ _ q ih => exact ih
  | pop _ _ q ih => exact ih
  | load _ q ih => exact ih
  | branch _ q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto _ => exact Set.finite_empty
  | halt => exact Set.finite_empty

end pushSyms

namespace NF

attribute [local instance] OracleFinTM2.kFin OracleFinTM2.ΛFin OracleFinTM2.σFin
  OracleFinTM2.Γk₀Fin

variable (tm : OracleFinTM2) (X : ∀ k, Set (tm.Γ k))

/-- Every symbol any statement of `tm` can push, tagged with its stack. -/
def pushed : Set (Σ k, tm.Γ k) :=
  ⋃ l, ⋃ b, pushSyms (tm.m l b)

theorem pushed_finite : (pushed tm).Finite :=
  Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => pushSyms_finite _

/-- The symbols that can appear on stack `k`: pushed symbols, the input and query alphabets
(whole), and the seed `X k`. -/
def symSet (k : tm.K) : Set (tm.Γ k) :=
  {x | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ pushed tm} ∪ (setOf fun _ => k = tm.k₀) ∪ (setOf fun _ => k = tm.kq) ∪
    X k

theorem mem_symSet_of_pushed {k : tm.K} {x : tm.Γ k} (h : (⟨k, x⟩ : Σ k, tm.Γ k) ∈ pushed tm) :
    x ∈ symSet tm X k :=
  Or.inl (Or.inl (Or.inl h))

theorem mem_symSet_k₀ (x : tm.Γ tm.k₀) : x ∈ symSet tm X tm.k₀ :=
  Or.inl (Or.inl (Or.inr rfl))

theorem mem_symSet_kq (x : tm.Γ tm.kq) : x ∈ symSet tm X tm.kq :=
  Or.inl (Or.inr rfl)

theorem mem_symSet_of_X {k : tm.K} {x : tm.Γ k} (h : x ∈ X k) : x ∈ symSet tm X k :=
  Or.inr h

variable {X} (hX : ∀ k, (X k).Finite)

include hX in
theorem symSet_finite (k : tm.K) : (symSet tm X k).Finite := by
  refine (((?_ : Set.Finite _).union ?_).union ?_).union (hX k)
  · exact (pushed_finite tm).preimage (sigma_mk_injective.injOn)
  · by_cases h : k = tm.k₀
    · subst h
      exact Set.toFinite _
    · simp [h]
  · by_cases h : k = tm.kq
    · subst h
      haveI : Finite (tm.Γ tm.kq) := Finite.of_equiv _ tm.queryAlphabet.symm
      exact Set.toFinite _
    · simp [h]

/-- Stack renumbering. -/
noncomputable abbrev κ : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
/-- Label renumbering. -/
noncomputable abbrev ℓ : tm.Λ ≃ Fin (Fintype.card tm.Λ) := Fintype.equivFin tm.Λ
/-- State renumbering. -/
noncomputable abbrev ς : tm.σ ≃ Fin (Fintype.card tm.σ) := Fintype.equivFin tm.σ

variable (X)

/-- Alphabet sizes of the normal form, indexed by renumbered stacks. -/
noncomputable def aFun (j : Fin (Fintype.card tm.K)) : ℕ :=
  Nat.card (symSet tm X ((κ tm).symm j))

theorem aFun_eq (k : tm.K) : aFun tm X (κ tm k) = Nat.card (symSet tm X k) :=
  congrArg (fun k' => Nat.card (symSet tm X k')) (Equiv.symm_apply_apply _ _)

variable {X}

/-- Renumbering of the symbols of stack `k`. -/
noncomputable def ε (k : tm.K) : symSet tm X k ≃ Fin (Nat.card (symSet tm X k)) :=
  haveI := (symSet_finite tm hX k).to_subtype
  Finite.equivFin _

/-- Encode a reachable symbol of stack `k`. -/
noncomputable def enc (k : tm.K) (x : symSet tm X k) : Fin (aFun tm X (κ tm k)) :=
  Fin.cast (aFun_eq tm X k).symm (ε tm hX k x)

/-- Decode a symbol of the normal form on stack `κ k`. -/
noncomputable def dec (k : tm.K) (i : Fin (aFun tm X (κ tm k))) : tm.Γ k :=
  ((ε tm hX k).symm (Fin.cast (aFun_eq tm X k) i)).1

theorem dec_mem (k : tm.K) (i : Fin (aFun tm X (κ tm k))) : dec tm hX k i ∈ symSet tm X k :=
  ((ε tm hX k).symm (Fin.cast (aFun_eq tm X k) i)).2

theorem dec_enc (k : tm.K) (x : symSet tm X k) : dec tm hX k (enc tm hX k x) = x.1 := by
  simp [dec, enc]

theorem enc_dec (k : tm.K) (i : Fin (aFun tm X (κ tm k))) (h : dec tm hX k i ∈ symSet tm X k) :
    enc tm hX k ⟨dec tm hX k i, h⟩ = i := by
  simp [dec, enc]

theorem dec_injective (k : tm.K) : Injective (dec tm hX k) := by
  intro i j h
  have e : (⟨dec tm hX k i, dec_mem tm hX k i⟩ : symSet tm X k) = ⟨dec tm hX k j, dec_mem tm hX k j⟩ :=
    Subtype.ext h
  have := congrArg (enc tm hX k) e
  rwa [enc_dec, enc_dec] at this

/-- Encode an input symbol. -/
noncomputable def enc₀ (x : tm.Γ tm.k₀) : Fin (aFun tm X (κ tm tm.k₀)) :=
  enc tm hX tm.k₀ ⟨x, mem_symSet_k₀ tm X x⟩

theorem dec_enc₀ (x : tm.Γ tm.k₀) : dec tm hX tm.k₀ (enc₀ tm hX x) = x :=
  dec_enc tm hX tm.k₀ _

/-- The query alphabet of the normal form. -/
noncomputable def qAlpha : Fin (aFun tm X (κ tm tm.kq)) ≃ Bool where
  toFun i := tm.queryAlphabet (dec tm hX tm.kq i)
  invFun b := enc tm hX tm.kq ⟨tm.queryAlphabet.symm b, mem_symSet_kq tm X _⟩
  left_inv i := by
    simp only [Equiv.symm_apply_apply]
    exact enc_dec tm hX tm.kq i _
  right_inv b := by
    simp [dec_enc]


/-! ### The translated program -/

theorem pushSyms_subset_pushed (l : tm.Λ) (b : Bool) : pushSyms (tm.m l b) ⊆ pushed tm :=
  fun _ hx => Set.mem_iUnion.2 ⟨l, Set.mem_iUnion.2 ⟨b, hx⟩⟩

/-- Statement translation. The proof argument says that every symbol the statement pushes is
reachable, so that it can be encoded. -/
noncomputable def tr : (q : TM2.Stmt tm.Γ tm.Λ tm.σ) → pushSyms q ⊆ pushed tm →
    TM2.Stmt (fun j => Fin (aFun tm X j)) (Fin (Fintype.card tm.Λ)) (Fin (Fintype.card tm.σ))
  | .push k f q, h =>
      .push (κ tm k) (fun s => enc tm hX k ⟨f ((ς tm).symm s),
        mem_symSet_of_pushed tm X (h (Set.mem_union_left _ (Set.mem_range_self _)))⟩)
        (tr q fun _ hx => h (Set.mem_union_right _ hx))
  | .peek k f q, h =>
      .peek (κ tm k) (fun s o => ς tm (f ((ς tm).symm s) (o.map (dec tm hX k)))) (tr q h)
  | .pop k f q, h =>
      .pop (κ tm k) (fun s o => ς tm (f ((ς tm).symm s) (o.map (dec tm hX k)))) (tr q h)
  | .load g q, h => .load (fun s => ς tm (g ((ς tm).symm s))) (tr q h)
  | .branch f q₁ q₂, h =>
      .branch (fun s => f ((ς tm).symm s)) (tr q₁ fun _ hx => h (Set.mem_union_left _ hx))
        (tr q₂ fun _ hx => h (Set.mem_union_right _ hx))
  | .goto f, _ => .goto (fun s => ℓ tm (f ((ς tm).symm s)))
  | .halt, _ => .halt

/-- The normal form of `tm`. -/
noncomputable def nf : NFMachine where
  nK := Fintype.card tm.K
  nΛ := Fintype.card tm.Λ
  nσ := Fintype.card tm.σ
  a := aFun tm X
  k₀ := κ tm tm.k₀
  k₁ := κ tm tm.k₁
  kq := κ tm tm.kq
  main := ℓ tm tm.main
  init := ς tm tm.initialState
  qAlpha := qAlpha tm hX
  m := fun l b => tr tm hX (tm.m ((ℓ tm).symm l) b) (pushSyms_subset_pushed tm _ _)

/-! ### Simulation -/

variable (X) in
/-- Configurations of the normal form, as a raw type. -/
abbrev NCfg : Type :=
  TM2.Cfg (fun j => Fin (aFun tm X j)) (Fin (Fintype.card tm.Λ)) (Fin (Fintype.card tm.σ))

/-- Stacks of the original machine read off stacks of the normal form. -/
noncomputable def eStk (S : ∀ j, List (Fin (aFun tm X j))) : ∀ k, List (tm.Γ k) :=
  fun k => (S (κ tm k)).map (dec tm hX k)

theorem eStk_update (S : ∀ j, List (Fin (aFun tm X j))) (k : tm.K)
    (L : List (Fin (aFun tm X (κ tm k)))) :
    eStk tm hX (update S (κ tm k) L) = update (eStk tm hX S) k (L.map (dec tm hX k)) := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [eStk]
  · simp [eStk, update_of_ne h, update_of_ne ((κ tm).injective.ne h)]

theorem eStk_injective : Injective (eStk tm hX) := by
  intro S S' h
  funext j
  obtain ⟨k, rfl⟩ := (κ tm).surjective j
  have := congrFun h k
  simp only [eStk] at this
  exact List.map_injective_iff.2 (dec_injective tm hX k) this

/-- The configuration of the original machine read off a configuration of the normal form. -/
noncomputable def e (c : NCfg tm X) : tm.Cfg :=
  ⟨c.l.map (ℓ tm).symm, (ς tm).symm c.var, eStk tm hX c.stk⟩

theorem e_injective : Injective (e tm hX) := by
  rintro ⟨l, v, S⟩ ⟨l', v', S'⟩ h
  have h1 : l.map (ℓ tm).symm = l'.map (ℓ tm).symm := congrArg TM2.Cfg.l h
  have h2 : (ς tm).symm v = (ς tm).symm v' := congrArg TM2.Cfg.var h
  have h3 : eStk tm hX S = eStk tm hX S' := congrArg TM2.Cfg.stk h
  rw [Option.map_injective (ℓ tm).symm.injective h1, (ς tm).symm.injective h2,
    eStk_injective tm hX h3]

/-- One block of statements: the original executes `q` from the read-off configuration exactly
as the normal form executes `tr q`. -/
theorem stepAux_tr (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (hq : pushSyms q ⊆ pushed tm)
    (v : Fin (Fintype.card tm.σ)) (S : ∀ j, List (Fin (aFun tm X j))) :
    TM2.stepAux q ((ς tm).symm v) (eStk tm hX S) = e tm hX (TM2.stepAux (tr tm hX q hq) v S) := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [tr, TM2.stepAux]
      rw [← ih, eStk_update, List.map_cons, dec_enc]
      rfl
  | peek k f q ih =>
      simp only [tr, TM2.stepAux]
      rw [← ih]
      simp only [eStk, List.head?_map, Equiv.symm_apply_apply]
  | pop k f q ih =>
      simp only [tr, TM2.stepAux]
      rw [← ih, eStk_update]
      simp only [eStk, List.head?_map, List.map_tail, Equiv.symm_apply_apply]
  | load g q ih =>
      simp only [tr, TM2.stepAux]
      rw [← ih, Equiv.symm_apply_apply]
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [tr, TM2.stepAux]
      cases f ((ς tm).symm v)
      · exact ih₂ _ _ _
      · exact ih₁ _ _ _
  | goto f => simp [tr, TM2.stepAux, e]
  | halt => simp [tr, TM2.stepAux, e]

theorem query_e (c : NCfg tm X) :
    tm.query (e tm hX c) = (nf tm hX).toOracleFinTM2.query c := by
  show ((c.stk _).map (dec tm hX tm.kq)).map tm.queryAlphabet = (c.stk _).map (qAlpha tm hX)
  rw [List.map_map]
  rfl

/-- One step of the original from a read-off configuration is the read-off of one step of the
normal form, with any oracle. -/
theorem step_e (A : Oracle) (c : NCfg tm X) :
    tm.step A (e tm hX c) = ((nf tm hX).toOracleFinTM2.step A c).map (e tm hX) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · unfold OracleFinTM2.step
    rw [query_e]
    exact congrArg some (stepAux_tr tm hX _ (pushSyms_subset_pushed tm _ _) v S)

theorem iter_e (A : Oracle) (n : ℕ) (c : NCfg tm X) :
    (flip bind (tm.step A))^[n] (some (e tm hX c)) =
      ((flip bind ((nf tm hX).toOracleFinTM2.step A))^[n] (some c)).map (e tm hX) :=
  iter_map (e tm hX) (step_e tm hX A) n (some c)

theorem e_initList (l : List (tm.Γ tm.k₀)) :
    e tm hX ((nf tm hX).toOracleFinTM2.initList (l.map (enc₀ tm hX))) = tm.initList l := by
  simp only [OracleFinTM2.initList, Turing.initList, e, OracleFinTM2.toFinTM2,
    NFMachine.toOracleFinTM2, nf]
  congr 1
  · simp
  · simp
  · funext k
    by_cases h : k = tm.k₀
    · subst h
      simp [eStk, Function.comp_def, dec_enc₀]
    · simp [eStk, h, (κ tm).injective.ne h]

theorem e_haltList (o : List (Fin (aFun tm X (κ tm tm.k₁)))) :
    e tm hX ((nf tm hX).toOracleFinTM2.haltList o) = tm.haltList (o.map (dec tm hX tm.k₁)) := by
  simp only [OracleFinTM2.haltList, Turing.haltList, e, OracleFinTM2.toFinTM2,
    NFMachine.toOracleFinTM2, nf]
  congr 1
  · simp
  · funext k
    by_cases h : k = tm.k₁
    · subst h
      simp [eStk]
    · simp [eStk, h, (κ tm).injective.ne h]

/-- **N3a.** The normal form outputs `o` on `enc l` within `t` steps iff `tm` outputs `dec o`
on `l` within `t` steps, for every oracle, input, output and `t` (and with the same number of
steps). -/
theorem nf_outputs_iff (A : Oracle) (l : List (tm.Γ tm.k₀))
    (o : Option (List (Fin (aFun tm X (κ tm tm.k₁))))) (t : ℕ) :
    Nonempty (OTM2OutputsInTime A tm l (o.map (List.map (dec tm hX tm.k₁))) t) ↔
      Nonempty (OTM2OutputsInTime A (nf tm hX).toOracleFinTM2 (l.map (enc₀ tm hX)) o t) := by
  constructor
  · rintro ⟨⟨⟨s, hs⟩, hst⟩⟩
    refine ⟨⟨⟨s, ?_⟩, hst⟩⟩
    change (flip bind (tm.step A))^[s] (some (tm.initList l)) = _ at hs
    rw [← e_initList tm hX l, iter_e] at hs
    apply Option.map_injective (e_injective tm hX)
    rw [hs]
    cases o with
    | none => rfl
    | some o => exact congrArg some (e_haltList tm hX o).symm
  · rintro ⟨⟨⟨s, hs⟩, hst⟩⟩
    refine ⟨⟨⟨s, ?_⟩, hst⟩⟩
    rw [← e_initList tm hX l, iter_e, hs]
    cases o with
    | none => rfl
    | some o => exact congrArg some (e_haltList tm hX o)

end NF

/-- **N3b.** Every oracle machine with a finite output alphabet has a normal form that, through
input and output alphabet equivalences, outputs the same lists in the same time under every
oracle. -/
theorem exists_nf (tm : OracleFinTM2) [Finite (tm.Γ tm.k₁)] :
    ∃ (N : NFMachine) (e₀ : Fin (N.a N.k₀) ≃ tm.Γ tm.k₀) (e₁ : Fin (N.a N.k₁) ≃ tm.Γ tm.k₁),
      ∀ (A : Oracle) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) (t : ℕ),
        Nonempty (OTM2OutputsInTime A tm l l' t) ↔
          Nonempty (OTM2OutputsInTime A N.toOracleFinTM2 (l.map e₀.symm)
            (l'.map (List.map e₁.symm)) t) := by
  let X : ∀ k, Set (tm.Γ k) := fun k => setOf fun _ => k = tm.k₁
  have hX : ∀ k, (X k).Finite := by
    intro k
    by_cases h : k = tm.k₁
    · subst h; exact Set.toFinite _
    · simp [X, h]
  have mem₁ : ∀ x : tm.Γ tm.k₁, x ∈ NF.symSet tm X tm.k₁ := fun _ => NF.mem_symSet_of_X tm X rfl
  let enc₁ : tm.Γ tm.k₁ → Fin (NF.aFun tm X (NF.κ tm tm.k₁)) :=
    fun x => NF.enc tm hX tm.k₁ ⟨x, mem₁ x⟩
  refine ⟨NF.nf tm hX,
    ⟨NF.dec tm hX tm.k₀, NF.enc₀ tm hX, fun i => NF.enc_dec tm hX tm.k₀ i _, NF.dec_enc₀ tm hX⟩,
    ⟨NF.dec tm hX tm.k₁, enc₁, fun i => NF.enc_dec tm hX tm.k₁ i _,
      fun x => NF.dec_enc tm hX tm.k₁ ⟨x, mem₁ x⟩⟩, fun A l l' t => ?_⟩
  have key := NF.nf_outputs_iff tm hX A l (l'.map (List.map enc₁)) t
  have hl' : (l'.map (List.map enc₁)).map (List.map (NF.dec tm hX tm.k₁)) = l' := by
    cases l' with
    | none => rfl
    | some o =>
        simp only [Option.map_some, List.map_map, Option.some.injEq]
        exact List.map_id'' (fun x => NF.dec_enc tm hX tm.k₁ ⟨x, mem₁ x⟩) _
  rw [hl'] at key
  exact key

/-- **N3c.** The same through given alphabet equivalences. -/
theorem exists_nf_equiv {αΓ βΓ : Type} [Finite βΓ] (tm : OracleFinTM2)
    (ι₀ : tm.Γ tm.k₀ ≃ αΓ) (ι₁ : tm.Γ tm.k₁ ≃ βΓ) :
    ∃ (N : NFMachine) (e₀ : Fin (N.a N.k₀) ≃ αΓ) (e₁ : Fin (N.a N.k₁) ≃ βΓ),
      ∀ (A : Oracle) (u : List αΓ) (o : Option (List βΓ)) (t : ℕ),
        Nonempty (OTM2OutputsInTime A tm (u.map ι₀.symm) (o.map (List.map ι₁.symm)) t) ↔
          Nonempty (OTM2OutputsInTime A N.toOracleFinTM2 (u.map e₀.symm)
            (o.map (List.map e₁.symm)) t) := by
  haveI : Finite (tm.Γ tm.k₁) := Finite.of_equiv βΓ ι₁.symm
  obtain ⟨N, e₀, e₁, h⟩ := exists_nf tm
  refine ⟨N, e₀.trans ι₀, e₁.trans ι₁, fun A u o t => ?_⟩
  have key := h A (u.map ι₀.symm) (o.map (List.map ι₁.symm)) t
  have h₀ : ⇑(e₀.trans ι₀).symm = ⇑e₀.symm ∘ ⇑ι₀.symm :=
    funext fun x => Equiv.symm_trans_apply _ _ _
  have h₁ : ⇑(e₁.trans ι₁).symm = ⇑e₁.symm ∘ ⇑ι₁.symm :=
    funext fun x => Equiv.symm_trans_apply _ _ _
  rw [h₀, h₁]
  simpa only [List.map_map, Option.map_map, List.map_comp_map] using key

end Relativization
