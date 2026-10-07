import Relativization.Classes

/-!
# Plain machines and the empty oracle

* `Plain.toOracle M`: a plain `FinTM2` as an oracle machine. An `OracleFinTM2` needs a query stack
  with binary alphabet and `M` need not have one, so `toOracle` adds a fresh stack `none` that the
  program never touches. The lifted machine ignores the oracle's answers.
* `OTM2ComputableInPolyTime.ofPlain` (S1), `OTM2ComputableInPolyTime.toPlain` (S2): the two
  translations, with the same alphabet equivalences and the same time polynomial.
* `inP_of_inPolynomialTime` (S3): `P ⊆ P^A` for every oracle `A`.
* `inP_empty_iff` (T1), `inNP_empty_iff` (T2), `classEquality_empty_iff` (T2') and the binary
  instances `inP_empty_bool_iff` (E1), `inNP_empty_bool_iff` (E2), `pEqNP_empty_iff` (E3): with
  the empty oracle the relativized classes are the `Millennium` ones.
-/

namespace Relativization

open Turing StateTransition Function Computability Millennium

namespace Plain

attribute [local instance] FinTM2.kFin

variable (M : FinTM2)

/-- Stack alphabets of the lifted machine: `M`'s stacks and a new binary stack `none`. -/
@[reducible] def PΓ : Option M.K → Type
  | none => Bool
  | some k => M.Γ k

/-- A statement of `M`, acting on the stacks `some k` of the lifted machine. -/
def liftS : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (PΓ M) M.Λ M.σ
  | .push k f q => .push (some k) f (liftS q)
  | .peek k f q => .peek (some k) f (liftS q)
  | .pop k f q => .pop (some k) f (liftS q)
  | .load a q => .load a (liftS q)
  | .branch f q₁ q₂ => .branch f (liftS q₁) (liftS q₂)
  | .goto f => .goto f
  | .halt => .halt

/-- `M` as an oracle machine: one extra stack serves as the query stack and is never used. -/
def toOracle : OracleFinTM2 where
  K := Option M.K
  k₀ := some M.k₀
  k₁ := some M.k₁
  Γ := PΓ M
  Λ := M.Λ
  main := M.main
  ΛFin := M.ΛFin
  σ := M.σ
  initialState := M.initialState
  σFin := M.σFin
  Γk₀Fin := M.Γk₀Fin
  kq := none
  queryAlphabet := Equiv.refl Bool
  m := fun l _ => liftS M (M.m l)

/-- Stacks of the lifted machine from `M`'s stacks and the content of the query stack. -/
def mkStk (S : ∀ k, List (M.Γ k)) (t : List Bool) : ∀ k : Option M.K, List (PΓ M k)
  | none => t
  | some k => S k

variable {M}

theorem update_mkStk (S : ∀ k, List (M.Γ k)) (t : List Bool) (k : M.K) (x : List (M.Γ k)) :
    update (mkStk M S t) (some k) x = mkStk M (update S k x) t := by
  funext k'
  rcases k' with _ | k'
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm

/-- A lifted statement acts on the lifted stacks as the original acts on `M`'s stacks, and leaves
the query stack alone. -/
theorem stepAux_liftS (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k))
    (t : List Bool) :
    TM2.stepAux (liftS M q) v (mkStk M S t) =
      ⟨(TM2.stepAux q v S).l, (TM2.stepAux q v S).var, mkStk M (TM2.stepAux q v S).stk t⟩ := by
  induction q generalizing v S with
  | push k f q ih =>
      simp only [liftS, TM2.stepAux]
      rw [show mkStk M S t (some k) = S k from rfl, update_mkStk, ih]
  | peek k f q ih =>
      simp only [liftS, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [liftS, TM2.stepAux]
      rw [show mkStk M S t (some k) = S k from rfl, update_mkStk, ih]
  | load a q ih =>
      simp only [liftS, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [liftS, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [liftS, TM2.stepAux]
  | halt => simp [liftS, TM2.stepAux]

variable (M)

/-- A configuration of `M` as a configuration of the lifted machine (query stack empty). -/
def emb (c : M.Cfg) : (toOracle M).Cfg :=
  ⟨c.l, c.var, mkStk M c.stk []⟩

variable {M}

/-- One step of the lifted machine, with any oracle, is one step of `M`. -/
theorem step_emb (A : Oracle) (c : M.Cfg) :
    (toOracle M).step A (emb M c) = (M.step c).map (emb M) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · show some (TM2.stepAux (liftS M (M.m l)) v (mkStk M S [])) = _
    rw [stepAux_liftS]
    rfl

theorem initList_toOracle (l : List (M.Γ M.k₀)) :
    (toOracle M).initList l = emb M (initList M l) := by
  simp only [OracleFinTM2.initList, initList, emb]
  congr 1
  funext k
  rcases k with _ | k
  · simp [mkStk, toOracle, OracleFinTM2.toFinTM2]
  · by_cases h : k = M.k₀
    · subst h; simp [mkStk, toOracle, OracleFinTM2.toFinTM2]
    · simp [mkStk, toOracle, OracleFinTM2.toFinTM2, h]

theorem haltList_toOracle (l : List (M.Γ M.k₁)) :
    (toOracle M).haltList l = emb M (haltList M l) := by
  simp only [OracleFinTM2.haltList, haltList, emb]
  congr 1
  funext k
  rcases k with _ | k
  · simp [mkStk, toOracle, OracleFinTM2.toFinTM2]
  · by_cases h : k = M.k₁
    · subst h; simp [mkStk, toOracle, OracleFinTM2.toFinTM2]
    · simp [mkStk, toOracle, OracleFinTM2.toFinTM2, h]

/-- The lifted machine, with any oracle, has the outputs and running times of `M`. -/
def outputs (A : Oracle) {l : List (M.Γ M.k₀)} {l' : Option (List (M.Γ M.k₁))} {n : ℕ}
    (h : TM2OutputsInTime M l l' n) : OTM2OutputsInTime A (toOracle M) l l' n where
  steps := h.steps
  evals_in_steps := by
    have e := h.evals_in_steps
    have key := iter_map (emb M) (step_emb A) h.steps (some (initList M l))
    rw [initList_toOracle]
    change (flip bind ((toOracle M).step A))^[h.steps] (some (emb M (initList M l))) = _
    rw [show some (emb M (initList M l)) = (some (initList M l)).map (emb M) from rfl, key]
    rw [e]
    cases l' with
    | none => rfl
    | some o => exact congrArg some (haltList_toOracle o).symm
  steps_le_m := h.steps_le_m

end Plain

section classes

variable {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}

/-- **S1.** A plain polynomial-time machine is a polynomial-time oracle machine for every oracle,
with the same alphabets and time bound. -/
def OTM2ComputableInPolyTime.ofPlain (A : Oracle) (h : TM2ComputableInPolyTime ea eb f) :
    OTM2ComputableInPolyTime A ea eb f where
  tm := Plain.toOracle h.tm
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := h.time
  outputsFun a := Plain.outputs A (h.outputsFun a)

/-- **S2.** A polynomial-time oracle machine with the empty oracle is a plain polynomial-time
machine (fix the answer `false`), with the same alphabets and time bound. -/
def OTM2ComputableInPolyTime.toPlain (h : OTM2ComputableInPolyTime ∅ ea eb f) :
    TM2ComputableInPolyTime ea eb f where
  tm := h.tm.toFinTM2 false
  inputAlphabet := h.inputAlphabet
  outputAlphabet := h.outputAlphabet
  time := h.time
  outputsFun a :=
    { steps := (h.outputsFun a).steps
      evals_in_steps := by
        have hstep : (h.tm.toFinTM2 false).step = h.tm.step ∅ :=
          funext fun c => (h.tm.step_empty c).symm
        rw [hstep]
        exact (h.outputsFun a).evals_in_steps
      steps_le_m := (h.outputsFun a).steps_le_m }

end classes

/-- **S3 (`P ⊆ P^A`).** A language decidable in polynomial time is in `P^A` for every oracle. -/
theorem inP_of_inPolynomialTime (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) :
    InPolynomialTime ea L → InP A ea L :=
  fun ⟨f, h, hL⟩ => ⟨f, .ofPlain A h, hL⟩

/-- **T1.** With the empty oracle, `P^A` is `Millennium.InPolynomialTime`. -/
theorem inP_empty_iff {α : Type} (ea : FinEncoding α) (L : Language α) :
    InP ∅ ea L ↔ InPolynomialTime ea L :=
  ⟨fun ⟨f, h, hL⟩ => ⟨f, h.toPlain, hL⟩, inP_of_inPolynomialTime ∅ ea L⟩

/-- **T2.** With the empty oracle, `NP^A` is `Millennium.InNondeterministicPolynomialTime`. -/
theorem inNP_empty_iff {α : Type} (ea : FinEncoding α) (L : Language α) :
    InNP ∅ ea L ↔ InNondeterministicPolynomialTime ea L := by
  unfold InNP InNondeterministicPolynomialTime PolynomialTimeCheckingRelation
  simp only [inP_empty_iff]

/-- **T2'.** With the empty oracle, relativized class equality is the Clay statement. -/
theorem classEquality_empty_iff : ClassEquality ∅ ↔ ClayPVersusNP := by
  unfold ClassEquality ClayPVersusNP ClayPVersusNP.Formulations.ClassEquality
  simp only [inP_empty_iff, inNP_empty_iff]

/-- **E1.** T1 over the binary alphabet. -/
theorem inP_empty_bool_iff (L : Language (List Bool)) :
    InP ∅ (fin_encoding_string Bool) L ↔ InPolynomialTime (fin_encoding_string Bool) L :=
  inP_empty_iff _ L

/-- **E2.** T2 over the binary alphabet. -/
theorem inNP_empty_bool_iff (L : Language (List Bool)) :
    InNP ∅ (fin_encoding_string Bool) L ↔
      InNondeterministicPolynomialTime (fin_encoding_string Bool) L :=
  inNP_empty_iff _ L

/-- **E3.** With the empty oracle, `PEqNP` is `P = NP` for binary languages. -/
theorem pEqNP_empty_iff :
    PEqNP ∅ ↔ ∀ L : Language (List Bool),
      InPolynomialTime (fin_encoding_string Bool) L ↔
        InNondeterministicPolynomialTime (fin_encoding_string Bool) L := by
  unfold PEqNP
  simp only [inP_empty_iff, inNP_empty_iff]

end Relativization
