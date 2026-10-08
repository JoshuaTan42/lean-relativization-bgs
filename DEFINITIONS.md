# DEFINITIONS.md: the exact formal statement

Everything below is quoted from the source at the commit this file ships with. Toolchain
`leanprover/lean4:v4.31.0`; Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`);
LeanMillenniumPrizeProblems `603053dc267cf3efe422f438eb78098c0ececd6f`, file
`Problems/PVersusNP/Millennium.lean`. That commit comes after the September 2026 soundness fix
(`1fdee4b`, "Fix statement soundness across problems"), which limited NP certificates to strings
over a finite alphabet. Unqualified names are in namespace `Relativization`.

## Target

`Relativization/BakerGillSolovay.lean:30`:

```lean
theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B) :=
  ⟨collapse, separation⟩
```

It takes no hypotheses, variables or instance arguments. Both conjuncts use the same type
`Oracle` and the same predicate `PEqNP`.

## Oracle

`Relativization/Oracle.lean:24`:

```lean
/-- An oracle is a language over the binary alphabet. -/
abbrev Oracle := Set (List Bool)
```

An oracle is any set of finite binary strings. Its membership does not have to be decidable.

## The oracle machine model

`Relativization/Oracle.lean:28`. This is Mathlib's `Turing.FinTM2` (a multi-stack machine) plus
a query stack:

```lean
structure OracleFinTM2 where
  {K : Type} [kDecidableEq : DecidableEq K]
  [kFin : Fintype K]
  (k₀ k₁ : K)
  (Γ : K → Type)
  (Λ : Type)
  (main : Λ)
  [ΛFin : Fintype Λ]
  (σ : Type)
  (initialState : σ)
  [σFin : Fintype σ]
  [Γk₀Fin : Fintype (Γ k₀)]
  /-- the query stack -/
  (kq : K)
  /-- the query alphabet is binary -/
  (queryAlphabet : Γ kq ≃ Bool)
  /-- the program: one statement per label and oracle answer -/
  (m : Λ → Bool → Turing.TM2.Stmt Γ Λ σ)
```

The machine has a finite set `K` of stacks, an input stack `k₀` with a finite alphabet, an
output stack `k₁`, finitely many labels `Λ` and finitely many internal states `σ`. It also has a
**query stack** `kq`, whose alphabet is in bijection with `Bool`, and a program that receives one
bit for each label.

`Relativization/Oracle.lean:87-101`:

```lean
/-- The query string: the query stack, top first, read as bits. -/
def query (c : tm.Cfg) : List Bool :=
  (c.stk tm.kq).map tm.queryAlphabet

open Classical in
/-- One step with oracle `A`: the program sees whether the current query string is in `A`. -/
noncomputable def step (A : Oracle) (c : tm.Cfg) : Option tm.Cfg :=
  Turing.TM2.step (fun l => tm.m l (decide (tm.query c ∈ A))) c

def initList (s : List (tm.Γ tm.k₀)) : tm.Cfg :=
  Turing.initList (tm.toFinTM2 false) s

def haltList (s : List (tm.Γ tm.k₁)) : tm.Cfg :=
  Turing.haltList (tm.toFinTM2 false) s
```

* **One answer bit per step.** A step from a live configuration with label `l` computes
  `b := decide (query c ∈ A)`, the oracle's verdict on the query stack as it stands *before* the
  step. It then executes the whole statement `m l b`, a finite tree of `push`, `pop`, `peek`,
  `load`, `branch`, `goto` and `halt` (Mathlib's `TM2.stepAux`). A halted configuration has no
  successor. A `t`-step run therefore asks at most `t` queries
  (`Relativization/Queries.lean:33`, `card_queries_le : (tm.queries A l t).card ≤ t`).
* **Query length.** One step pushes at most `tm.depth` symbols onto the query stack
  (`Oracle.lean:264`, `depth`, the largest number of query-stack pushes in one statement). The
  initial query is no longer than the input (`query_initList_length_le`). After `n` steps the
  query has length at most `|initial query| + n · depth` (`query_length_iter`, `Oracle.lean:298`).
  Building a long query costs steps. This is the "query tape" cost regime of Baker, Gill and
  Solovay, not the "oracle tape" model under which they say their proofs fail (pp. 436–437).
* **Other conventions.** The query stack is not erased by a query. It may be the input stack
  (`kq = k₀`). Halting means reaching Mathlib's `haltList`: label `none`, state reset to
  `initialState`, the output on `k₁` and every other stack empty. Work-stack alphabets may be
  infinite types, as in `FinTM2`, but a machine pushes only finitely many distinct symbols, and
  the normal form `exists_dcode_decides` turns every machine into one over `Fin` alphabets that
  runs the same way under every oracle.

`Relativization/Oracle.lean:106-124`:

```lean
def OTM2OutputsInTime (A : Oracle) (tm : OracleFinTM2) (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) (m : ℕ) :=
  EvalsToInTime (tm.step A) (tm.initList l) (Option.map tm.haltList l') m

structure OTM2ComputableInPolyTime (A : Oracle) {α β αΓ βΓ : Type} (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) where
  tm : OracleFinTM2
  inputAlphabet : tm.Γ tm.k₀ ≃ αΓ
  outputAlphabet : tm.Γ tm.k₁ ≃ βΓ
  time : Polynomial ℕ
  outputsFun : ∀ a, OTM2OutputsInTime A tm ((ea a).map inputAlphabet.invFun)
    (some ((eb (f a)).map outputAlphabet.invFun)) (time.eval (ea a).length)
```

`EvalsToInTime f a b m` (Mathlib) means: for some `steps ≤ m`, iterating `f` `steps` times from
`some a` gives `b`. The polynomial `time` has natural coefficients and is fixed per machine. The
bound is required under the oracle `A` only.

## Encodings (from `Millennium` and Mathlib)

```lean
def Language (α : Type) := α → Prop

def fin_encoding_string (alphabet : Type) [Fintype alphabet] : FinEncoding (List alphabet) :=
  { Γ := alphabet, encode := id, decode := fun l => some l, … }

def pair_encoding {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) : FinEncoding (α × β) :=
  { Γ := pair_symbol ea eb,
    encode := λ p =>
      (ea.encode p.1).map Sum.inl ++
        Sum.inr none :: (eb.encode p.2).map (fun b => Sum.inr (some b)), … }
```

`fin_encoding_string Bool` is the identity, so a binary string is its own code and `|w|` is
`w.length`. `pair_encoding` writes a pair as Cook's `w#y`, with `Sum.inr none` as `#`, of length
`|w| + 1 + |y|`. Mathlib's `finEncodingBoolBool` encodes `b : Bool` as the one-symbol list `[b]`,
so a decider halts with exactly `[f a]` on its output stack.

## `P^X` and `NP^X`

`Relativization/Classes.lean:19-38`:

```lean
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
```

`InP` and `InNP` are `Millennium.InPolynomialTime` and
`Millennium.InNondeterministicPolynomialTime` word for word, with
`OTM2ComputableInPolyTime A` in place of Mathlib's `TM2ComputableInPolyTime`:

```lean
def InPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_comp : TM2ComputableInPolyTime ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

def InNondeterministicPolynomialTime {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    PolynomialTimeCheckingRelation ea (fin_encoding_string Γ₁) R ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y
-- PolynomialTimeCheckingRelation ea eb R := InPolynomialTime (pair_encoding ea eb) (fun p => R p.1 p.2)
```

* `NP^A` is defined by verifiers. The verifier must decide `R` on **every** pair `w#y`, within a
  polynomial of `|w| + 1 + |y|`. Certificates are strings over a finite alphabet `Γ₁` with
  `|y| ≤ |w|^k`, where Lean has `0^0 = 1`.
* `PEqNP` quantifies over every predicate on binary strings, decidable or not. A language in
  neither class satisfies the biconditional trivially.
* `ClassEquality` is defined but **not** used by the main theorem (see "What this is not" in
  `README.md`).

## Faithfulness at the empty oracle (machine-checked)

`Relativization/Plain.lean:196-228`, no hypotheses:

```lean
theorem inP_empty_iff {α : Type} (ea : FinEncoding α) (L : Language α) :
    InP ∅ ea L ↔ InPolynomialTime ea L
theorem inNP_empty_iff {α : Type} (ea : FinEncoding α) (L : Language α) :
    InNP ∅ ea L ↔ InNondeterministicPolynomialTime ea L
theorem classEquality_empty_iff : ClassEquality ∅ ↔ ClayPVersusNP
theorem pEqNP_empty_iff :
    PEqNP ∅ ↔ ∀ L : Language (List Bool),
      InPolynomialTime (fin_encoding_string Bool) L ↔
        InNondeterministicPolynomialTime (fin_encoding_string Bool) L
```

With the empty oracle, the relativized classes are exactly the `P` and `NP` of the
LeanMillenniumPrizeProblems formulation of the Clay problem. They are proved by real machine
translations (fix the answer bit to `false`; add an unused query stack), with the same
polynomial. For non-empty oracles there is no external definition to compare against.
Faithfulness there rests on the definitions above mirroring `Millennium` clause for clause.

## The witnesses (not part of the statement)

The statement only says that some `A` and some `B` exist. The proof uses these two.

**Collapse oracle `univOracle` (decision D6).** It is a variant of the oracle `A = K(A)` of
Baker-Gill-Solovay Theorem 1. A frame `1^i 0 1^T 0 v` belongs to `A` iff verifier code `i`, run
with oracle `A` on `v.reverse # y`, accepts within a step budget for some certificate `y` with
`|y| ≤ |v|^{k_i}`. The budget is chosen so that every query the run can ask is shorter than the
frame. That makes the self-referential definition well founded for machines that push `D > 1`
symbols per step.

```lean
def frame (i T : ℕ) (v : List Bool) : List Bool :=                          -- Frame.lean:14
  List.replicate i true ++ false :: (List.replicate T true ++ false :: v)
noncomputable def mu (i n : ℕ) : ℕ := n + 1 + n ^ (vEnum i).k                -- Univ.lean:36
/-- **D6.** The step budget `⌊(T ∸ μ_i(n)) / (D_i + 1)⌋`. -/
noncomputable def budget (i T n : ℕ) : ℕ := (T - mu i n) / ((M i).depth + 1) -- Univ.lean:39
def Acc (O : Oracle) (i T : ℕ) (v : List Bool) : Prop :=                    -- Univ.lean:53
  ∃ y : List (Fin (vEnum i).g), y.length ≤ v.length ^ (vEnum i).k ∧
    Nonempty (OTM2OutputsInTime O (M i) (input i v.reverse y)
      (some [(vEnum i).outE.symm true]) (budget i T v.length))
def Phi (O : Oracle) (x : List Bool) : Prop :=                              -- Univ.lean:59
  ∃ i T v, decode x = some (i, T, v) ∧ Acc O i T v
def level : ℕ → Oracle                                                      -- Univ.lean:72
  | 0 => ∅
  | m + 1 => level m ∪ {x | x.length = m ∧ Phi (level m) x}
def univOracle : Oracle := {x | ∃ m, x ∈ Univ.level m}                      -- Univ.lean:79
```

`Univ.mem_univOracle : x ∈ univOracle ↔ Phi univOracle x` (`Univ.lean:177`) is the
self-referential equation. `vEnum : ℕ → VCode` is a surjection onto verifier codes, obtained
with `Classical.choose` from countability (`Codes.lean:275`). It is noncomputable.

**Separation oracle `sepOracle`.** It is a variant of the stage construction of Baker-Gill-Solovay
Theorem 3. Stage `i` runs decider code `i` on `0^n`, with `p_i(n) < 2^n` and `n` above every
earlier query. If the decider does not output `[true]`, the stage adds an unqueried string
`u ++ 0^n` with `|u| = n`.

```lean
def sepOracle : Oracle := {z | ∃ i, z ∈ Stage.oracleAt i}                   -- Stage.lean:133
def sepLang (B : Oracle) : Language (List Bool) :=                          -- Sep.lean:173
  fun w => ∃ y : List Bool, y.length ≤ w.length ∧ y.reverse ++ w.reverse ∈ B
```

`sepLang B ∈ NP^B` holds for every `B` (`sepLang_inNP`), and
`sepLang sepOracle ∉ P^sepOracle` (`sepLang_not_inP`, `Stage.lean:269`).

## Plain-language reading

* **Oracle machine.** A finite multi-stack machine with a binary query stack. At every step it
  learns, at no cost, whether the current content of the query stack is in the oracle.
* **`L ∈ P^X`.** Some such machine with oracle `X` takes each binary string `w` and, within
  `p(|w|)` steps for a fixed polynomial `p`, halts with output `[true]` if `w ∈ L` and `[false]`
  otherwise. On halting, all other stacks are empty and the state is reset.
* **`L ∈ NP^X`.** There are a finite certificate alphabet `Γ₁`, an exponent `k` and a relation
  `R` such that `w ∈ L` iff some `y ∈ Γ₁*` with `|y| ≤ |w|^k` has `R w y`, and `R` is decided in
  `P^X` on the strings `w#y`.
* **`PEqNP X`.** For every language `L` of binary strings, `L ∈ P^X ↔ L ∈ NP^X`.
* **The theorem.** There is a set `A` of binary strings with `P^A = NP^A`, and a set `B` of
  binary strings with `P^B ≠ NP^B`. Since `P^B ⊆ NP^B` for every oracle (`inP_subset_inNP`,
  `Comp.lean:535`), the second half says that some language is in `NP^B` but not in `P^B`.

## A restatement on plain machines, and how to check it

The session-8 red-team review restated the theorem by hand. The restatement uses only the fields
of `OracleFinTM2`, Mathlib's `TM2.step`, and `initList`/`haltList`. It does not use `InP`,
`InNP`, `PEqNP`, `OTM2ComputableInPolyTime`, `OTM2OutputsInTime` or `OracleFinTM2.step`. The
review then proved the restatement from `baker_gill_solovay`. From
`logs/redteam-src-RT1_Statement.lean.txt`:

```lean
noncomputable def oStep (tm : OracleFinTM2) (A : Set (List Bool)) (c : TM2.Cfg tm.Γ tm.Λ tm.σ) :
    Option (TM2.Cfg tm.Γ tm.Λ tm.σ) :=
  TM2.step (fun l => tm.m l (decide ((c.stk tm.kq).map tm.queryAlphabet ∈ A))) c

def PolyDecider {α αΓ : Type} (A : Set (List Bool)) (enc : α → List αΓ) (f : α → Bool) : Prop :=
  ∃ (tm : OracleFinTM2) (ι₀ : tm.Γ tm.k₀ ≃ αΓ) (ι₁ : tm.Γ tm.k₁ ≃ Bool) (p : Polynomial ℕ),
    ∀ a : α, ∃ s ≤ p.eval (enc a).length,
      (flip bind (oStep tm A))^[s] (some (tm.initList ((enc a).map ι₀.symm))) =
        some (tm.haltList [ι₁.symm (f a)])

def InP' (A : Set (List Bool)) (L : List Bool → Prop) : Prop :=
  ∃ f : List Bool → Bool, PolyDecider A id f ∧ ∀ w, L w ↔ f w = true

def pairEnc (Γ₁ : Type) (p : List Bool × List Γ₁) : List (Bool ⊕ Option Γ₁) :=
  p.1.map Sum.inl ++ Sum.inr none :: p.2.map (fun b => Sum.inr (some b))

def InNP' (A : Set (List Bool)) (L : List Bool → Prop) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : List Bool → List Γ₁ → Prop) (k : ℕ),
    (∃ g : List Bool × List Γ₁ → Bool, PolyDecider A (pairEnc Γ₁) g ∧ ∀ p, R p.1 p.2 ↔ g p = true) ∧
      ∀ w, L w ↔ ∃ y : List Γ₁, y.length ≤ w.length ^ k ∧ R w y

theorem bgs_explicit :
    (∃ A : Set (List Bool), ∀ L : List Bool → Prop, InP' A L ↔ InNP' A L) ∧
      (∃ B : Set (List Bool), ∃ L : List Bool → Prop, InNP' B L ∧ ¬ InP' B L)
```

The file also proves `polyDecider_iff`, `inP'_iff : InP' A L ↔ InP A (fin_encoding_string Bool) L`
and `inNP'_iff`. Here `PolyDecider` says: some oracle machine reaches the halting configuration
with output `[f a]` within `p(|enc a|)` steps of `oStep`, on every input `a`.

**To check it.** From the repository root, after `lake build`, copy the logged source to a
`.lean` file outside `Relativization/` and run it:

```
cp logs/redteam-src-RT1_Statement.lean.txt /tmp/Check_RT1.lean
lake env lean /tmp/Check_RT1.lean
```

The file starts with `import Relativization`, prints the definitions the statement depends on
(`#print`), and ends with five `#print axioms` lines. Re-run on 2026-10-08 for this file (about
17 seconds), the last lines were:

```
'RT.polyDecider_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT.inP'_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT.inNP'_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT.bgs_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

(`EXIT=0` is the exit status, printed by the wrapper used for the run.) `REDTEAM.md` §1 has the
`#print` output of every definition involved, and §1a lists the degenerate readings that were
ruled out, each with a Lean proof.
