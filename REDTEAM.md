# REDTEAM.md: independent review of `Relativization.baker_gill_solovay`

**Reviewer.** Claude (Opus 5.5) in a Claude Code session on 2026-10-08, working as an independent
red-team reviewer. I did not write this code, and my job was to look for reasons the theorem might
not mean what is claimed.

**Ground rules followed.** I wrote only to `REDTEAM.md` and to `logs/redteam-*`. I did not modify
any `.lean` file, the lakefile, the manifest or the toolchain. I installed nothing and committed
nothing. My Lean checks are scratch files in the session scratchpad, outside the repo, run with
`lake env lean` from the repo root. Their sources are copied verbatim into
`logs/redteam-src-*.lean.txt`, with the scratchpad path written as `<scratchpad>`, and their outputs
are in `logs/redteam-<task>-*.txt`. I did not use the session audit scripts.

**Starting state.** `git status` was clean on `main` at `3d2d815` ("Session 7: collapse, separation
and the Baker-Gill-Solovay theorem"). The oleans match the sources:

```
$ lake build --no-build
All targets up-to-date (1342 jobs).
EXIT=0
```
(`logs/redteam-build-nobuild.txt`)

## Summary

| Task | Result |
|---|---|
| 1 Statement audit | The statement is as claimed. A hand-written restatement that uses none of the repo's class definitions is proved equivalent (`RT.bgs_explicit`). No degenerate reading found: for every oracle, `P^A` is not every language, queries change the class, and `¬PEqNP B` is equivalent to `NP^B ⊄ P^B`. Differences from BGS 1975 are listed in §1d. The most notable is that the paper constructs *recursive* oracles and the Lean statement says nothing about recursiveness. |
| 2 Faithfulness | T1, T2, T2′, E1–E3 take no hypotheses. With them, `P^∅` and `NP^∅` are the Millennium (Clay) `P` and `NP`. Both classes contain a language (∅ and Σ\*), and neither contains every language (`sepLang sepOracle` is outside). |
| 3 Kernel check | Same toolchain as PvsNP (`v4.31.0`, which bundles `leanchecker`). All 22 modules replay with exit 0, both as one prefix run and module by module. `--fresh Relativization` (the whole closure, Mathlib included, from an empty environment) and `--fresh Relativization.BakerGillSolovay` both exit 0. |
| 4 Re-audit | My own comment-aware scanner (self-tested) finds 0 banned tokens and 0 metaprogramming commands in the code. Over all 1,642 repo constants, the axioms are exactly {propext, Classical.choice, Quot.sound}, and an independent term-walking collector agrees. The 11,574-constant closure of the theorem has 0 `unsafe` and 0 `partial` constants. `#print axioms` gives only standard axioms on all 32 declarations of the two final modules. |
| 5 Dependencies | 16 manifest packages. All checkouts sit at their pinned revs and are unmodified. Mathlib's and problems' own manifests agree. The import closure is Lean core, Mathlib (with Mathlib's own dependencies), Problems and Relativization; Physlib and the doc-gen4 tree are pinned but never imported. |
| 6 Literature | I read the 1975 paper (a scanned copy, pp. 431–437) myself. The attribution is **confirmed** against that copy: the collapse oracle is a variant of Theorem 1's `A = K(A)`, and the separation is a variant of Theorem 3's stage construction. |

No critical or major findings. Findings table at the end; verdict in the last section.

---

## 1. Statement audit

### 1.0 The theorem as stated

`Relativization/BakerGillSolovay.lean:21-31`:
```lean
theorem collapse : ∃ A : Oracle, PEqNP A :=
  ⟨univOracle, univOracle_pEqNP⟩
theorem separation : ∃ B : Oracle, ¬ PEqNP B :=
  ⟨sepOracle, sepOracle_not_pEqNP⟩
theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B) :=
  ⟨collapse, separation⟩
```
From `logs/redteam-1-statement.txt`, where the claimed type is re-typed by hand as an `example`
and elaborates:
```
baker_gill_solovay : (∃ A, PEqNP A) ∧ ∃ B, ¬PEqNP B
'Relativization.baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### 1.1 Every definition the statement depends on (`#print`, `pp.fullNames true`)

These are quoted from `logs/redteam-1-statement.txt` and cut only where marked `…`.

```
@[reducible] def Relativization.Oracle : Type :=
Set (List Bool)
def Relativization.PEqNP : Relativization.Oracle → Prop :=
fun A =>
  ∀ (L : Millennium.Language (List Bool)),
    Relativization.InP A (Millennium.fin_encoding_string Bool) L ↔
      Relativization.InNP A (Millennium.fin_encoding_string Bool) L
def Relativization.InP : Relativization.Oracle →
  {α : Type} → Computability.FinEncoding α → Millennium.Language α → Prop :=
fun A {α} ea L => ∃ f x, ∀ (a : α), L a ↔ f a = Bool.true
def Relativization.InNP : Relativization.Oracle →
  {α : Type} → Computability.FinEncoding α → Millennium.Language α → Prop :=
fun A {α} ea L =>
  ∃ Γ₁ x R k,
    (Relativization.InP A (Millennium.pair_encoding ea (Millennium.fin_encoding_string Γ₁)) fun p => R p.1 p.2) ∧
      ∀ (a : α), L a ↔ ∃ y, y.length ≤ (ea.encode a).length ^ k ∧ R a y
structure Relativization.OTM2ComputableInPolyTime (A : Relativization.Oracle) {α β αΓ βΓ : Type} (ea : α → List αΓ)
  (eb : β → List βΓ) (f : α → β) : Type 1
fields:
  Relativization.OTM2ComputableInPolyTime.tm : Relativization.OracleFinTM2
  Relativization.OTM2ComputableInPolyTime.inputAlphabet : self.tm.Γ self.tm.k₀ ≃ αΓ
  Relativization.OTM2ComputableInPolyTime.outputAlphabet : self.tm.Γ self.tm.k₁ ≃ βΓ
  Relativization.OTM2ComputableInPolyTime.time : Polynomial ℕ
  Relativization.OTM2ComputableInPolyTime.outputsFun : (a : α) →
      Relativization.OTM2OutputsInTime A self.tm (List.map self.inputAlphabet.invFun (ea a))
        (Option.some (List.map self.outputAlphabet.invFun (eb (f a)))) (Polynomial.eval (ea a).length self.time)
def Relativization.OTM2OutputsInTime : Relativization.Oracle →
  (tm : Relativization.OracleFinTM2) → List (tm.Γ tm.k₀) → Option (List (tm.Γ tm.k₁)) → ℕ → Type :=
fun A tm l l' m => StateTransition.EvalsToInTime (tm.step A) (tm.initList l) (Option.map tm.haltList l') m
structure Relativization.OracleFinTM2 : Type 1
fields:
  Relativization.OracleFinTM2.K : Type
  Relativization.OracleFinTM2.kDecidableEq : DecidableEq self.K
  Relativization.OracleFinTM2.kFin : Fintype self.K
  Relativization.OracleFinTM2.k₀ : self.K
  Relativization.OracleFinTM2.k₁ : self.K
  Relativization.OracleFinTM2.Γ : self.K → Type
  Relativization.OracleFinTM2.Λ : Type
  Relativization.OracleFinTM2.main : self.Λ
  Relativization.OracleFinTM2.ΛFin : Fintype self.Λ
  Relativization.OracleFinTM2.σ : Type
  Relativization.OracleFinTM2.initialState : self.σ
  Relativization.OracleFinTM2.σFin : Fintype self.σ
  Relativization.OracleFinTM2.Γk₀Fin : Fintype (self.Γ self.k₀)
  Relativization.OracleFinTM2.kq : self.K
  Relativization.OracleFinTM2.queryAlphabet : self.Γ self.kq ≃ Bool
  Relativization.OracleFinTM2.m : self.Λ → Bool → Turing.TM2.Stmt self.Γ self.Λ self.σ
def Relativization.OracleFinTM2.step : (tm : Relativization.OracleFinTM2) →
  Relativization.Oracle → tm.Cfg → Option tm.Cfg :=
fun tm A c => Turing.TM2.step (fun l => tm.m l (Decidable.decide (tm.query c ∈ A))) c
def Relativization.OracleFinTM2.query : (tm : Relativization.OracleFinTM2) → tm.Cfg → List Bool :=
fun tm c => List.map (⇑tm.queryAlphabet) (c.stk tm.kq)
def Relativization.OracleFinTM2.initList : (tm : Relativization.OracleFinTM2) → List (tm.Γ tm.k₀) → tm.Cfg :=
fun tm s => Turing.initList (tm.toFinTM2 Bool.false) s
def Relativization.OracleFinTM2.haltList : (tm : Relativization.OracleFinTM2) → List (tm.Γ tm.k₁) → tm.Cfg :=
fun tm s => Turing.haltList (tm.toFinTM2 Bool.false) s
structure StateTransition.EvalsToInTime.{u_1} {σ : Type u_1} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Type
fields:
  StateTransition.EvalsTo.steps : ℕ
  StateTransition.EvalsTo.evals_in_steps : (flip Bind.bind f)^[self.steps] (Option.some a) = b
  StateTransition.EvalsToInTime.steps_le_m : self.steps ≤ m
def Turing.initList : (tm : Turing.FinTM2) → List (tm.Γ tm.k₀) → tm.Cfg :=
fun tm s => { l := Option.some tm.main, var := tm.initialState, stk := fun k => if h : k = tm.k₀ then ⋯.mpr s else [] }
def Turing.haltList : (tm : Turing.FinTM2) → List (tm.Γ tm.k₁) → tm.Cfg :=
fun tm s => { l := Option.none, var := tm.initialState, stk := fun k => if h : k = tm.k₁ then ⋯.mpr s else [] }
def Turing.TM2.step … M x =>
  match x with
  | { l := Option.none, var := var, stk := stk } => Option.none
  | { l := Option.some l, var := v, stk := S } => Option.some (Turing.TM2.stepAux (M l) v S)
def Millennium.fin_encoding_string … { Γ := alphabet, encode := id, decode := fun l => Option.some l, … }
def Millennium.pair_encoding … encode := fun p =>
      List.map Sum.inl (ea.encode p.1) ++
        Sum.inr Option.none :: List.map (fun b => Sum.inr (Option.some b)) (eb.encode p.2), …
def Millennium.InPolynomialTime : {α : Type} → Computability.FinEncoding α → Millennium.Language α → Prop :=
fun {α} ea L => ∃ f _comp, ∀ (a : α), L a ↔ f a = Bool.true
def Millennium.InNondeterministicPolynomialTime : … fun {α} ea L =>
  ∃ Γ₁ x R k,
    Millennium.PolynomialTimeCheckingRelation ea (Millennium.fin_encoding_string Γ₁) R ∧
      ∀ (a : α), L a ↔ ∃ y, y.length ≤ (ea.encode a).length ^ k ∧ R a y
```

`Turing.TM2.Stmt` has the constructors `push k (σ → Γ k)`, `peek k (σ → Option (Γ k) → σ)`,
`pop k (…)`, `load (σ → σ)`, `branch (σ → Bool)`, `goto (σ → Λ)` and `halt`. One step executes
one finite statement tree. `finEncodingBoolBool.encode = encodeBool = pure`, so the output of a
decider is the one-symbol list `[f a]` (Mathlib, `Computability/Encoding.lean:186,196-201`).

### 1.2 An independent restatement (`logs/redteam-src-RT1_Statement.lean.txt`)

To rule out a definition hiding something, I restated the theorem by hand. The restatement uses
only `OracleFinTM2` (structure fields), `TM2.step`, `initList` and `haltList`. It does not mention
`InP`, `InNP`, `PEqNP`, `OTM2ComputableInPolyTime`, `OTM2OutputsInTime` or `OracleFinTM2.step`.

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
theorem oStep_eq (tm : OracleFinTM2) (A : Set (List Bool)) : oStep tm A = tm.step A := rfl
theorem bgs_explicit :
    (∃ A : Set (List Bool), ∀ L : List Bool → Prop, InP' A L ↔ InNP' A L) ∧
      (∃ B : Set (List Bool), ∃ L : List Bool → Prop, InNP' B L ∧ ¬ InP' B L)
```
Proofs: `polyDecider_iff : PolyDecider A enc f ↔ Nonempty (OTM2ComputableInPolyTime A enc
finEncodingBoolBool.encode f)`, then `inP'_iff`, `inNP'_iff`, and `bgs_explicit` derived from
`baker_gill_solovay`. Output:
```
'RT.polyDecider_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT.inP'_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT.inNP'_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT.bgs_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```
In plain words, the theorem says this:

* **Collapse.** There is a set A of binary strings such that, for every binary language L, these
  are equivalent:
  * some finite multi-stack machine decides L within a polynomial number of steps. At each step it
    learns whether its current binary query stack is in A, and it halts with output `[b]`, the
    other stacks empty and the state reset.
  * L has certificates `y` of length at most `|w|^k` over a finite alphabet, and such a machine
    decides the pairs `w#y`.
* **Separation.** There is a set B and a language L in the second class for B but not in the
  first.

### 1a. Could either half hold for a degenerate reason?

All rows are proved in `logs/redteam-src-RT3_Degenerate.lean.txt` and
`logs/redteam-src-RT2_Faithful.lean.txt`, with outputs `logs/redteam-3-degenerate.txt` and
`logs/redteam-2-faithful.txt`, unless another location is given.

| Degeneracy | Verdict | Lean evidence |
|---|---|---|
| Trivial alphabet | No. Inputs and oracle strings are `List Bool`, and `PEqNP` fixes `fin_encoding_string Bool`. | `Oracle := Set (List Bool)`, `PEqNP` in §1.1 |
| `P^A` is every language, so equality is cheap | No, for **every** oracle. Decider codes are countable (N2), every decider has a code (N4), and a code determines its language (F4). So `Set (List Bool)` would inject into `List Bool`, contradicting `Function.cantor_injective`. | `RT3.exists_not_inP (A : Oracle) : ∃ L, ¬ InP A (fin_encoding_string Bool) L`; `RT3.collapse_not_everything : ∃ L, ¬ InP univOracle … L ∧ ¬ InNP univOracle … L` |
| `P^A` / `NP^A` empty | No. | `RT3.collapse_nonempty : InNP univOracle … (· ∈ univOracle) ∧ InP univOracle … (sepLang univOracle)` |
| `P^B` so small that `P^B ≠ NP^B` is cheap | No. `P^B` contains Clay `P` and `B` itself. | `RT3.sep_P_contains : (∀ L, InPolynomialTime … L → InP sepOracle … L) ∧ InP sepOracle … (· ∈ sepOracle)` |
| Queries do nothing | No. Some oracle puts into `P^A` a language outside Clay `P = P^∅`. | `RT3.queries_matter : ∃ A, InP A … (· ∈ A) ∧ ¬ InPolynomialTime … (· ∈ A)` |
| `NP^A` is every language (the September 2026 Millennium bug class) | No. Certificates are strings over a finite `Γ₁` with the identity encoding, mirroring the post-fix `Millennium` definition (`1fdee4b` is an ancestor of the pinned commit, §5). `RT3.collapse_not_everything` also gives a language outside `NP^univOracle`. | §1.1, §5 |
| Statement vacuous via hypotheses | No. Neither conjunct has hypotheses or instance arguments. | §1.0 |

All of these report `[propext, Classical.choice, Quot.sound]` and `EXIT=0`.

### 1b. Does `¬PEqNP B` mean "some language is in `NP^B` but not in `P^B`"?

Yes; I proved the equivalence for every `B`, using T4 (`inP_subset_inNP`).
```lean
theorem not_pEqNP_iff (B : Oracle) : ¬ PEqNP B ↔ ∃ L : Language (List Bool),
    InNP B (fin_encoding_string Bool) L ∧ ¬ InP B (fin_encoding_string Bool) L
theorem separation_explicit :
    InNP sepOracle (fin_encoding_string Bool) (sepLang sepOracle) ∧
      ¬ InP sepOracle (fin_encoding_string Bool) (sepLang sepOracle) :=
  ⟨sepLang_inNP sepOracle, sepLang_not_inP⟩
```
```
'RT3.not_pEqNP_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RT3.separation_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```
T4 itself is `Relativization/Comp.lean:535`,
`theorem inP_subset_inNP (A : Oracle) (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
(L) : InP A (fin_encoding_string alphabet) L → InNP A (fin_encoding_string alphabet) L`. Its
proof composes Millennium's left-projection machine with the decider (`oracleComp`). The repo's
own proof of `¬PEqNP sepOracle` (`Stage.lean:305`) also goes through the explicit witness
`sepLang sepOracle`. The second conjunct of `RT.bgs_explicit` (§1.2) is this reading.

### 1c. Is `P^X` polynomial time in the usual sense? What do queries cost?

* **Time.** `outputsFun` requires, for every input `a`, a run of at most
  `time.eval (ea a).length` steps (`EvalsToInTime … steps ≤ m`) that ends exactly at
  `haltList [f a]`. `time : Polynomial ℕ` is fixed per machine. The machine is a single finite
  object: finite `K`, `Λ`, `σ` and input alphabet. Non-input stack alphabets may be infinite types,
  as in Mathlib's `FinTM2`. But only finitely many symbols are ever pushed, since `push` takes
  `σ → Γ k` with `σ` finite, and the normal form N3/N4 (`exists_dcode_decides`) turns every machine
  into one over `Fin` alphabets that runs exactly like it under every oracle. The separation's lower
  bound starts from `exists_dcode_decides` (`Stage.lean:271`), so it covers every `OracleFinTM2`.
* **Answer bits.** `step` (§1.1) runs `tm.m l (decide (tm.query c ∈ A))`: exactly one oracle bit
  per step, about the query stack as it stands before the step. This matches PLAN §3.3 ("One step
  sees the oracle's verdict on the query stack as it stands before the step … A `t`-step run makes
  at most `t` queries").
* **No exponential queries.** One step pushes at most `tm.depth` symbols onto the query stack, and
  the initial query is no longer than the input. Re-checked from the repo's lemmas in
  `RT3_Degenerate.lean` (the `example`s elaborate):
  ```lean
  tm.query_length_iter A n c d h : (tm.query d).length ≤ (tm.query c).length + n * tm.depth
  tm.query_initList_length_le l : (tm.query (tm.initList l)).length ≤ l.length
  tm.card_queries_le A l t       : (tm.queries A l t).card ≤ t
  ```
  So a `t`-step run asks at most `t` queries, each of length at most `|input| + t·depth`.
  Building a length-`m` query costs at least `(m − |input|)/depth` steps. That is the "query tape"
  cost regime BGS rely on: "we can query an oracle about any number of length n in approximately n
  steps" (p. 436). It is not the "oracle tape" model, under which they say "our proofs of
  Theorems 1-3 are no longer valid" (pp. 436–437; §6).
* **Unusual conventions, none of them super-polynomial.**
  * The answer is visible at every step. A classical machine simulates this by querying every step,
    a constant factor.
  * The query stack is not erased.
  * The query stack may be the input stack (`kq = k₀`), which saves at most a linear copy.
  * Halting requires Mathlib's `haltList` cleanup (state reset, every other stack empty), which
    costs at most linear time.
  * The polynomial bound is required only under the given oracle. BGS require it "whatever oracle X
    is used" (p. 432); the classes are the same by clocking.
  * The simulations between this model and BGS's query machines are standard but **not
    formalized** (finding F2).

### 1d. Comparison with the textbook statement

**Sources.** BGS is quoted from my own reading of the 1975 paper (§6). For textbooks, my
recollection is that Arora–Barak (Thm 3.7) and Sipser (Thm 9.20) state "there exist oracles A, B
with P^A = NP^A and P^B ≠ NP^B" without recursiveness. That is from memory and **not verified in
this session**.

| # | Point | BGS 1975 | Lean | Effect on the Lean statement |
|---|---|---|---|---|
| 1 | Oracle | "any set X" of binary strings (p. 431) | `Set (List Bool)` | same |
| 2 | Languages | over binary strings (inputs are binary, tuples via the 00/01/11 code, p. 433) | `PEqNP`: `Language (List Bool)` only | same as BGS. Weaker than a relativized Clay `ClassEquality` (all alphabets) for the collapse; the separation implies `¬ ClassEquality sepOracle` (`RT3.not_classEquality_sep`) (F3) |
| 3 | Deterministic machine | multitape TM with query tape and query/yes/no states (p. 432) | Mathlib TM2 multi-stack, binary query stack, one answer bit per step | incomparable as definitions; same classes by standard simulations, not formalized (F2) |
| 4 | Time bound | polynomial bound under **every** oracle (p. 432) | polynomial bound under the given oracle | incomparable as definitions; same classes by clocking, not formalized (F2) |
| 5 | Acceptance | accepting states | halt in `haltList [b]`, cleanup required | same classes |
| 6 | `NP^X` | nondeterministic query machines (p. 432) | verifiers: `|y| ≤ |w|^k`, `y ∈ Γ₁*`, `R ∈ P^X` on `w#y` | incomparable as definitions; same classes by the relativizing certificate argument, not formalized (F2) |
| 7 | Certificate bound | n/a | `|w|^k` with `0^0 = 1`, inherited from Millennium | differs from `p(|w|)` only on lengths 0 and 1 (F8) |
| 8 | Recursiveness | abstract: "We construct a recursive set A … a recursive set B" (p. 431); §2: "we construct a recursive oracle A"; Remarks: A "can be recognized deterministically in exponential time" (p. 434); §3: "there exist recursive oracles X" (p. 435) | no decidability clause; the witnesses are `noncomputable`, built from `Classical.choose` enumerations `dEnum`, `vEnum` | **weaker** than the abstract; **equal** to Theorems 1 and 3 as printed (p. 434, p. 436) (F1) |
| 9 | Witnesses | A = K(A) (Thm 1); PSPACE-complete A (Thm 2); B by stages against `L(B) = {x : ∃ y ∈ B, |y| = |x|}` (Thm 3) | `univOracle` (frames `1^i 0 1^T 0 v`, step budget); `sepOracle` with `sepLang B = {w | ∃ y, |y| ≤ |w| ∧ y.reverse ++ w.reverse ∈ B}` | irrelevant to the ∃-statement; the constructions are variants (F7) |
| 10 | Scope | Theorems 1–7, Lemmas 1–2 | the headline only (Theorems 1 and 3) | Lean covers less of the paper; Theorem 2 is not formalized |

---

## 2. Faithfulness: the empty oracle gives the repository's Clay `P` and `NP`

The session-1 lemmas as stated (`logs/redteam-2-faithful.txt`):
```
OracleFinTM2.step_empty : ∀ (tm : OracleFinTM2) (c : tm.Cfg), tm.step ∅ c = (tm.toFinTM2 false).step c
inP_of_inPolynomialTime : ∀ (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α),
  InPolynomialTime ea L → InP A ea L
@inP_empty_iff : ∀ {α : Type} (ea : FinEncoding α) (L : Language α), InP ∅ ea L ↔ InPolynomialTime ea L
@inNP_empty_iff : ∀ {α : Type} (ea : FinEncoding α) (L : Language α),
  InNP ∅ ea L ↔ InNondeterministicPolynomialTime ea L
classEquality_empty_iff : ClassEquality ∅ ↔ ClayPVersusNP
inP_empty_bool_iff : ∀ (L : Language (List Bool)),
  InP ∅ (fin_encoding_string Bool) L ↔ InPolynomialTime (fin_encoding_string Bool) L
inNP_empty_bool_iff : ∀ (L : Language (List Bool)),
  InNP ∅ (fin_encoding_string Bool) L ↔ InNondeterministicPolynomialTime (fin_encoding_string Bool) L
pEqNP_empty_iff : PEqNP ∅ ↔
  ∀ (L : Language (List Bool)),
    InPolynomialTime (fin_encoding_string Bool) L ↔ InNondeterministicPolynomialTime (fin_encoding_string Bool) L
```

* **No hypotheses.** I re-typed T1, T2, T2′ and E3 by hand as `example`s quantified over every
  encoding and language, and they elaborate. `example : (∅ : Oracle) = {w : List Bool | False} := rfl`
  confirms `∅` is the empty set of strings.
* **How they are proved** (`Plain.lean:163-228`). T1 left-to-right is `toPlain`: fix the answer
  `false`, which matches `∅` by `step_empty`, with `time := h.time` (the same polynomial). T1
  right-to-left is `ofPlain`: add an untouched binary query stack, again with `time := h.time`. T2
  unfolds and rewrites with T1 under the binders, which works because `InNP` copies
  `InNondeterministicPolynomialTime` clause for clause (§1.1). These are real machine translations,
  not a degenerate case.
* **Not vacuous: both sides are inhabited, and neither is everything.** From
  `RT2_Faithful.lean`:
  ```lean
  theorem clayP_empty_lang : InPolynomialTime (fin_encoding_string Bool) (fun w => w ∈ (∅ : Oracle))
  theorem clayP_all_lang   : InPolynomialTime (fin_encoding_string Bool) (fun w => w ∈ (Set.univ : Oracle))
  theorem clayP_all_ne_empty : (fun w : List Bool => w ∈ (Set.univ : Oracle)) ≠ (fun w => w ∈ (∅ : Oracle))
  theorem inNP_empty_all_lang : InNondeterministicPolynomialTime (fin_encoding_string Bool) (fun w => w ∈ (Set.univ : Oracle))
  theorem not_clayP_sep    : ¬ InPolynomialTime (fin_encoding_string Bool) (sepLang sepOracle)
  theorem not_inP_empty_sep : ¬ InP ∅ (fin_encoding_string Bool) (sepLang sepOracle)
  ```
  ```
  'RT2.clayP_empty_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RT2.clayP_all_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RT2.clayP_all_ne_empty' depends on axioms: [propext]
  'RT2.inNP_empty_all_lang' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RT2.not_clayP_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
  'RT2.not_inP_empty_sep' depends on axioms: [propext, Classical.choice, Quot.sound]
  EXIT=0
  ```
  `clayP_all_lang` uses my own `step_univ` and `toPlainUniv`, the `Set.univ` analogues of
  `step_empty` and `toPlain`. All six results come from the session-1 lemmas, `oracle_inP` and
  the separation.
* **Limit.** The faithfulness anchor is only at `A = ∅`. There is no external definition of
  relativized `P`/`NP` (in Mathlib or the problems repo) to compare against for `A ≠ ∅`. For
  non-empty oracles, faithfulness rests on the structural mirroring of §1.1–1.2 (F2).

---

## 3. Independent kernel check

### 3.1 How PvsNP ran it, and the toolchains

`D:\PvsNP\README.md:86-89`: "To re-check every declaration with the Lean kernel, starting from an
empty environment (`leanchecker` ships with Lean v4.28.0 and later): `lake env leanchecker --fresh
Solution`". `D:\PvsNP\NOTES.md:6`: "leanchecker: passed per-module and with `--fresh Solution` …".
`D:\PvsNP\REDTEAM.md:87`: "`lake env leanchecker --fresh Solution` | exit 0, 10:28:25 → 10:37:46
(9 min 21 s)".

```
$ cat /d/PvsNP/lean-toolchain lean-toolchain
leanprover/lean4:v4.31.0
leanprover/lean4:v4.31.0
```
The binary is present in that toolchain:
`~/.elan/toolchains/leanprover--lean4---v4.31.0/bin/leanchecker.exe` (115,200 bytes), with source
`src/lean/LeanChecker.lean`. That source says that with no module argument it checks the
manifest's package (`Relativization`) by prefix; without `--fresh` each module's own constants are
replayed onto its imported environment; and `--fresh` (one module only) replays every constant of
the closure, Mathlib included, into an empty environment. Its docstring also says: "This is not an
external verifier, simply a tool to detect "environment hacking"" (F5). Nothing was changed or
installed. `lake env` supplies the search path, and leanchecker writes nothing.

**Disclosure.** My very first invocation, `lake env leanchecker --help`, printed nothing and
returned `EXIT=0`. `--help` is not a recognized flag, so per the source it ran the default check of
all `Relativization*` modules. A following no-argument invocation I stopped by hand. Neither run is
used as evidence. The logged runs are below.

### 3.2 Per-module (`logs/redteam-leanchecker-modules.txt`)

```
Thu Oct  8 14:29:58 AUSEST 2026
$ lake env leanchecker --verbose Relativization
replaying Relativization
replaying Relativization.Univ
… (all 22 modules listed) …
replaying Relativization.BakerGillSolovay
LEANCHECKER_PREFIX_EXIT=0
Thu Oct  8 14:32:28 AUSEST 2026
```
Then each of the 21 imported modules and the root one at a time
(`lake env leanchecker --verbose <Module>`): 22 lines `EXIT[Relativization.<M>]=0`, 0 non-zero,
ending `EXIT[Relativization]=0` at `Thu Oct  8 14:57:28 AUSEST 2026`.

### 3.3 From scratch (`logs/redteam-leanchecker-fresh.txt`)

```
start Thu Oct  8 14:57:42 AUSEST 2026
$ lake env leanchecker --fresh --verbose Relativization
replaying Relativization with --fresh
LEANCHECKER_FRESH_EXIT[Relativization]=0
end Thu Oct  8 15:02:37 AUSEST 2026
start Thu Oct  8 15:02:37 AUSEST 2026
$ lake env leanchecker --fresh --verbose Relativization.BakerGillSolovay
replaying Relativization.BakerGillSolovay with --fresh
LEANCHECKER_FRESH_EXIT[Relativization.BakerGillSolovay]=0
end Thu Oct  8 15:06:10 AUSEST 2026
```
`--fresh Relativization` replays the whole closure of the root module through the kernel from an
empty environment, so every repo module and all of the Mathlib and Problems code they import. It
exits 0 in 4 min 55 s. `--fresh Relativization.BakerGillSolovay`, the module holding the theorem,
exits 0 in 3 min 33 s. This is the same check PvsNP ran (`--fresh Solution`, exit 0, 9 min 21 s).
The binary was available, so no fallback was needed.

### 3.4 Options for a truly independent kernel

`leanchecker` re-runs Lean's own kernel. A second implementation would be stronger: lean4lean
(a Lean re-implementation of the kernel) or nanoda (Rust). Neither is installed. Each needs a
download and a build. Rule 4 forbids putting clones, caches or toolchains on C:, which has 11 GB
free (`df -h`: `C: 232G 221G 11G 96%`). A build on D: (`276G` available) is possible, but it is a
download that needs your approval. Not done.

---

## 4. Independent re-audit

### 4.1 Source scan (my own scanner, `logs/redteam-src-rt_scan.py.txt`)

The scanner strips line comments, nested block and doc comments, and string literals. It then
matches whole words. Results over `Relativization.lean Relativization/*.lean`, 22 files and 5,652
lines (`logs/redteam-4-scan.txt`):
```
== BANNED TOKENS (code only, comments/strings stripped)
'sorry': code hits 0, raw hits incl. comments 0
'admit': code hits 0, raw hits incl. comments 0
'axiom': code hits 0, raw hits incl. comments 0
'native_decide': code hits 0, raw hits incl. comments 0
'implemented_by': code hits 0, raw hits incl. comments 0
'extern': code hits 0, raw hits incl. comments 0
'unsafe': code hits 0, raw hits incl. comments 0
'partial': code hits 0, raw hits incl. comments 0
```
Every metaprogramming and environment marker has 0 code hits: `run_cmd`, `run_elab`, `run_meta`,
`#eval`, `#exit`, `elab`, `elab_rules`, `macro`, `macro_rules`, `syntax`, `declare_syntax_cat`,
`notation`, `infix*`, `postfix`, `initialize`, `builtin_initialize`, `addDecl`, `addAndCompile`,
`modifyEnv`, `setEnv`, `Environment`, `Lean.Elab`, `Lean.Meta`, `MetaM`/`CoreM`/`TacticM`/
`CommandElabM`, `simproc`, `opaque`, `unsafeCast`, `ofReduceBool`, `trustCompiler`, `dbg_trace`,
`panic`, `decide +native`, `open private` and `set_option`. The only exception is `prefix`, with 2
raw hits, both in comments. The remaining markers are ordinary:
```
'attribute': 5   (four `attribute [local instance] …Fin`, one `attribute [simp] Flag.untag_tag`)
'deriving': 7    (all `deriving DecidableEq, Fintype`, Counter.lean and Pad.lean)
'@[': 7          (`@[reducible]` ×2, `@[simp]` ×5)
```
Every `import` is `Relativization.*`, `Mathlib.*` or `Problems.PVersusNP.Millennium`.

**Self-test** of the scanner on a planted file. It reported exactly the planted code hits (`sorry`
1 of 4 raw, `admit` 0 of 1 raw since it sat in a comment, and `axiom`, `native_decide`,
`implemented_by`, `extern`, `unsafe`, `partial`, `run_cmd`, `opaque`, `set_option` 1 each). It did
not match `inP'_admit`.

The trusted definitions file `Problems/PVersusNP/Millennium.lean` has 0 banned tokens in code (one
`sorry` inside a comment). It has 3 `attribute [instance]`, 2 `deriving` and 5 `@[…]`, and imports
only `Mathlib.*` and `Init.Data.List.Lemmas`.

### 4.2 Whole-environment scan (`logs/redteam-src-RT4_Env.lean.txt`, output `logs/redteam-4-env.txt`, rows `logs/redteam-4-env-rows.txt`)

```
constants in Relativization modules: 1642
UNION of collectAxioms over all of them: [Quot.sound, Classical.choice, propext]
constants whose collectAxioms is not within [propext, Classical.choice, Quot.sound]: 0 []
flags (axiom/opaque/quot/unsafe/partial/extern/implemented_by): 12 [PARTIAL Relativization.StmtCountable.toW._unsafe_rec, … PARTIAL Relativization.Plain.liftS._unsafe_rec]
```
* **The 12 `PARTIAL …._unsafe_rec` constants.** These are compiler artefacts that Lean generates
  for the code of structurally recursive definitions (`pushDepth`, `liftS`, `mapS`, `ones`, …).
  There is no `partial` in the source (§4.1). None is reachable from the theorem:
  ```
  CLOSURE of baker_gill_solovay: 11574 constants; from Relativization modules 857; unsafe 0 []; partial 0 []; opaque 3 [Lean.opaqueId,
   String.Internal.append,
   Polynomial.wrapped._@.Mathlib.Algebra.Polynomial.Eval.Defs.2849575019._hygCtx._hyg.2]; extern 53; implemented_by 5 [List.attachWith,
   Lean.Name.num, Lean.Name.str, Lean.Name.anonymous, Nat.repr]
  ```
  The three `opaque` constants and the `extern`/`implemented_by` attributes are on Lean-core and
  Mathlib declarations, not repo ones. They only affect compiled code. The kernel uses the
  definitions.
* **Declarations not under `Relativization.`** There are 130 such declarations in repo modules.
  Most are Lean-generated private matcher equation lemmas or splitters (`match_N.eq_M` ×101,
  `match_N.splitter` ×23). Two are equation lemmas realized on demand (`Turing.initList.eq_1`,
  `Turing.haltList.eq_1`). The rest are user definitions placed into Mathlib's namespace with
  `_root_`: `Turing.TM2OutputsInTime.ofRun` (`Prog.lean:1060`) and
  `Turing.TM2OutputsInTime.ofRunLe` (`Counter.lean:409`), plus two `_proof_` auxiliaries. These
  are new names, since Lean forbids redeclaration, so nothing is shadowed (F6).
* **Declarations without source ranges.** 828 carry standard auto-generated suffixes
  (`rec`/`casesOn`/`eq_N`/`match_N`/`proof_N`/`inst…`/…). The other 56 are all Lean/Mathlib
  machinery: `match_N.splitter`, `congr_simp`, `_sparseCasesOn_N.else_eq`, `proxyType`,
  `proxyTypeEquiv` and `enumList_*`/`ofNat_ctorIdx` from `deriving Fintype`. No unexplained
  declaration.
* **Axiom declarations in the whole environment** (3,583 modules): 15, all from `Init`
  (`Classical.choice`, `Quot.sound`, `propext`, `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`,
  `Lean.trustCompiler`, and the `lc*`/`isScalarObj` compiler axioms). Mathlib, Problems and
  Relativization declare none.

### 4.3 `#print axioms` versus an independent term walk

In this Lean version, `collectAxioms`, and with it `#print axioms`, does **not** walk the proof
terms of imported declarations. It reads axiom lists that were computed and stored in each `.olean`
when it was written: `Lean/Util/CollectAxioms.lean`, "Downstream modules look up pre-computed
entries for imported declarations, so axiom collection never crosses module boundaries" (F4). So I
wrote `walkAxioms`, which walks the stored types, values, constructors and recursor rules of every
reachable constant itself:
```
WALK Relativization.baker_gill_solovay: axioms [Quot.sound, Classical.choice, propext]; constants visited 11574; theorems visited 6832; missing []
WALK Relativization.collapse: axioms [Quot.sound, Classical.choice, propext]; constants visited 11013; theorems visited 6449; missing []
WALK Relativization.separation: axioms [Quot.sound, Classical.choice, propext]; constants visited 10622; theorems visited 6298; missing []
WALK Relativization.univOracle_pEqNP: axioms [Quot.sound, Classical.choice, propext]; constants visited 11012; theorems visited 6448; missing []
WALK Relativization.sepOracle_not_pEqNP: axioms [Quot.sound, Classical.choice, propext]; constants visited 10621; theorems visited 6297; missing []
WALK from all 1642 Relativization constants: axioms [Quot.sound, Classical.choice, propext]; constants visited 12413; theorems visited 7398; missing []
WALK sanity [sorryAx, Classical.em]: [Quot.sound, Classical.choice, sorryAx, propext]
```
The sanity line shows the walker does report `sorryAx` when it is reachable.

`#print axioms`, run through the real command for **every** constant of `Relativization.Collapse`
and `Relativization.BakerGillSolovay` (32 declarations, including auxiliaries and the equation
lemmas realized there):
```
'Relativization.baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.eval_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_pad_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inNP_subset_inP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inP_of_pad_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.pow_weaken' depends on axioms: [propext, Quot.sound]
'Relativization.separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.univOracle_pEqNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.Acc_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.eval_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.exists_exponents' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.muPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.muPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padFun_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2OutputsInTime.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.eval_le_pow._proof_1_1' depends on axioms: [propext, Quot.sound]
'Relativization.eval_le_pow._proof_1_2' depends on axioms: [propext, Quot.sound]
'Relativization.eval_le_pow._proof_1_3' depends on axioms: [propext, Quot.sound]
'Relativization.eval_le_pow._proof_1_4' depends on axioms: [propext, Quot.sound]
'Relativization.eval_le_pow._proof_1_5' depends on axioms: [propext, Quot.sound]
'Relativization.exists_pad_reduction._proof_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.padFun.eq_1' depends on axioms: [propext]
'Relativization.pow_weaken._proof_1_1' depends on axioms: [propext, Quot.sound]
'Relativization.pow_weaken._proof_1_2' depends on axioms: [propext, Quot.sound]
'Relativization.Collapse.muPoly.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padPoly.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2OutputsInTime.mono._proof_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.Acc.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.mu.eq_1' depends on axioms: [propext, Classical.choice, Quot.sound]
EXIT=0
```

---

## 5. Dependencies

`lakefile.toml` has exactly two `[[require]]` entries:
* `mathlib`, `git = "https://github.com/leanprover-community/mathlib4"`,
  `rev = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"`;
* `problems`, `git = "https://github.com/lean-dojo/LeanMillenniumPrizeProblems"`,
  `rev = "603053dc267cf3efe422f438eb78098c0ececd6f"`.

There are no other options apart from `autoImplicit = false` and `relaxedAutoImplicit = false`:
no `moreLeanArgs`, plugins or `precompileModules`. Checkouts against the manifest
(`logs/redteam-5-deps.txt`):
```
name               manifest rev                               HEAD                                       match  dirty  remote==url
problems           603053dc267cf3efe422f438eb78098c0ececd6f   603053dc267cf3efe422f438eb78098c0ececd6f   YES    clean  True
mathlib            fabf563a7c95a166b8d7b6efca11c8b4dc9d911f   fabf563a7c95a166b8d7b6efca11c8b4dc9d911f   YES    clean  True
Physlib            3dddd61e231b2f8936dbaa1460dc60df71bc434d   3dddd61e231b2f8936dbaa1460dc60df71bc434d   YES    clean  True
plausible          63045536fe95024e6c18fc7b48e03f506701c5bc   63045536fe95024e6c18fc7b48e03f506701c5bc   YES    clean  True
LeanSearchClient   c5d5b8fe6e5158def25cd28eb94e4141ad97c843   c5d5b8fe6e5158def25cd28eb94e4141ad97c843   YES    clean  True
importGraph        5c7542ed018c78194f1e2b903eaf6a792b74c03d   5c7542ed018c78194f1e2b903eaf6a792b74c03d   YES    clean  True
proofwidgets       24b0d9dc081c5423f8eec7e866c441e5184f29d9   24b0d9dc081c5423f8eec7e866c441e5184f29d9   YES    clean  True
aesop              e3cb2f741431ce31bf73549fb52316a57368b06f   e3cb2f741431ce31bf73549fb52316a57368b06f   YES    clean  True
Qq                 f46324995fca5f0483b742e4eb4daec7f4ee50d2   f46324995fca5f0483b742e4eb4daec7f4ee50d2   YES    clean  True
batteries          fa08db58b30eb033edcdab331bba000827f9f785   fa08db58b30eb033edcdab331bba000827f9f785   YES    clean  True
doc-gen4           0bc516c1b9db83658d6475c40d9b1ed71219b921   0bc516c1b9db83658d6475c40d9b1ed71219b921   YES    clean  True
Cli                92564e5770e4d09f2d86dfbf8ada1e9c715b384c   92564e5770e4d09f2d86dfbf8ada1e9c715b384c   YES    clean  True
leansqlite         0be4df908d1a8e75b58961041e2b4973692623df   0be4df908d1a8e75b58961041e2b4973692623df   YES    clean  True
UnicodeBasic       a2e430a4c9d3ad24078b8581fe0162fc5b0c9a6c   a2e430a4c9d3ad24078b8581fe0162fc5b0c9a6c   YES    clean  True
BibtexQuery        5d31b64fb703c5d77f6ef4d1fb958f9bdf1ea539   5d31b64fb703c5d77f6ef4d1fb958f9bdf1ea539   YES    clean  True
MD4Lean            6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5   6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5   YES    clean  True
```
* Every package required by `.lake/packages/mathlib/lake-manifest.json` and
  `.lake/packages/problems/lake-manifest.json` is pinned to the same rev as the root manifest
  (23 lines, all `SAME`). The package directories are exactly the 16 manifest names.
* **What is actually used.** The import closure has 3,583 modules with top-level prefixes
  `[Init, Lean, Std, Batteries, Mathlib, ImportGraph, Aesop, Qq, Plausible, LeanSearchClient,
  ProofWidgets, Relativization, Problems]` (§4.2). `Batteries` through `ProofWidgets` come in only
  through Mathlib's own imports. Physlib, doc-gen4, Cli, leansqlite, UnicodeBasic, BibtexQuery and
  MD4Lean are pinned (inherited from problems) but never imported. The only Problems module used
  is `Problems.PVersusNP.Millennium`, which imports only `Mathlib.*` and `Init.Data.List.Lemmas`.
* The problems commit contains the NP soundness fix:
  `git -C .lake/packages/problems merge-base --is-ancestor 1fdee4b HEAD` returns `EXIT=0`, with
  `1fdee4b Fix statement soundness across problems; add Tests library and CI`.
* It matches PvsNP. `git -C /d/PvsNP/LeanMillenniumPrizeProblems rev-parse HEAD` gives
  `603053dc267cf3efe422f438eb78098c0ececd6f`, and the two `Millennium.lean` files are
  byte-identical (`diff` prints `IDENTICAL`). The toolchains are equal (§3.1).

---

## 6. Literature

**I read the paper itself, from a scanned copy.** The method and the exact transcribed lines are
in `logs/redteam-6-literature.txt`. The PDF came from
`cse.ucdenver.edu/~cscialtman/complexity/Relativizations of the P=NP Question (Original).pdf`. It
has no text layer and no PDF renderer is installed, so I extracted the 12 CCITT-G4 page images
with a stdlib-only script (`logs/redteam-src-pdf_ccitt.py.txt`), converted them with the ffmpeg
already on PATH, and viewed pages 431–437. The header reads "SIAM J. COMPUT. Vol. 4, No. 4,
December 1975", authors "THEODORE BAKER, JOHN GILL AND ROBERT SOLOVAY". This is a course-site copy;
I did not compare it with SIAM's own copy.

* **Theorem 1** (p. 434): "There is an oracle A such that P^A = NP^A." Proof: "We construct an
  oracle A such that A = K(A). Let A = {⟨i, x, 0^n⟩ : NP_i^A accepts x in < n steps}. This is a
  valid inductive definition of a set. In a computation of length < n, no string of length ≥ n can
  be queried." The repo's `univOracle` (`x ∈ A ↔ Phi A x`, frames `1^i 0 1^T 0 v`) is a variant
  of this construction. It uses a step budget `⌊(T ∸ μ)/(D+1)⌋` to recover "no query is as long as
  the frame" for machines that push `D > 1` symbols per step. **Attribution confirmed.**
* **Theorem 2** (p. 434): "If A is polynomial-space complete, then P^A = NP^A." Not formalized; the
  textbook PSPACE-complete witness is this theorem.
* **Theorem 3** (p. 436): "There is an oracle B such that P^B ≠ NP^B." The proof works in stages
  against `L(B) = {x : there is y ∈ B such that |y| = |x|}`: run `P_i` on `0^n` with `p_i(n) < 2^n`
  and add an unqueried length-`n` string if `P_i` rejects. The repo's `sepOracle` uses the same
  scheme with a different language: strings `u ++ 0^n` of length `2n`, and
  `sepLang B = {w | ∃ y, |y| ≤ |w| ∧ y.reverse ++ w.reverse ∈ B}`. **Attribution confirmed as a
  variant.**
* **Recursiveness.** The abstract says "We construct a recursive set A such that P^A = NP^A. On the
  other hand, we construct a recursive set B such that P^B ≠ NP^B." The Theorem 1 remarks add that
  "The oracle A constructed in Theorem 1 can be recognized deterministically in exponential time."
  This contradicts `NOTES.md` §4.13 item 6 ("This is no weaker than the textbook, whose
  construction is also non-effective") (F1).
* `NOTES.md` §6 relayed quotes of Lemma 1 and of the Theorem 1 proof from a subagent and marked
  them unconfirmed. They match my reading. So does its remark that BGS's proofs fail for oracle-tape
  models: pp. 436–437, "With these models of query machines, our proofs of Theorems 1-3 are no
  longer valid."

---

## Findings

| ID | Severity | Finding | Exact Lean evidence | Recommended fix |
|---|---|---|---|---|
| F1 | minor | The Lean statement does not say that A and B are recursive (decidable), although the paper's abstract and its §2/§3 introductions claim recursive oracles. The witnesses are `noncomputable`, built from the classical enumerations `dEnum`/`vEnum`, so the Lean development does not even show they are decidable. `NOTES.md` §4.13 item 6 says wrongly that the textbook construction is "also non-effective". | `BakerGillSolovay.lean:30` `theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B)` (no decidability conjunct); `Codes.lean:268,275` `noncomputable def dEnum`, `vEnum`; `Stage.lean:133` `def sepOracle : Oracle := {z \| ∃ i, z ∈ Stage.oracleAt i}` | Correct NOTES §4.13(6). Describe the result as "Theorems 1 and 3 of BGS (without the recursiveness of the abstract)". Optionally add a stretch target: computable enumerations plus `ComputablePred (· ∈ A)` and `ComputablePred (· ∈ B)`. |
| F2 | minor | The equivalence between the relativized classes on Mathlib TM2 oracle machines (answer bit every step, verifier-defined `NP^X`, time bound only under the given oracle) and BGS's query machines (query state, nondeterministic machines, bound under every oracle) is a paper argument. Faithfulness is machine-checked only at `A = ∅`. | `Oracle.lean:92-93` (`step`), `Classes.lean:24-28` (`InNP` via certificates), `Oracle.lean:112-124` (bound under `A` only); `Plain.lean:196-228` (anchor at `∅` only) | Keep NOTES §4.13(1) and make it more prominent. Add the verifier-versus-nondeterministic and every-oracle-clock points to that list, since §4.13 currently says "Nothing else differs". Optionally formalize a nondeterministic `OracleFinTM2` and prove that it gives the same `NP^A`. |
| F3 | minor | The collapse is proved for binary languages only (`PEqNP`), not for the relativized Clay form over every alphabet (`ClassEquality univOracle`). This is the same as BGS but weaker than "relativized Clay". The separation does give `¬ ClassEquality sepOracle`. | `Classes.lean:30-38`; `RT3.not_classEquality_sep : ¬ ClassEquality sepOracle` (`logs/redteam-3-degenerate.txt`) | State it as is (already done in NOTES §4.13(2)); T8 is the fix. |
| F4 | informational | In Lean v4.31, `#print axioms` on imported declarations reads axiom lists cached in the `.olean` files instead of walking the proofs. The audits so far relied on it. | `Lean/Util/CollectAxioms.lean`, "Downstream modules look up pre-computed entries for imported declarations"; my `walkAxioms` gives the same three axioms (§4.3) | Keep an independent term walk, or the `--fresh` kernel replay together with a walk, in the audit recipe. |
| F5 | informational | `leanchecker` is the same kernel implementation re-run, not an independent checker. | `LeanChecker.lean` docstring "This is not an external verifier" | If an independent kernel check is wanted, run lean4lean or nanoda on D: (needs approval for the download). |
| F6 | informational | Two user definitions are placed in Mathlib's `Turing` namespace. They are new names (redeclaration is impossible), so nothing is shadowed, but it is namespace pollution. | `Prog.lean:1060` `def _root_.Turing.TM2OutputsInTime.ofRun`; `Counter.lean:409` `noncomputable def _root_.Turing.TM2OutputsInTime.ofRunLe` | Move them under `Relativization.` |
| F7 | informational | The witnesses are variants of BGS's: frames and a step budget instead of `⟨i, x, 0^n⟩`, and `sepLang` with strings of length `2n` instead of `L(B)`. This does not matter for the ∃-statement, but documentation should say "variant of". | `Frame.lean:14` `def frame`; `Sep.lean:173-174` `def sepLang` | Wording only. |
| F8 | informational | The certificate bound is `\|w\|^k` with `0^0 = 1`, inherited from Millennium. It differs from `p(\|w\|)` only on inputs of length 0 and 1. | `Classes.lean:27` `y.length ≤ (ea.encode a).length ^ k` | None needed; already in NOTES §4.13(4). |
| F9 | informational | 12 compiler-generated `partial` `._unsafe_rec` constants exist in the repo's environment. None is reachable from the theorem, and none comes from source `partial`. | §4.2: `CLOSURE of baker_gill_solovay: … unsafe 0 []; partial 0 []` | None; mention in the audit recipe so a future scan does not misread them. |

There are no critical or major findings. In particular, no degenerate class, no vacuous lemma, no
banned token, no extra axiom, no unpinned or modified dependency, and no kernel failure.

## Verdict

Yes: as stated, `Relativization.baker_gill_solovay` can fairly be called a formalization of the
Baker-Gill-Solovay theorem in its usual form, Theorems 1 and 3 of the 1975 paper (an oracle A with
P^A = NP^A and an oracle B with P^B ≠ NP^B, for binary languages), with no degenerate class, no
vacuous hypothesis, no axiom beyond propext, Classical.choice and Quot.sound, and a clean kernel
replay from scratch. It is weaker than the paper's abstract, which constructs *recursive* A and B,
and it relies on the standard but unformalized equivalence between Mathlib TM2 oracle machines with
verifier-defined NP and the paper's query machines, so to claim the full 1975 statement, add
decidability of both witnesses, correct `NOTES.md` §4.13 item 6, and ideally formalize that model
equivalence (F1, F2).
