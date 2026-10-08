# PLAN — Baker-Gill-Solovay in Lean 4 + Mathlib

Status: plan approved 2026-10-07 with decisions Q1 (yes), Q2/Q3 (yes, with conditions), Q5 (binary
first). Session 1 (foundations and faithfulness checks) and session 2 (normal form N1–N4, unique
output F4) are done; see §6.7 and §6.8 for the revised estimates and for corrections to this
plan, and `NOTES.md` for statements, proofs and check outputs.
Nothing is committed.

Target: there is an oracle `A` with `P^A = NP^A` and an oracle `B` with `P^B ≠ NP^B`,
on Mathlib's `FinTM2` machine model, with relativized classes that reduce to the
LeanMillenniumPrizeProblems `P` and `NP` at the empty oracle.

## 0. Decisions needed from you

| # | Decision | Recommendation |
|---|---|---|
| Q1 | Add LeanMillenniumPrizeProblems as a dependency (lakefile change, diff in §1.3) | Yes. The trivial-oracle lemma cannot be stated in Lean without its constants. |
| Q2 | Machine model | Option H (§3): the program reads one oracle bit per step. |
| Q3 | Oracle for `P^A = NP^A` | The self-referential bounded-acceptance oracle (§4.1), not TQBF. |
| Q4 | Which half first | `P^B ≠ NP^B` (§4.3). |
| Q5 | Theorem scope | Binary input alphabet first; the Clay-shaped "all finite alphabets" form as a stretch goal (§6.3). |
| Q6 | Copy PvsNP source files into this repo (§5) | Yes, with a provenance header; `D:\PvsNP` stays untouched. |

## 1. Setup record

### 1.1 What exists

| Item | Value |
|---|---|
| Toolchain | `leanprover/lean4:v4.31.0` (already installed under elan; nothing installed this session) |
| Mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, pinned by full SHA |
| Other packages | plausible, LeanSearchClient, importGraph, proofwidgets, aesop, Qq, batteries, Cli: all nine revisions identical to `D:\PvsNP\lake-manifest.json` (compared programmatically) |
| Git | initialised, `core.autocrlf=false` (local), `.gitignore` = `.lake/`, no commits |
| Files | `claude.md`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore`, `Relativization.lean` (imports only), `PLAN.md` |

`lakefile.toml`:

```toml
name = "relativization"
defaultTargets = ["Relativization"]

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false

# Mathlib pinned to the exact commit used by D:\PvsNP (tag v4.31.0).
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"

# Every module lives under Relativization/ and is imported from Relativization.lean,
# so adding a file never requires a lakefile change.
[[lean_lib]]
name = "Relativization"
```

### 1.2 Cache reuse (observed output)

The Mathlib download cache already existed at `C:\Users\Joshua Tan\.cache\mathlib`
(8,542 `.ltar` files, 412.2 MB, all dated 2026-09-25). `lake update` was run with
`MATHLIB_NO_CACHE_ON_UPDATE=1`, then `lake exe cache unpack` (decompress only, cannot download):

```
Decompressing 8538 file(s) (4 already decompressed)
Decompressed in 555938 ms
Completed successfully!
```

then `lake exe cache get`:

```
Current branch: HEAD
Using cache (Azure) from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8542 file(s)
```

then `lake build`:

```
✔ [1204/1205] Built Relativization (14s)
Build completed successfully (1205 jobs).
```

The C: cache directory was unchanged afterwards (8,542 files, 412.2 MB, newest write 2026-09-25).
`D:\Relativization\.lake` is 6.90 GB. D: free space went from 274.57 GB to 267.42 GB.

Standing caveat for rule 4: the download cache and the elan toolchain live on C: and predate
this project. Any future command that would download Mathlib cache files (a Mathlib bump, a
different commit) would write to C:. Use `lake exe cache unpack` first, or set
`MATHLIB_CACHE_DIR` to a D: path, before any such step.

### 1.3 Proposed lakefile change (Q1) — not applied

```diff
 [[require]]
 name = "mathlib"
 git = "https://github.com/leanprover-community/mathlib4"
 rev = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"
 
+# Definitions of P and NP that the relativized classes must reduce to (same commit as D:\PvsNP).
+[[require]]
+name = "problems"
+git = "https://github.com/lean-dojo/LeanMillenniumPrizeProblems"
+rev = "603053dc267cf3efe422f438eb78098c0ececd6f"
+
```

Why: `Millennium.InPolynomialTime`, `InNondeterministicPolynomialTime`, `pair_encoding`,
`fin_encoding_string` and the verified left-projection machine
(`LeftProjection.polynomial_time_computable`) all live in
`Problems/PVersusNP/Millennium.lean`. That file imports only Mathlib.

Cost: clones of the problems repo and its transitive dependencies (Physlib, doc-gen4, leansqlite,
UnicodeBasic, BibtexQuery, MD4Lean; about 45 MB of git data in the PvsNP checkout), all on D:.
Only `Problems.PVersusNP.Millennium` (one file, 1,885 lines including blanks) would be compiled; no
Physlib module is imported.
After the change I would run `lake update problems` and verify the Mathlib revision in the manifest
is still `fabf563a`.

Alternative: vendor a copy of the definitions. Then the main theorem depends on Mathlib alone, but
the trivial-oracle lemma is about a copy, not the real constants. Not recommended.

## 2. Prior work

Verification status is marked per item. "Survey" means reported by a web-search subagent that
fetched pages through a summarising tool; I did not audit those sources.

### 2.1 Baker-Gill-Solovay itself

No completed machine-checked proof of either half was found in Lean, Coq/Rocq, Isabelle/AFP, HOL4,
HOL Light, Agda, Mizar or ACL2. This is a search result, not a proof of absence: GitHub code search
and live Zulip were not searchable.

- **PleaNP** (Lean 4 + Mathlib, P. D. Allen, 2026), <https://github.com/philipdallen/PleaNP>.
  I fetched the README myself, twice, through a summarising fetch tool, so the quotes are as that
  tool relayed them. Its status note dated 2026-09-22 says: "Relativization is a frozen statement
  carrying 2 tracked `sorry`s" and "**No barrier theorem is proven.**" It also says "None of these
  barriers has a machine-checked proof in any proof assistant, in any computational model."
  Survey: both halves are stated in `lean/PleaNP/Barriers/Relativization.lean` ending in `sorry`;
  the tracker lists the blockers as "PSPACE/QBF" for the equalising oracle and "machine enumeration
  + diagonalization" for the separating one; its oracle classes sit on `FinTM2` with the query read
  from the input tape; `P^A ⊆ NP^A` is proved.
- **iehality/unrelativizable** (Lean 4, 2025). Survey: a three-commit stub, no classes, no statement.

### 2.2 Oracle machines and relativized classes

- **Complexitylib** (Lean 4, S. Schlesinger), <https://github.com/SamuelSchlesinger/complexitylib>.
  Survey: `OracleTM` with a query tape and query states, added 2026-08-30, deterministic only, with
  `DecidesInTime`; no `P^A` or `NP^A`; PH defined by quantifiers. It also has Savitch
  (`PSPACE_eq_NPSPACE`), a time hierarchy theorem and a universal TM, all on its own machine model.
- **LeanMillenniumPrizeProblems** `PolynomialHierarchy.lean`. Survey: alternating quantifiers,
  explicitly without oracle machines.
- **CSLib**. Survey: single- and multi-tape TMs, oracle tapes only planned.
- **Coq**: coq-library-complexity (Cook-Levin and a time hierarchy in the L calculus, no oracles);
  Forster-Kirst-Mück and follow-ups (synthetic oracle computability, Kleene-Post, Post's problem; no
  resource bounds). Survey.
- **Isabelle AFP**: Cook-Levin (Balbach), Universal Turing Machine, Multitape TM Substrate; nothing
  on oracle machines, PSPACE or QBF. Survey.
- **É. Bonnet** (Lean 4, 2026): Savitch and a PSPACE-completeness proof on a custom space machine.
  Survey.

### 2.3 Oracle computability in Mathlib (read locally at `fabf563a`)

`Mathlib/Computability/RecursiveIn.lean` and `TuringDegree.lean` (Duve, Roth, 2025):
`Nat.RecursiveIn (O : Set (ℕ →. ℕ)) : (ℕ →. ℕ) → Prop`, an inductive closure of the partial
recursive operations plus the oracles, then `RecursiveIn`, `ComputableIn`, `TuringReducible`,
`TuringDegree`. It is computability only: no machines, no step counts, no link to TM0/TM1/TM2.
Not usable for polynomial-time classes. `TM2ComputableInPolyTime.comp` is still a `proof_wanted`
in `Mathlib/Computability/TuringMachine/Computable.lean:284`.

### 2.4 What this project would add

1. A complete proof of both halves, which the search did not find anywhere.
2. Relativized `P^A`, `NP^A` on Mathlib's `FinTM2` that equal the LeanMillenniumPrizeProblems
   classes at the empty oracle, so `ClassEquality ∅` is literally the Clay statement.
3. Routes around the two blockers PleaNP names: no PSPACE or QBF (§4.1), and countability of machines
   by a cardinality argument with no Gödel numbering (§4.2).
4. Reusable pieces: an oracle `FinTM2`, plain-then-oracle composition, a countable normal form for
   `FinTM2`.

## 3. Machine model

### 3.1 Options

| | Design | Trivial-oracle lemma | Reuse of `TM2.Stmt` lemmas | Bookkeeping of queries |
|---|---|---|---|---|
| A | New statement type: `TM2.Stmt` plus a `query` constructor | Needs a statement translation and a simulation | None: `stepAux` and every PvsNP lemma must be redone | Several queries per step, each on a mid-statement stack |
| B | `FinTM2` plus query labels with yes/no successor labels | Simulation proof (query steps vs plain steps) | Partial: only on runs known to avoid query labels | One per step |
| E | `FinTM2` plus a virtual one-symbol stack holding the answer, refreshed each step | Statement translation | Full | One per step, but `haltList` must change |
| **H** | `FinTM2` whose program is `Λ → Bool → TM2.Stmt`: each step receives the oracle's answer for the current query-stack content | Step functions equal, so both directions are immediate | Full: for a fixed bit the program is a plain TM2 program | One per step, on the pre-step content |

### 3.2 Recommendation: option H

```lean
/-- An oracle is a language over the binary alphabet. -/
abbrev Oracle := Set (List Bool)

/-- `Turing.FinTM2` plus a query stack with binary alphabet, and a program that may depend on the
oracle's answer about the current content of the query stack. -/
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
  (kq : K)
  (queryAlphabet : Γ kq ≃ Bool)
  (m : Λ → Bool → Turing.TM2.Stmt Γ Λ σ)

/-- Fixing the oracle's answer gives a plain `FinTM2` on the same types. -/
def OracleFinTM2.toFinTM2 (tm : OracleFinTM2) (b : Bool) : FinTM2 := { …, m := fun l => tm.m l b }

def OracleFinTM2.Cfg (tm : OracleFinTM2) : Type := Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

/-- The query string: the query stack, top first, read as bits. -/
def OracleFinTM2.query (tm : OracleFinTM2) (c : tm.Cfg) : List Bool :=
  (c.stk tm.kq).map tm.queryAlphabet

open Classical in
noncomputable def OracleFinTM2.step (tm : OracleFinTM2) (A : Oracle) (c : tm.Cfg) : Option tm.Cfg :=
  Turing.TM2.step (fun l => tm.m l (decide (tm.query c ∈ A))) c

def OracleFinTM2.initList (tm : OracleFinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg :=
  Turing.initList (tm.toFinTM2 false) s
def OracleFinTM2.haltList (tm : OracleFinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg :=
  Turing.haltList (tm.toFinTM2 false) s

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

Classes, mirroring `Millennium.InPolynomialTime` and `InNondeterministicPolynomialTime` word for
word (`Language`, `pair_encoding`, `fin_encoding_string` are the Millennium ones, pending Q1):

```lean
def InP (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_ : OTM2ComputableInPolyTime A ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

def InNP (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    InP A (pair_encoding ea (fin_encoding_string Γ₁)) (fun p => R p.1 p.2) ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y

/-- Binary-alphabet form. -/
def PEqNP (A : Oracle) : Prop :=
  ∀ L : Language (List Bool),
    InP A (fin_encoding_string Bool) L ↔ InNP A (fin_encoding_string Bool) L

/-- Relativized `ClayPVersusNP.Formulations.ClassEquality`. -/
def ClassEquality (A : Oracle) : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InP A (fin_encoding_string alphabet) L ↔ InNP A (fin_encoding_string alphabet) L
```

Elaboration check: all of the above, and the statements in §6.2, were elaborated against this
project's Mathlib in a throwaway file (statements as `Prop`-valued `def`s, no proofs, with local
stand-ins for the two Millennium encodings). The file reported
`'Relativization.Stmt_bgs' depends on axioms: [propext, Classical.choice, Quot.sound]` and exit
code 0. It was deleted afterwards and is not part of the repo.

### 3.3 Conventions a reviewer should know about

- **The answer is visible at every step, not only in a query state.** One step sees the oracle's
  verdict on the query stack as it stands before the step. A classical query-state machine is the
  special case where the program ignores the bit except at query labels. Conversely a classical
  machine simulates this model by querying before each step, a constant-factor slowdown. `P^A` and
  `NP^A` are unchanged. A `t`-step run makes at most `t` queries.
- **The query stack is not erased by a query.** This matters for space bounds, not for polynomial time.
- **The query stack may be the input stack** (`kq = k₀`) when the input alphabet is binary. This makes
  `A ∈ P^A` a three-label machine.
- **Halting** is Mathlib's `haltList`: every stack except the output empty, state reset. The query
  stack must be emptied too.
- **Work alphabets may be infinite types**, exactly as in `FinTM2` (only `Γ k₀` is `Fintype`). This
  keeps the trivial-oracle lemma immediate; the price is paid once, in the normal-form lemma N3.

### 3.4 Requirements from the brief

| Requirement | Statement | How |
|---|---|---|
| Trivial oracle matches `P` | T1 in §6.2 | `tm.step ∅ = (tm.toFinTM2 false).step`; conversely a `FinTM2` is an `OracleFinTM2` that ignores the bit |
| Trivial oracle matches `NP` | T2 | unfold, T1 under the binders |
| `A ∈ P^A` | T3 | hand-written machine with `kq = k₀`: record the bit, drain the input, output it |
| `P^A ⊆ NP^A` | T4 | Millennium's left-projection machine, then the decider, via plain-then-oracle composition (F7) |

### 3.5 An architectural consequence

Only one oracle machine is ever written by hand (the T3 decider). Everything else that needs an
oracle is "a plain polynomial-time function, then the T3 decider", glued by one composition lemma:

```lean
theorem oracleComp (A : Oracle) … (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : OTM2ComputableInPolyTime A eβ eγ g) : Nonempty (OTM2ComputableInPolyTime A eα eγ (g ∘ f))
```

So the plain-machine library from PvsNP is usable unchanged.

## 4. Proof routes

### 4.1 `P^A = NP^A`

**Standard route (TQBF).** Needs: space-bounded TM2 semantics and PSPACE; QBF syntax, semantics and
encoding; TQBF PSPACE-hardness, which is a Cook-Levin-scale tableau reduction with a quantified
reachability formula, emitted by a polynomial-time TM2 machine; a polynomial-space TM2 evaluator
for QBF; and a polynomial-space simulation of an oracle verifier over all certificates with that
evaluator inlined. Calibration: the PvsNP Cook-Levin development is 11,186 non-blank lines, about
9,000 of them generator machines and tableau (`D3*`, `Sit`, `Asm`, `Pre`, `Pkg`). My estimate for
this route is 15,000 to 20,000 lines and 25 to 35 sessions, with wide uncertainty. Complexitylib and Bonnet have Savitch and PSPACE material, but
on other machine models, so none of it transfers to TM2.

**Cheaper oracle that works: bounded acceptance, defined by recursion on length.**
Fix a surjection `e : ℕ → VCode` onto normal-form oracle verifiers (§4.2), each code carrying a
certificate alphabet size `g` and an exponent `k`. Write `frame i T v = 1^i 0 1^T 0 v`. Define

> `x ∈ A` iff, with `(i, T, v) = decode x`, `w = v.reverse`, `n = |w|`, `μ = n + 1 + n^{k_i}`,
> `D_i = depth (e i)` and the **step budget** `β = ⌊(T ∸ μ) / (D_i + 1)⌋`: there is a
> certificate `y ∈ [g_i]*` with `|y| ≤ n^{k_i}` such that verifier `e i`, run on `w#y` with
> oracle `A`, halts with output `[true]` within `β` steps.

**Decision D6 (approved 2026-10-07): this budget, not `T`, is the definition.** With it every
query asked within the budget is strictly shorter than `x` for every certificate and every
oracle (NOTES §5.5), so `A` is defined by recursion on length through
`A_{m+1} = A_m ∪ {x : |x| = m ∧ Φ(A_m, x)}` and then satisfies the untruncated equation
`x ∈ A ↔ Φ(A, x)` (NOTES §5.6). The budget-`T` version with the oracle cut off at length `|x|`
(the first draft of this paragraph) is recorded in NOTES §5.8 and is not used. The universal
simulation lives in the definition of `A`, as mathematics. No universal machine, no PSPACE, no
QBF, no Savitch.

Why `NP^A ⊆ P^A`. Let `L ∈ NP^A` via a verifier with code `i` (so `k_i = k`), time polynomial
`q` and depth `D = D_i`. Take `T(n) = (n + c')^d` at least `μ(n) + (D + 1) · q(μ(n))` with
`μ(n) = n + 1 + n^k` (such `c', d` exist: `Pkg.eval_le_pow` in PvsNP). Let
`pad w = frame i (T |w|) w.reverse`. Its budget is at least `q(μ(|w|))`, so under `A` the coded
verifier halts on every short certificate within the budget with the verifier's answer, and by
unique output (F4) `pad w ∈ A ↔ w ∈ L` (NOTES §5.7). `pad` is a plain polynomial-time function,
so `L ∈ P^A` by `oracleComp` with the T3 decider. The other inclusion is T4.

I have not traced a citation for this construction; the argument is elementary and is written out
above. It needs verifying step by step in Lean like everything else.

Machine cost: one plain machine computing `pad`, i.e. copy the input, count it, raise to a fixed
power in unary, emit constants. PvsNP already has the unary power loop (`Pre.pow_run`).
Estimate for the whole half: about 1,600 lines beyond the shared foundation.

Rejected alternatives: an EXP-complete oracle needs a universal simulator built as a TM2 machine;
any PSPACE-complete oracle has the TQBF costs.

### 4.2 `P^B ≠ NP^B`

**The countability problem.** `FinTM2 : Type 1`. Its stack index, label, state and alphabet types
are arbitrary Lean types, so machines do not form a countable type and cannot be enumerated as
they stand.

**Countable normal form, without Gödel numbering.**

1. Restrict each stack alphabet to its reachable symbols: all of `Γ k₀`, `Γ k₁`, `Γ kq` (finite
   already) and, on every stack, the ranges of the finitely many `push` functions `σ → Γ k`
   (`σ` is finite). PvsNP has this finite set and its membership lemmas as `Sit.symSet`.
2. Transport `K`, `Λ`, `σ` and each restricted alphabet to `Fin n` along `Fintype.equivFin`.
3. `NFMachine` is a structure of naturals, `Fin`-indexed data and `TM2.Stmt` trees over `Fin`
   types. `Countable NFMachine` follows from Mathlib instances plus one lemma,
   `Countable (TM2.Stmt Γ Λ σ)` for finite `σ` and countable `Γ k`, `Λ`, `K`.
   Confirmed present at this commit: `Mathlib.Tactic.DeriveCountable`, `Countable (∀ a, π a)` for
   finite domain, `Encodable (WType β)`, `Countable (α →₀ β)`, `exists_surjective_nat`.
4. `exists_surjective_nat` gives `e : ℕ → Code`. It is used only inside noncomputable definitions.
   No decoder, no universal machine, no clocked machines: a requirement is a pair
   `(code, polynomial)` and a stage just inspects the first `p(n)` steps of a run.

The real work is the simulation lemma (N3): the normal-form machine and the original produce the
same outputs in the same number of steps, for every oracle.

**Can enumeration be avoided altogether?** Not in substance. For every fixed `B`, a non-uniform
family of query-free decision procedures computes the separating language, so no argument that
uses only "each decider makes polynomially many queries" can work. Any proof must use that there
are countably many machines. Random-oracle (Bennett-Gill) and generic-oracle (Baire category)
arguments need the same countability for their union bound or countable intersection. What can be
avoided, and is avoided above, is the explicit numbering.

**The argument.** Separating language and its verifier:

```lean
def sepLang (B : Oracle) : Language (List Bool) :=
  fun w => ∃ y : List Bool, y.length ≤ w.length ∧ y.reverse ++ w.reverse ∈ B
```

`sepLang B ∈ NP^B` for every `B`: the relation `R w y := y.reverse ++ w.reverse ∈ B` is the T3
decider after the plain function `(w, y) ↦ (w ++ y).reverse`, which is a one-loop machine (pop the
input, push the bit, skip the separator). This shape was chosen to make the machine trivial; a
"some string of length `|w|`" language would need a length comparison.

Stages. Fix a surjection onto `(decider code, polynomial)` pairs. At stage `i` with `(c, p)`: pick
`n` above the current length bound with `p(n) < 2^n`; run `c` on `0^n` with the finite oracle built
so far for `p(n)` steps; at most `p(n)` strings are queried, so some `u` of length `n` has
`u ++ 0^n` unqueried; add `u ++ 0^n` exactly when the run halted with `[false]`; raise the length
bound above `2n` and above every query length of that run. `B` is the union. For any polynomial-time
decider with oracle `B`, its normal form and time bound are some requirement `i`; by locality its
run on `0^n` under `B` is the stage-`i` run; the stage made its answer wrong.

Estimate for the half: about 1,000 lines beyond the shared foundation.

### 4.3 Which half first

`P^B ≠ NP^B` first.

- It forces the whole shared foundation (model, locality, composition, T3, normal form) with the
  smallest hand-written machine (one loop).
- It is the half where a modelling mistake about queries would surface, and the cheapest place to
  find one.
- The collapse half then adds only the recursive definition of `A`, the `pad` machine and one
  correctness argument.

## 5. Reuse from `D:\PvsNP` (HEAD `c271016`, read-only)

Same toolchain and Mathlib commit, so verbatim copies are expected to compile unchanged; this has
not been run. Files would be copied into `Relativization/Lib/` with a header naming the source
commit. `D:\PvsNP` is never modified or depended on by path.

| Source | Non-blank lines | Imports | Carries over | Used for |
|---|---|---|---|---|
| `Prog.lean` | 823 | Mathlib only | Verbatim: `Run`, `RunLe`, `Bud`, `incr`/`decr`, `xfer`, `cmp`, `forLoop`, `emit`, `copy_run`, `add_run`, `mul_run`, `xferE` | Every plain machine (`flat`, `pad`) |
| `Emb.lean` | 155 | `Prog` | Verbatim: `SEmb`, `mapS`, `stepAux_mapS`, `run_embed` | Assembling `pad` from sub-machines; template for N3 |
| `Comp.lean` | 528 | Millennium (last theorem only) | Port, not verbatim: the composite machine and every lemma, with `M₂` an oracle machine | F7 `oracleComp`. Also `pushes`, `length_stepAux`, `length_iter`, `eval_mono` for the query-length bound F5 |
| `D3OneHot.lean` 28–230, `D3Fam.MS` | ~220 | `Prog` | Extract: counter view `SK`, `SΓ`, `st`, `emitS`, `incS`, `drainS`, `xferES`, `copyS`, `mulS_run` | `pad` |
| `Pre.lean` 35–238, 718–735 | ~220 | counter view | Extract: `xferS`, `powS`, `pow_run`, `IsPoly` | `pad` (unary `(n + c)^e`) and its time bound |
| `Pkg.lean` (parts) | ~150 | | Extract: `run_height`, `xfer_drain`, `drain_run`, `outputsOfRunLe`, `eval_le_pow` | Halting cleanup and packaging of plain machines; choice of `T` |
| `Sit.lean` 467–506 | ~60 | | Extract: `PushSym`, `pushFS`, `symSet`, membership lemmas | N3 step 1 |

Not carried over: SAT/CNF, the tableau, the clause generators, `Asm`.

Limits of the reuse. `Emb.mapS` keeps the state type fixed and uses alphabet bijections; N3 needs
state and label equivalences and alphabet injections, so it is a new lemma on the same pattern.
The `Prog` primitives overwrite the whole state with a flag, so they suit machines whose state is
one `Bool`.

## 6. Definitions, targets, sub-lemmas

### 6.1 Definitions

| Id | Definition | Where |
|---|---|---|
| D1 | `Oracle`, `OracleFinTM2`, `toFinTM2`, `Cfg`, `query`, `step`, `initList`, `haltList` | §3.2 |
| D2 | `OTM2OutputsInTime`, `OTM2ComputableInPolyTime` | §3.2 |
| D3 | `InP`, `InNP`, `PEqNP`, `ClassEquality` | §3.2 |
| D4 | `NFMachine`, `NFMachine.toOracleFinTM2`; code types `DCode` (deciders) and `VCode` (verifiers with `g`, `k`) | §4.2 |
| D5 | `sepLang`; the stage sequence and `sepOracle` | §4.2 |
| D6 | `frame`, `decode`; the budget `⌊(T ∸ μ)/(D + 1)⌋`; the level functional and `univOracle` | §4.1 (decided 2026-10-07) |

```lean
structure NFMachine where
  nK : ℕ
  nΛ : ℕ
  nσ : ℕ
  a : Fin nK → ℕ
  k₀ : Fin nK
  k₁ : Fin nK
  kq : Fin nK
  main : Fin nΛ
  init : Fin nσ
  qAlpha : Fin (a kq) ≃ Bool
  m : Fin nΛ → Bool → Turing.TM2.Stmt (fun k => Fin (a k)) (Fin nΛ) (Fin nσ)
```

### 6.2 Target theorems

To be copied into `NOTES.md` before any of them is attempted (rule 2).

```lean
/-- T0 -/ theorem step_empty (tm : OracleFinTM2) (c : tm.Cfg) :
    tm.step ∅ c = (tm.toFinTM2 false).step c

/-- T1 -/ theorem inP_empty_iff {α : Type} (ea : FinEncoding α) (L : Language α) :
    InP ∅ ea L ↔ Millennium.InPolynomialTime ea L

/-- T2 -/ theorem inNP_empty_iff {α : Type} (ea : FinEncoding α) (L : Language α) :
    InNP ∅ ea L ↔ Millennium.InNondeterministicPolynomialTime ea L

/-- T2' -/ theorem classEquality_empty_iff : ClassEquality ∅ ↔ Millennium.ClayPVersusNP

/-- T3 -/ theorem oracle_inP (A : Oracle) : InP A (fin_encoding_string Bool) (· ∈ A)

/-- T4 -/ theorem inP_subset_inNP (A : Oracle) (alphabet : Type) [Fintype alphabet]
    [Nontrivial alphabet] (L : Language (List alphabet)) :
    InP A (fin_encoding_string alphabet) L → InNP A (fin_encoding_string alphabet) L

/-- T5 -/ theorem collapse : ∃ A : Oracle, PEqNP A

/-- T6 -/ theorem separation : ∃ B : Oracle, ¬ PEqNP B

/-- T7, main -/ theorem baker_gill_solovay :
    (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B)
```

Acceptance for T7: `#print axioms baker_gill_solovay` lists only `propext`, `Classical.choice`,
`Quot.sound`; the build has no `sorry`; `lake env leanchecker --fresh` passes.

### 6.3 Stretch target

```lean
/-- T8 -/ theorem baker_gill_solovay_clay :
    (∃ A : Oracle, ClassEquality A) ∧ (∃ B : Oracle, ¬ ClassEquality B)
```

The second conjunct follows from T6 by taking `alphabet := Bool`. The first needs the collapse for
every finite input alphabet: `pad` must encode input symbols as fixed-width bit blocks and
`univOracle` must decode them. Estimate 400 to 600 lines, 2 sessions.

### 6.4 Sub-lemmas

Difficulty: E = routine; M = some design or a few hundred lines; H = a session or more, with design risk.
Lines are estimates for new or ported Lean, excluding verbatim copies.

**Foundation**

| Id | Statement (informal) | Diff. | Lines | Needs |
|---|---|---|---|---|
| F1 | T0: empty-oracle step is the plain step | E | 10 | D1 |
| F2 | `step_congr`: `step A c = step A' c` if `A`, `A'` agree on `query c` | E | 15 | D1 |
| F3 | `iter_congr`: `n`-step runs agree if the oracles agree on every query made along the first | E–M | 40 | F2 |
| F4 | Halting configurations are terminal; output and halting step of a run are unique | M | 60 | D2 |
| F5 | After `n` steps, `query` has length at most its initial length plus `pushBound · n` | E–M | 80 | port of `Comp.length_iter` |
| F6 | T1, T2, T2' | E | 80 | F1, Q1 |
| F7 | `oracleComp`: plain polynomial-time function, then oracle machine | M | 600 | port of `Comp.lean` |
| F8 | T3 | E–M | 150 | D2 |
| F9 | T4 | E | 60 | F7, Millennium `LeftProjection` |

**Normal form**

| Id | Statement (informal) | Diff. | Lines | Needs |
|---|---|---|---|---|
| N1 | `Countable (TM2.Stmt Γ Λ σ)` for finite `σ`, countable `K`, `Λ`, `Γ k` | M | 80 | |
| N2 | `Countable NFMachine`, `Countable DCode`, `Countable VCode`, `Countable (Polynomial ℕ)` | E | 50 | N1 |
| **N3** | **Simulation: for an `OracleFinTM2` with finite input and output alphabets there is an `NFMachine` with matching alphabet equivalences such that, for every oracle, input, output and `t`, one outputs in time `t` iff the other does** | **H** | **400–600** | `Sit.symSet`, pattern of `Emb` |
| N4 | Every polynomial-time oracle decider has a `DCode`; every verifier has a `VCode` | M | 120 | N3 |

**Separation**

| Id | Statement (informal) | Diff. | Lines | Needs |
|---|---|---|---|---|
| B1 | `(w, y) ↦ (w ++ y).reverse` is `TM2ComputableInPolyTime` on `pair_encoding` | M | 200 | `Prog` |
| B2 | `sepLang B ∈ NP^B` for every `B` | E | 50 | B1, F7, F8 |
| B3 | A set of fewer than `2^n` strings misses some `u ++ 0^n` with `|u| = n`; every polynomial is eventually below `2^n` | E–M | 100 | |
| B4 | Stage sequence: definition by recursion with choice; invariants (length bounds strictly increase, finite oracle below the bound is final, added string was unqueried) | H | 350 | F3, F5, B3, N2 |
| B5 | Run stability: the stage-`i` run on `0^n` is the run under the final oracle for `p(n)` steps | M–H | 150 | B4, F3 |
| B6 | `sepLang sepOracle ∉ P^sepOracle`, hence T6 | M | 120 | B2, B5, F4, N4 |

**Collapse**

| Id | Statement (informal) | Diff. | Lines | Needs |
|---|---|---|---|---|
| A1 | `decode (frame i T v) = (i, T, v)`, length of `frame` | E | 80 | |
| A2 | `univOracle` by levels; fixpoint equation `x ∈ A ↔ Φ (A ∩ {|z| < |x|}) x` | M | 150 | D6, N2 |
| A3 | Counter view and power loop, extracted from PvsNP | E | 450 (ported) | `Prog` |
| A4 | `pad i c' d : w ↦ frame i ((|w| + c')^d) w.reverse` is `TM2ComputableInPolyTime` | M–H | 550 | A3, `Emb` |
| A5 | Reduction is correct: `L w ↔ pad w ∈ univOracle` for `L ∈ NP^univOracle` | M–H | 300 | A1, A2, F3, F4, F5, N4, `eval_le_pow` |
| A6 | T5 | E–M | 80 | A4, A5, F7, F8, F9 |

**Main**: T7 from T5 and T6, E, 20 lines.

### 6.5 Hardest sub-lemma

**N3, simulation by a normal-form machine.** Both halves depend on it; it is the only place where
"arbitrary Lean types as alphabets" has to be confronted; and it combines three things that are each
awkward with dependent stack alphabets `Γ : K → Type`: restricting an alphabet to a subtype (the
statement translation must carry a proof that every pushed symbol is reachable), transporting four
type families along equivalences at once, and relating `initList`/`haltList`, which Mathlib defines
with a cast on `Γ k`. It is conceptually trivial and that is the risk: it will be all bookkeeping.

Mitigations, in order:
1. Prove it as one "pullback along alphabet injections and index equivalences" lemma, with the
   configuration map going from the normal-form machine to the original (`Subtype.val` on symbols),
   so no invariant about reachable symbols is needed in the simulation itself.
2. Prototype on plain `FinTM2` first; the oracle bit adds one hypothesis (the query strings match).
3. Fallback: require `[∀ k, Fintype (Γ k)]` in `OracleFinTM2`. Then BGS needs only the relabelling
   half of N3, and the alphabet restriction moves to the direction `P ⊆ P^∅` of T1.

Second hardest: B4 with B5, the stage construction. It is the mathematical core, but it involves
no machines and no dependent types.

### 6.6 Estimate

| Block | New or ported lines |
|---|---|
| Definitions | 200 |
| Foundation F1–F9 | 1,100 |
| Normal form N1–N4 | 650–850 |
| Separation B1–B6 | 970 |
| Collapse A1–A6 | 1,600 |
| Main | 20 |
| **Total new or ported** | **about 4,500–4,800** |
| Verbatim copies (`Prog`, `Emb`) | 980 |

Allowing for the usual growth of proofs over estimates, I expect the finished repository to hold
5,500 to 8,000 lines of Lean.

Sessions, assuming sessions like the PvsNP ones:

| Session | Content |
|---|---|
| 1 | Q1 lakefile change; D1–D3; F1–F6 (model, locality, uniqueness, query length, trivial-oracle lemmas) |
| 2 | F7 `oracleComp` |
| 3 | F8, F9, B1, B2 |
| 4–5 | N1–N4 |
| 6–7 | B3–B6: **T6 done** |
| 8 | A1–A3 |
| 9–10 | A4 |
| 11 | A5, A6: **T5 and T7 done** |
| 12 | Red-team pass on definitions and statements, axiom audit, `leanchecker`, README |
| 13–14 | Stretch: T8 |

About 12 sessions for T7, plausibly 10 to 15; 2 more for T8.

### 6.7 Revision after session 1 (2026-10-07)

The tables in §6.4 and §6.6 above are the original estimates, left as written. This subsection
records what session 1 actually cost and what changes. Details and check outputs: `NOTES.md` §7.

**Done in session 1:** Q1 lakefile change; D1–D3; F1, F2, F3, F5, F6, F7, F8, F9; plus `P ⊆ P^A`
(S1–S3) and the binary instances (E1–E3), which were not separate plan items. F7 and F8/F9 were
planned for sessions 2 and 3. **Not done:** F4 (unique output), which was planned for session 1.

**Actual against estimate** (non-blank lines; the plan's line estimates do not say whether blank
lines are counted, so the comparison is approximate):

| Plan item | Estimated | Actual | Where | Note |
|---|---|---|---|---|
| Definitions D1–D3 | 200 (all of D1–D6) | 136 | `Oracle.lean` 1–127 (105), `Classes.lean` (31) | D4–D6 not written yet |
| F1, F2, F3, F5 | 145 | 138 | `Oracle.lean` 205–end | plus `depth`, not in the plan |
| Generic iteration lemmas | 0 (inside F7) | 68 | `Oracle.lean` 128–204 | shared by F3, F5, F6, F7, F8 |
| F6 (T1, T2, T2') and `P ⊆ P^A` | 80 | 195 | `Plain.lean` | **2.4×**: `P ⊆ P^∅` needs an added stack and a simulation (NOTES §7.4 item 1) |
| F7 `oracleComp` | 600 | 458 | `Comp.lean` 1–532 | port went through with one restatement over raw types |
| F8 (T3) | 150 | 106 | `Self.lean` | all four step lemmas are `rfl` |
| F9 (T4) | 60 | 14 | `Comp.lean` 533–end | |
| Root module | 0 | 15 | `Relativization.lean` | |
| **Session total** | **1,235** (items above) | **1,130** | 1,331 lines including blanks | 0.92 of estimate |

**What this says about the remaining estimates.** Not much: one data point, on the block that
was mostly a port of code that already existed. Ports and hand-written small machines came in
under (0.2–0.8×); the one item whose difficulty the plan misjudged came in at 2.4×. The remaining
blocks (N3, B4/B5, A4) are the ones with design risk, so their line estimates are kept and the
overall range is not narrowed.

| Block | Original | Revised | Reason |
|---|---|---|---|
| Definitions | 200 | 136 done + 80 (D4–D6) | |
| Foundation F1–F9 | 1,100 | 994 done + 60 (F4) | includes S1–S3, E1–E3 |
| Normal form N1–N4 | 650–850 | 650–850 | unchanged |
| Separation B1–B6 | 970 | 970 | unchanged |
| Collapse A1–A6 | 1,600 | 1,650 | +50 in A2 for the budget of NOTES §5.4, if approved |
| Main | 20 | 20 | |
| **Total new or ported** | **4,500–4,800** | **about 4,550–4,750** | 1,130 written |
| Verbatim copies (`Prog`, `Emb`) | 980 | 980 | not copied yet; first needed for B1 |

Finished repository: still 5,500 to 8,000 lines.

**Sessions.** Session 1 covered the plan's sessions 1 and 2 and the F8/F9 half of session 3.

| Session | Content |
|---|---|
| 1 (done) | Q1; D1–D3; F1–F3, F5–F9; `P ⊆ P^A` |
| 2 | F4; copy `Prog`/`Emb`; B1, B2 |
| 3–4 | N1–N4 |
| 5–6 | B3–B6: **T6 done** |
| 7 | A1–A3 |
| 8–9 | A4 |
| 10 | A5, A6: **T5 and T7 done** |
| 11 | Red-team pass, axiom audit, `leanchecker`, README |
| 12–13 | Stretch: T8 |

About 11 sessions for T7, plausibly 9 to 14; 2 more for T8.

**Corrections to earlier sections of this plan, found in session 1.** The text above is unchanged;
these supersede it.

1. §3.4 and §3.2 ("both directions are immediate"): only `P^∅ ⊆ P` is immediate. See the F6 row.
2. §4.1 ("I have not traced a citation") and §7 ("the cheap oracle is not the textbook one"):
   the self-referential oracle is reported to be Theorem 1 of Baker-Gill-Solovay 1975 itself
   (`A = K(A)`); the PSPACE-complete oracle is their Theorem 2. **Unconfirmed**: the paper has
   not yet been checked by the author; citation and its provenance: NOTES §6. It also means §2.4 item 3 should claim a formalisation of the original first
   proof, not a new route.
3. §4.1, definition of `A` (D6) — **approved 2026-10-07 and now written into §4.1**: step budget
   `⌊(T ∸ (n + 1 + n^k)) / (D + 1)⌋` instead of `T`, where `D` is the depth of the coded
   machine. With budget `T`, a machine pushing two or more symbols per step asks queries longer
   than the coded tuple, and "membership refers only to shorter strings" holds only because the
   oracle is cut off by fiat. Both versions give `P^A = NP^A`; the padding function and `T(n)`
   are the same. Argument and comparison: NOTES §5.5 and §5.8.
4. §6.4 F5: the bound uses `depth` (maximum over paths of pushes onto the query stack), not a
   port of `Comp.pushBound` (sum over branches of pushes onto any stack).

### 6.8 Revision after session 2 (2026-10-07)

**Done in session 2:** F4; D4 (`NFMachine`); N1, N2, N3, N4; decision D6 recorded in §4.1.
Session 2 of the §6.7 table was to be "F4; copy `Prog`/`Emb`; B1, B2", and N1–N4 were sessions
3–4. The copies and B1, B2 are **not done**; nothing of B3–B6, A1–A6 or T5–T8 was started.
Details and check outputs: `NOTES.md` §8.

**Actual against estimate** (non-blank lines; file headers and docstrings included):

| Plan item | Estimated | Actual | Where | Note |
|---|---|---|---|---|
| F4 | 60 | 83 | `Halt.lean` | includes the two F4' forms used by NOTES §5.7 |
| D4 `NFMachine` | (part of 80 for D4–D6) | 38 | `Normal.lean` 25–64 | |
| N1 | 80 | 84 | `Countable.lean` | hand-written `WType` injection, no `deriving`; needs finite alphabets (NOTES §4.5 item 1) |
| N2 | 50 | 134 | `Codes.lean` 22–145, 229–279 | **2×**: three code types, two enumerations, two witness machines, two countability instances |
| N3 | 400–600 | 318 | `Normal.lean` 66–end | under the range: the simulation map goes from the normal form to the original, so no reachability invariant on configurations (NOTES §4.7, §8.4) |
| N4 | 120 | 111 | `Codes.lean` 147–227, 281–end | includes the pair-alphabet translation |
| Root module | 0 | 11 | `Relativization.lean` | |
| **Session total** | **710–910** | **815** | 962 lines including blanks | inside the range |

Revised blocks (non-blank lines written so far: 1,130 + 815 = 1945):

| Block | Original | Revised | Reason |
|---|---|---|---|
| Definitions | 200 | 136 + 38 done + 50 (D5, D6) | |
| Foundation F1–F9 | 1,100 | 1077 done | complete |
| Normal form N1–N4 | 650–850 | 647 done | complete |
| Separation B1–B6 | 970 | 970 | unchanged |
| Collapse A1–A6 | 1,600 | 1,650 | unchanged (D6 approved) |
| Main | 20 | 20 | |
| **Total new or ported** | **4,500–4,800** | **about 4,650–4,750** | 1945 written |
| Verbatim copies (`Prog`, `Emb`) | 980 | 980 | not copied yet; first needed for B1 |

Finished repository: still 5,500 to 8,000 lines; the central estimate is now nearer the bottom
of that range, since the two blocks with design risk that are done (F7, N3) both came in under.

**Sessions.** Session 2 covered the plan's F4 and sessions 3–4 (N1–N4), but not the copies or
B1, B2.

| Session | Content |
|---|---|
| 1 (done) | Q1; D1–D3; F1–F3, F5–F9; `P ⊆ P^A` |
| 2 (done) | F4; D4; N1–N4; D6 decided |
| 3 | copy `Prog`/`Emb`; B1, B2 |
| 4–5 | B3–B6: **T6 done** |
| 6 | A1–A3 |
| 7–8 | A4 |
| 9 | A5, A6: **T5 and T7 done** |
| 10 | Red-team pass, axiom audit, `leanchecker`, README |
| 11–12 | Stretch: T8 |

About 10 sessions for T7, plausibly 9 to 13; 2 more for T8.

**Corrections to earlier sections of this plan, found in session 2.**

5. §4.2 item 3 and §6.4 N1: `Countable (TM2.Stmt Γ Λ σ)` needs `Finite (Γ k)` for every `k`,
   not `Countable (Γ k)` (`Option ℕ → Bool` is uncountable). Harmless: normal forms have `Fin`
   alphabets.
6. §6.4 N3: the output-alphabet equivalence needs `Finite (tm.Γ tm.k₁)`, which `OracleFinTM2`
   does not require. The normal form exists for every machine (N3a, with the output translated
   by the decoding map); the equivalence form (N3b, N3c) is stated under that hypothesis, which
   every machine inside an `OTM2ComputableInPolyTime` with finite `βΓ` satisfies.
7. §4.2 "`Countable NFMachine` follows from Mathlib instances plus one lemma": true, but the
   instance search for the nested `Σ` exceeds Lean's default size, so the fiber gets its own
   instance (NOTES §8.4 item 6). No `set_option`.
8. §6.5 mitigation 1 ("configuration map from the normal-form machine to the original") was the
   right call and is what was done; mitigations 2 and 3 were not needed.

### 6.9 Revision after session 3 (2026-10-07)

**Done in session 3:** `Prog` and `Emb` ported from `D:\PvsNP` (`c271016`) with an oracle-run
layer (NOTES §4.8, O1–O5); B1 (`Sep.revComputable`); B2 (`sepLang`, `sepLang_inNP`), plus
`sepLang_replicate_iff` for B6. This is the §6.8 table's session 3, complete. Nothing of B3–B6,
A1–A6 or T5–T8 was started. Details and check outputs: `NOTES.md` §9.

**Actual against estimate** (non-blank lines; file headers and docstrings included):

| Plan item | Estimated | Actual | Where | Note |
|---|---|---|---|---|
| copy `Prog` | 823 verbatim | 800 verbatim + 30 header | `Prog.lean` 1–39, 40–968 | compiled unchanged (namespace and header only) |
| copy `Emb` | 155 verbatim | 133 verbatim + 20 header | `Emb.lean` 1–27, 28–176 | compiled unchanged; its `iter_none` dropped (duplicate of `Relativization.iter_none`) |
| adaptation (not in the plan) | 0 | 89 + 53 | `Prog.lean` 969–1073, `Emb.lean` 177–237 | `ORun`, O2/O3 transfers, O5 packaging, `OEmbeds`, `run_embed_oracle` |
| B1 | 200 | 143 | `Sep.lean` 1–169 | one label, one step per input symbol; uses only `Prog.Run` and `TM2OutputsInTime.ofRun` |
| B2 | 50 | 25 | `Sep.lean` 171–197 | includes `sepLang_replicate_iff` |
| Root module | 0 | 10 | `Relativization.lean` | |
| **Session total** | **250 new + 978 copied** | **373 new + 933 copied** | 1,510 lines (1,295 non-blank) in the three new files | new lines inside the range once the unplanned oracle layer (142) is separated: B1 + B2 came to 168 against 250 |

Revised blocks (non-blank lines written so far: 1,945 + 373 = 2,318 new; 933 ported verbatim):

| Block | Original | Revised | Reason |
|---|---|---|---|
| Definitions | 200 | 136 + 38 done + 50 (D5, D6) | |
| Foundation F1–F9 | 1,100 | 1,077 done | complete |
| Normal form N1–N4 | 650–850 | 647 done | complete |
| Program library (oracle layer) | 0 | 142 done | unplanned; §4.8 of NOTES |
| Separation B1–B6 | 970 | 168 done + 720 (B3–B6) | B1, B2 came in at 2/3 of the estimate |
| Collapse A1–A6 | 1,600 | 1,650 | unchanged |
| Main | 20 | 20 | |
| **Total new or ported** | **4,500–4,800** | **about 4,750–4,850** | 2,318 written |
| Verbatim copies (`Prog`, `Emb`) | 980 | 933 | done |

Finished repository: still 5,500 to 8,000 lines; the repository is at 3,828 lines (3,250 non-blank)
after session 3, with the two machine-heavy blocks (A3, A4) still to come.

**Sessions.** Unchanged from §6.8 except that session 3 is done.

| Session | Content |
|---|---|
| 1 (done) | Q1; D1–D3; F1–F3, F5–F9; `P ⊆ P^A` |
| 2 (done) | F4; D4; N1–N4; D6 decided |
| 3 (done) | copy `Prog`/`Emb` (+ oracle layer); B1, B2 |
| 4–5 | B3–B6: **T6 done** |
| 6 | A1–A3 |
| 7–8 | A4 |
| 9 | A5, A6: **T5 and T7 done** |
| 10 | Red-team pass, axiom audit, `leanchecker`, README |
| 11–12 | Stretch: T8 |

About 10 sessions for T7, plausibly 9 to 13; 2 more for T8.

**Corrections to earlier sections of this plan, found in session 3.**

9. §5 "verbatim copies are expected to compile unchanged; this has not been run": run now. Both
   files compiled unchanged on the first attempt (same toolchain and Mathlib commit); the only
   edits are the module headers, the namespaces, and the removal of `Emb.iter_none`
   (`logs/session3-port-diff.txt`).
10. §5 "Limits of the reuse" and §6.4 B1 "needs `Prog`": B1 needs none of the counter
    primitives. A symbol-copying loop keeps the popped symbol in the state (`σ = Option (Bool ⊕
    Option Bool)`), so one label and one step per symbol suffice; from `Prog` it uses `Run`,
    `Run.head`, `Run.zero`, `Run.of_eq` and the packaging `TM2OutputsInTime.ofRun`. The counter
    primitives are first needed by A3/A4 (`pad`).
11. §6.4 estimate for the copies did not include an oracle layer. `Prog` is a library for plain
    programs (its `Run` is `TM2.step M` of a fixed program), and the oracle step selects the
    statement by the oracle's answer, so the two are connected by the transfer lemmas
    `ORun.of_run` (all labels oblivious) and `ORun.of_run_visited` (visited labels oblivious), and
    `Emb.run_embed` gets an oracle-host twin. 142 lines, NOTES §4.8. No machine of the plan needs
    more: every `Prog`-built machine is plain, and the oracle machines are hand-written or composed.

### 6.10 Revision after session 4 (2026-10-07)

**Done in session 4:** B3 (`Count`), the query set of a run with the instance L4' of the sharp
locality lemma (`Queries`), B4, B5, B6 (`Stage`): `sepOracle`, `sepLang_not_inP`,
`sepOracle_not_pEqNP`. This is the §6.9 table's sessions 4–5 ("B3–B6: T6 done") in one
session, except that T6 itself (`∃ B, ¬ PEqNP B`) is not stated, by the session brief: it is
`⟨sepOracle, sepOracle_not_pEqNP⟩` and belongs to the final assembly. Nothing of A1–A6 or
T5–T8 was started. Details and check outputs: `NOTES.md` §4.10 and §10.

**Actual against estimate** (non-blank lines; file headers and docstrings included):

| Plan item | Estimated | Actual | Where | Note |
|---|---|---|---|---|
| B3 | 100 | 72 | `Count.lean` | both halves as the plan stated them; the polynomial bound is elementary (`m < 2^m` at `m = n / (d+1)`), no analysis import |
| query set, L4' (not in the plan) | 0 | 66 | `Queries.lean` | the finite set of queries asked, so that the counting argument (B3a) and the sharp locality lemma L4 speak about the same object; see the correction below |
| B4 | 350 | 154 | `Stage.lean` 1–210 | **0.44×**: no fixpoint, no finiteness, no `if`; the recursion carries `(bound, F)` and every invariant is `omega` over `boundAt`/`lenAt` |
| B5 | 150 | 28 | `Stage.lean` 211–240 | 0.19×: one application of L6' once `agree_on_queries` is proved |
| B6 | 120 | 62 | `Stage.lean` 241–308 | 0.52×: `exists_dcode_decides` + `dEnum_surjective` + B5 + F4' + `sepLang_replicate_iff` |
| Root module | 0 | 10 | `Relativization.lean` | |
| **Session total** | **720** | **392** | 476 lines (382 non-blank) in the three new files | 0.54 of estimate; 0.44 on the planned items alone |

Revised blocks (non-blank lines written so far: 2,318 + 392 = 2,710 new; 933 ported verbatim):

| Block | Original | Revised | Reason |
|---|---|---|---|
| Definitions | 200 | 136 + 38 + 12 done + 30 (D6) | D5 (`sepOracle`, stage data) is done, 12 lines of definitions proper |
| Foundation F1–F9 | 1,100 | 1,077 done | complete |
| Normal form N1–N4 | 650–850 | 647 done | complete |
| Program library (oracle layer) | 0 | 142 done | unplanned; NOTES §4.8 |
| Query set, L4' | 0 | 66 done | unplanned; NOTES §4.10 |
| Separation B1–B6 | 970 | 168 + 304 = 472 done | **complete** (T6 is one line in the assembly); 0.49× of the estimate |
| Collapse A1–A6 | 1,600 | 1,650 | unchanged |
| Main | 20 | 20 | |
| **Total new or ported** | **4,500–4,800** | **about 4,350–4,450** | 2,710 written; the separation block came in at half |
| Verbatim copies (`Prog`, `Emb`) | 980 | 933 | done |

Finished repository: the repository is at 4,316 lines (3,642 non-blank) after session 4. The
remaining blocks are the collapse (A1–A6, estimate 1,650, of which A3/A4 are the two
machine-heavy items) and the assembly. The earlier range 5,500–8,000 is now too wide at the
top: every block with design risk that is finished (F7, N3, B4/B5) came in under its estimate,
and the collapse's design (NOTES §5) is settled. Revised: **5,500 to 6,500 lines**.

**Sessions.** Session 4 covered the §6.9 table's sessions 4 and 5.

| Session | Content |
|---|---|
| 1 (done) | Q1; D1–D3; F1–F3, F5–F9; `P ⊆ P^A` |
| 2 (done) | F4; D4; N1–N4; D6 decided |
| 3 (done) | copy `Prog`/`Emb` (+ oracle layer); B1, B2 |
| 4 (done) | B3–B6 (`sepOracle_not_pEqNP`; T6 pending assembly) |
| 5 | A1–A3: `frame`/`decode`, `univOracle` by levels with the fixpoint equation (†) of NOTES §5.6, counter view and power loop from PvsNP |
| 6–7 | A4: `pad` |
| 8 | A5, A6; T5, T6, T7: **T5, T6 and T7 done** |
| 9 | Red-team pass, axiom audit, `leanchecker --fresh`, README |
| 10–11 | Stretch: T8 |

About 8 sessions for T7 (was 10), plausibly 8 to 11; 2 more for T8. The uncertainty is now
concentrated in A4 (`pad` on the counter view, §7 "`pad` on the counter view") and in A2/A5
(the fixpoint argument of NOTES §5.6, the one place a locality argument with budget 0 is needed,
§7.4 item 3).

**Corrections to earlier sections of this plan, found in session 4.**

12. §4.2 "by locality its run on `0^n` under `B` is the stage-`i` run" and §6.4 B4 "needs F3":
    correct, but the locality needed is the **sharp** form F3/L4 (`iter_congr`, queries actually
    asked), not the length form L5/L6. The string a stage adds has length `2n`, which is in
    general within the length bound `n + p(n)·D` of the stage's own run, so the length form
    cannot show the stage's run is unaffected by it; the sharp form can, because the string was
    chosen unqueried. NOTES §4.10 and §10.4 item 1. No definition was changed; the plan's choice
    of F3 was right and F5 (length) is used only for the strings of later stages.
13. §6.4 B4 "finite oracle": the stage oracle `F_i` is a `Set`, not a `Finset`; finiteness is
    never used (only `mem_sepOracle`). `B` is a primitive recursion carrying `(bound, F)`, with
    two `Classical.choose`s per stage and a `Prop`-valued decision in a set-builder, so no
    `Decidable` instance and no `if`.
14. §6.4 B3 "every polynomial is eventually below `2^n`": proved in that form
    (`eventually_eval_lt_two_pow`) with elementary arithmetic; no analysis import was needed.
15. §6.6/§6.9 schedule: B3–B6 took one session, not two; T6 is deferred to the assembly by the
    session-4 brief, which keeps all of T5–T8 together.

### 6.11 Revision after session 5 (2026-10-08)

**Done in session 5:** A1 (`Frame`: frames and their decoding, both directions), A2 (`Univ`:
`univOracle` by levels, the plan's equation (★), Proposition 5, "truncation is invisible", the
untruncated self-referential equation (†) `x ∈ A ↔ Φ(A, x)`, and uniqueness), A3 (`Counter`:
the counter view and the power loop, verbatim from PvsNP). The fixpoint argument, the risk
named in §6.10 for A2/A5, is proved: `Univ.mem_univOracle`, with the budget-0 case handled by
the empty query set (NOTES §4.11). Nothing of A4–A6 or T5–T8 was started, by the session
brief. Details and check outputs: `NOTES.md` §4.11 and §11.

**Actual against estimate** (non-blank lines; file headers and docstrings included):

| Plan item | Estimated | Actual | Where | Note |
|---|---|---|---|---|
| A1 | 80 | 85 | `Frame.lean` | 1.06×; `decode` in both directions (`decode_eq_some_iff`), as A2 needs |
| A2 | 150 | 167 | `Univ.lean` | 1.11×; includes (★), Proposition 5, (†) and the uniqueness half of Theorem 6 (not in the plan's row) |
| A3 | 450 (ported) | 365 | `Counter.lean` | 0.81×; 337 non-blank verbatim (the two PvsNP `[LIB]` sections, 377 lines) plus 28 for the header, `MS`, `ofRunLe` |
| Root module | 0 | 9 | `Relativization.lean` | |
| **Session total** | **680** | **626** | 722 lines (617 non-blank) in the three new files | 0.92 of estimate; 1.09 on A1–A2, the new proofs |

Revised blocks (non-blank lines written so far: 2,710 + 289 = 2,999 new; 933 + 337 = 1,270
ported verbatim):

| Block | Original | Revised | Reason |
|---|---|---|---|
| Definitions | 200 | 136 + 38 + 12 + 30 done | D6 is 30 lines of `Univ.lean` (`M`, `mu`, `budget`, `input`, `Acc`, `Phi`, `level`, `univOracle`) |
| Foundation F1–F9 | 1,100 | 1,077 done | complete |
| Normal form N1–N4 | 650–850 | 647 done | complete |
| Program library (oracle layer) | 0 | 142 done | NOTES §4.8 |
| Query set, L4' | 0 | 66 done | NOTES §4.10 |
| Separation B1–B6 | 970 | 472 done | complete (T6 is one line in the assembly) |
| Collapse A1–A3 | 680 | 617 done | **complete**; the fixpoint risk is retired |
| Collapse A4–A6 | 930 | 930 | A4 550 (`pad`), A5 300, A6 80; unchanged |
| Main | 20 | 20 | |
| **Total new or ported** | **4,500–4,800** | **about 4,350–4,450** | 3,336 non-blank written (2,999 new, 337 ported this session); unchanged range |
| Verbatim copies (`Prog`, `Emb`, counter view) | 980 | 1,270 | done |

Finished repository: 5,049 lines (4,268 non-blank) after session 5. Remaining: A4–A6
(estimate 930) and the assembly (20), then the stretch. Revised range unchanged: **5,500 to
6,500 lines**.

**Sessions.**

| Session | Content |
|---|---|
| 1 (done) | Q1; D1–D3; F1–F3, F5–F9; `P ⊆ P^A` |
| 2 (done) | F4; D4; N1–N4; D6 decided |
| 3 (done) | copy `Prog`/`Emb` (+ oracle layer); B1, B2 |
| 4 (done) | B3–B6 (`sepOracle_not_pEqNP`; T6 pending assembly) |
| 5 (done) | A1–A3; (†) `Univ.mem_univOracle` proved |
| 6–7 | A4: `pad` as a `TM2ComputableInPolyTime` (decision first: embed the counter sub-machine with `Emb.run_embed`, PvsNP `Pre.lean` `[FULL]` as template, or give the counter view an input stack) |
| 8 | A5 (the reduction `L w ↔ pad w ∈ univOracle`, from (†), `Phi_frame`, N4v', F4', `eval_le_pow`), A6, T5, T6, T7: **T5, T6 and T7 done** |
| 9 | Red-team pass, axiom audit, `leanchecker --fresh`, README |
| 10–11 | Stretch: T8 |

Still about 8 sessions for T7, plausibly 8 to 10; 2 more for T8. The remaining uncertainty is
A4 alone (§7 "`pad` on the counter view"); A5 is now a chain of proved lemmas plus one
polynomial bound (`eval_le_pow`, 30 lines in PvsNP `Pkg.lean`, to be ported).

**Corrections to earlier sections of this plan, found in session 5.**

16. §6.4 A2 lists only the truncated equation (★) `x ∈ A ↔ Φ(A ∩ {|z| < |x|}) x`. That is
    true and is what the levels give, but A5 (§5.7 of NOTES) needs the untruncated (†)
    `x ∈ A ↔ Φ(A, x)`, which §4.1 of this plan states in prose. Both are proved
    (`Univ.mem_univOracle_iff_trunc`, `Univ.mem_univOracle`); the step between them is
    Proposition 5 plus L6'. NOTES §4.11.
17. §6.4 A3 "450 ported": the two PvsNP `[LIB]` sections are 377 lines. `pow_run` uses
    `nlinarith`, which needs `Mathlib.Tactic.Linarith`; `Prog`'s imports do not provide it, so
    `Counter.lean` adds that import (header only; the bodies are verbatim,
    `logs/session5-port-diff.txt`). The port also brings the first `deriving` clauses of the
    repository (`SK`, `MS`, `PW`), copied from PvsNP; NOTES §11.4 item 3.
18. §7 "`pad` on the counter view" is the one open design point of the collapse half; the two
    routes are recorded in NOTES §4.11 (A3, "How A4 will use it"). Not decided this session.
19. §7.4 item 3 of NOTES and §6.10 above ("the one place a locality argument with budget 0 is
    needed"): confirmed. At budget 0 the query set of the run is empty (`Finset.range 0`), so
    Proposition 5 is vacuous there, while the length-form bound `μ_i(n) ≤ |x|` is false for
    small `T`. The sharp form L4'/L6' is what is used, as the plan said.

### 6.12 Revision after session 6 (2026-10-08)

**Done in session 6:** A4, complete in one session (the schedule in §6.11 allowed two). The
design decision was recorded first (NOTES §4.12: route E, embed the counter sub-machine into a
host with an input stack through `Emb.runLe_embed`; route V, an input stack in the counter view,
assessed and not taken), then `padFun`, the machine `Pad.padTM`, its run `Pad.pad_run`
(correctness and the time bound `padB` in one `RunLe`), `IsPoly` (ported) and
`Pad.padComputable : TM2ComputableInPolyTime … (padFun i c' d)`. No session 1–5 definition
changed (olean hashes, NOTES §12.5 (e)). Nothing of A5, A6 or T5–T8 was started, by the
session brief. Details and check outputs: `NOTES.md` §4.12 and §12.

**Actual against estimate** (non-blank lines; file headers and docstrings included):

| Plan item | Estimated | Actual | Where | Note |
|---|---|---|---|---|
| A4: types, programs, machine, bound | — | 61 (+28 header) | `Pad.lean` `[DEF]` | `PC`, `PK`, `PΓ`, `CL`, `PL`, `cprog`, `padEmb`, `rdStmt`, `pprog`, `padTM`, `padB` |
| A4: counter sub-run | — | 47 | `[CNT]` | `cprog_run`, with `F0`–`F3`, `cB`, `rep_singleton`; `pow_run` reused unchanged |
| A4: copy loop | — | 67 | `[RD]` | `pst`, four `update_pst_*`, two step lemmas, `rd_run` |
| A4: embedding, whole run | — | 14 + 42 | `[EMB]`, `[RUN]` | `embeds`, `agree`, `eq_pst_of_agree`; `initList_pad`, `haltList_pad`, `pad_run` |
| A4: polynomial, packaging | — | 14 + 30 | `[POLY]`, `[PKG]` | `IsPoly` (13 verbatim), `padB_poly`, `padComputable` |
| **A4** | **550** | **303** | `Pad.lean` (363 lines) | **0.55×**; 290 new, 13 ported |
| Root module | 0 | 5 | `Relativization.lean` | |
| **Session total** | **550** | **308** | | 0.56 of estimate |

Revised blocks (non-blank lines written so far: 2,999 + 295 = 3,294 new; 1,270 + 13 = 1,283
ported verbatim):

| Block | Original | Revised | Reason |
|---|---|---|---|
| Definitions | 200 | 216 done | unchanged |
| Foundation F1–F9 | 1,100 | 1,077 done | complete |
| Normal form N1–N4 | 650–850 | 647 done | complete |
| Program library (oracle layer) | 0 | 142 done | NOTES §4.8 |
| Query set, L4' | 0 | 66 done | NOTES §4.10 |
| Separation B1–B6 | 970 | 472 done | complete (T6 is one line in the assembly) |
| Collapse A1–A3 | 680 | 617 done | complete |
| Collapse A4 | 550 | 303 done | **complete**; route E; the §7 risk "`pad` on the counter view" is retired |
| Collapse A5–A6 | 380 | 380 | A5 300 (30 of them `eval_le_pow`, ported), A6 80; unchanged |
| Main | 20 | 20 | |
| **Total new or ported** | **4,500–4,800** | **about 4,050–4,150** | 3,644 non-blank written (3,294 new, 350 ported in this row; the 933 of `Prog`/`Emb` are in the next row) |
| Verbatim copies (`Prog`, `Emb`, counter view, `IsPoly`) | 980 | 1,283 | done |

Finished repository: 5,419 lines (4,576 non-blank) after session 6. Remaining: A5–A6
(estimate 380) and the assembly (20), about 480 lines with headers, so about 5,900 lines in
all; the range **5,500 to 6,500 lines** is unchanged, now at its lower half.

**Exact remaining work for T7** (brief item 3), all in one new file `Relativization/Collapse.lean`
unless the brief for session 7 says otherwise:

1. Port `eval_le_pow` and `pow_weaken` from PvsNP `Pkg.lean` 391–416 (`eval_mono` already exists
   as `Comp.eval_mono`): `∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c)^e`. About 30 lines, verbatim.
2. The exponent pair: for the verifier code `i` and its polynomial `p`, apply `eval_le_pow` to
   `q := X + 1 + X^(vEnum i).k + C ((Univ.M i).depth + 1) * p.comp (X + 1 + X^(vEnum i).k)` to
   get `c', d` with `(n + c')^d ≥ Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n)`.
   The budget lemma `p.eval (Univ.mu i n) ≤ Univ.budget i ((n + c')^d) n`
   (`Nat.le_div_iff_mul_le`). About 40 lines.
3. From N4v' (`exists_vcode_of_verifier h k`) with `O := univOracle`, for every `w` and every
   `y` with `|y| ≤ |w|^k`: `M_i^A` outputs `[outE.symm (f (w, y))]` on `Univ.input i w (y.map ρ)`
   within `p.eval (|w| + 1 + |y|) ≤ p.eval (μ_i |w|) ≤ budget` (time weakening of
   `OTM2OutputsInTime`, `eval_mono`). Then F4' (unique output, session 2) turns "outputs
   `[f(w,y)]` within the budget" into "outputs `[true]` within the budget ↔ `f (w, y) = true`".
   About 60 lines.
4. `Univ.Acc univOracle i ((|w| + c')^d) w.reverse ↔ ∃ y : List Γ₁, |y| ≤ |w|^k ∧ f (w, y) = true`
   (certificates transported along `ρ : Γ₁ ≃ Fin g_i`, `List.length_map`,
   `List.reverse_reverse`). About 50 lines.
5. **A5**, the reduction: `L w ↔ padFun i c' d w ∈ univOracle` from (†) `Univ.mem_univOracle`,
   `Univ.Phi_frame`, items 3–4 and `InNP`'s two clauses. About 40 lines.
6. **A6 / T5**: `L ∈ P^A` from `oracleComp univOracle (Pad.padComputable i c' d) hg` with
   `⟨g, hg, hgA⟩ := oracle_inP univOracle` (T3) and `fun w => g (padFun i c' d w)`; with T4
   (`inP_subset_inNP`), `PEqNP univOracle`. About 60 lines.
7. **T6**: `¬ PEqNP sepOracle` is `sepOracle_not_pEqNP` (session 4), one line. **T7**: the
   conjunction of T5 and T6 as stated in §6.2. About 20 lines, with the root-module entry.

**Sessions.**

| Session | Content |
|---|---|
| 1 (done) | Q1; D1–D3; F1–F3, F5–F9; `P ⊆ P^A` |
| 2 (done) | F4; D4; N1–N4; D6 decided |
| 3 (done) | copy `Prog`/`Emb` (+ oracle layer); B1, B2 |
| 4 (done) | B3–B6 (`sepOracle_not_pEqNP`; T6 pending assembly) |
| 5 (done) | A1–A3; (†) `Univ.mem_univOracle` proved |
| 6 (done) | A4 complete (`Pad.padComputable`), route E; one session instead of two |
| 7 | A5 (items 1–5 above), A6, T5, T6, T7: **T5, T6 and T7 done** |
| 8 | Red-team pass, axiom audit, `leanchecker --fresh`, README |
| 9–10 | Stretch: T8 |

Eight sessions for T7, as the §6.11 schedule said, now at the lower end of its "8 to 10";
two more for T8. The remaining uncertainty is A5's item 3 (the time weakening and F4' in the
exact `OTM2OutputsInTime` form), estimated above at 60 lines; the machine-building risk of the
collapse half is gone.

**Corrections to earlier sections of this plan, found in session 6.**

20. §6.4 A4 "550 lines" and §7 "the least certain machine estimate": 303 non-blank lines, in one
    session. The host-side bookkeeping (copy loop, embedding, `initList`/`haltList`) was 123
    lines and the counter arithmetic 47; `pow_run` was reused unchanged, and nothing in the
    counter view had to be generalised.
21. §6.11 scheduled A4 over sessions 6–7. It is done in session 6; the former session 8 content
    moves to session 7 and the schedule shortens by one session.
22. §7 "`pad` on the counter view" is retired: NOTES §4.12 records both routes and the choice of
    route E (embedding), and §12 the result. The time bound `padB c' d n` does not depend on
    `i`, so the polynomial of `padComputable` is the same for all codes with the same `c', d`.

## 7. Risks and open points

- **Faithfulness of option H.** The "one oracle bit per step" convention is equivalent to the
  query-state model for polynomial-time classes, but that equivalence would be a paper argument
  unless a classical variant and a simulation are also formalised. Not in the estimate.
- **The cheap oracle is not the textbook one.** T5 will be a theorem about `univOracle`, which is
  not PSPACE-complete in any formalised sense. The statement `∃ A, PEqNP A` is unaffected.
- **N1** may fall to `deriving instance Countable for Turing.TM2.Stmt`, or may need a hand-written
  injection; the 80 lines assume the latter.
- **`pad` on the counter view.** PvsNP's counter view has an output stack and counters but no input
  stack; `pad` needs one, either by extending the stack type or by embedding. Included in A4's
  estimate, but it is the least certain machine estimate. **Retired in session 6:** embedding
  (route E), NOTES §4.12 and §12; 303 lines against the estimate of 550.
- **Certificate bound `|y| ≤ |w|^k`** is inherited from the Clay formulation, including its
  behaviour on inputs of length 0 and 1. The separating language uses `k = 1`, where it is exact.
- **Prior work could appear.** PleaNP is active and has BGS as a stated goal.
