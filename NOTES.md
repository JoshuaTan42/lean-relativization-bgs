# NOTES — Baker-Gill-Solovay in Lean 4 + Mathlib

Working notes. `PLAN.md` holds the approved plan; this file holds the statements (rule 2), the
paper proofs, the lemma table and the check outputs.

Status legend: **stated** = written here, no Lean proof; **proved** = Lean proof compiled and
axiom-checked (output quoted in §7). Nothing is committed.

Contents: §1 setup record · §2 definitions · §3 target statements · §4 statements for session 1 ·
§5 paper proof of the collapse oracle · §6 literature · §7 lemma table and checks.

---

## 1. Setup record (2026-10-07, session 1)

Decision 1 (add LeanMillenniumPrizeProblems at `603053d`) applied to `lakefile.toml` exactly as
in PLAN §1.3.

Free space before: `C 13.78 GB free`, `D 267.42 GB free`. After: `C 13.77`, `D 267.31`.
(The 0.01 GB on C: is not this project's cache: the Mathlib download cache on C: was
`8542 files, 412.2 MB`, newest write `25 September 2026 6:31:27 PM`, both before and after.)

`MATHLIB_NO_CACHE_ON_UPDATE=1 lake update problems`:

```
info: problems: cloning https://github.com/lean-dojo/LeanMillenniumPrizeProblems
info: problems: checking out revision '603053dc267cf3efe422f438eb78098c0ececd6f'
info: toolchain not updated; already up-to-date
info: Physlib: cloning https://github.com/HEPLean/PhysLean
info: Physlib: checking out revision '3dddd61e231b2f8936dbaa1460dc60df71bc434d'
info: doc-gen4: cloning https://github.com/leanprover/doc-gen4
info: doc-gen4: checking out revision '0bc516c1b9db83658d6475c40d9b1ed71219b921'
info: leansqlite: cloning https://github.com/leanprover/leansqlite
info: leansqlite: checking out revision '0be4df908d1a8e75b58961041e2b4973692623df'
info: UnicodeBasic: cloning https://github.com/fgdorais/lean4-unicode-basic
info: UnicodeBasic: checking out revision 'a2e430a4c9d3ad24078b8581fe0162fc5b0c9a6c'
info: BibtexQuery: cloning https://github.com/dupuisf/BibtexQuery
info: BibtexQuery: checking out revision '5d31b64fb703c5d77f6ef4d1fb958f9bdf1ea539'
info: MD4Lean: cloning https://github.com/acmepjz/md4lean
info: MD4Lean: checking out revision '6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5'
info: mathlib: running post-update hooks
exit: 0
```

Manifest comparison (script: every package of the new manifest against
`D:\PvsNP\lake-manifest.json` and against the manifest from before the change):

```
BibtexQuery        new=5d31b64f…  pvsnp=5d31b64f…  before=None       SAME as PvsNP
Cli                new=92564e57…  pvsnp=92564e57…  before=92564e57…  SAME as PvsNP
LeanSearchClient   new=c5d5b8fe…  pvsnp=c5d5b8fe…  before=c5d5b8fe…  SAME as PvsNP
MD4Lean            new=6a3fb240…  pvsnp=6a3fb240…  before=None       SAME as PvsNP
Physlib            new=3dddd61e…  pvsnp=3dddd61e…  before=None       SAME as PvsNP
Qq                 new=f4632499…  pvsnp=f4632499…  before=f4632499…  SAME as PvsNP
UnicodeBasic       new=a2e430a4…  pvsnp=a2e430a4…  before=None       SAME as PvsNP
aesop              new=e3cb2f74…  pvsnp=e3cb2f74…  before=e3cb2f74…  SAME as PvsNP
batteries          new=fa08db58…  pvsnp=fa08db58…  before=fa08db58…  SAME as PvsNP
importGraph        new=5c7542ed…  pvsnp=5c7542ed…  before=5c7542ed…  SAME as PvsNP
leansqlite         new=0be4df90…  pvsnp=0be4df90…  before=None       SAME as PvsNP
mathlib            new=fabf563a7c95a166b8d7b6efca11c8b4dc9d911f  pvsnp=fabf563a7c95a166b8d7b6efca11c8b4dc9d911f  before=fabf563a7c95a166b8d7b6efca11c8b4dc9d911f  SAME as PvsNP
plausible          new=63045536…  pvsnp=63045536…  before=63045536…  SAME as PvsNP
problems           new=603053dc267cf3efe422f438eb78098c0ececd6f  pvsnp=None  before=None  new git dep (PvsNP uses a path dep)
proofwidgets       new=24b0d9dc…  pvsnp=24b0d9dc…  before=24b0d9dc…  SAME as PvsNP
doc-gen4           new=0bc516c1…  pvsnp=0bc516c1…  before=None       SAME as PvsNP
ALL MATCH
```

(Hashes abbreviated here with `…` except Mathlib and problems; the script compared the full
40-character values and printed `ALL MATCH`. `problems` has no revision in the PvsNP manifest
because PvsNP depends on it by path; the checkout there is at
`603053dc267cf3efe422f438eb78098c0ececd6f`, read with `git rev-parse HEAD`.)

`lake exe cache unpack` (cannot download), then `lake exe cache get`:

```
== unpack ==
Already decompressed 8542 file(s)
exit: 0
== get ==
Current branch: HEAD
Using cache (Azure) from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8542 file(s)
exit: 0
```

---

## 2. Definitions (D1–D3), as approved in PLAN §3.2

Namespace `Relativization`. `Language`, `pair_encoding`, `fin_encoding_string` are the
`Millennium` ones.

```lean
abbrev Oracle := Set (List Bool)

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

def OracleFinTM2.toFinTM2 (tm : OracleFinTM2) (b : Bool) : FinTM2      -- program `fun l => tm.m l b`
def OracleFinTM2.Cfg (tm : OracleFinTM2) : Type := Turing.TM2.Cfg tm.Γ tm.Λ tm.σ
def OracleFinTM2.query (tm : OracleFinTM2) (c : tm.Cfg) : List Bool :=
  (c.stk tm.kq).map tm.queryAlphabet
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

def InP (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (f : α → Bool) (_ : OTM2ComputableInPolyTime A ea.encode finEncodingBoolBool.encode f),
    ∀ a, L a ↔ f a = true

def InNP (A : Oracle) {α : Type} (ea : FinEncoding α) (L : Language α) : Prop :=
  ∃ (Γ₁ : Type) (_ : Fintype Γ₁) (R : α → List Γ₁ → Prop) (k : ℕ),
    InP A (pair_encoding ea (fin_encoding_string Γ₁)) (fun p => R p.1 p.2) ∧
      ∀ a, L a ↔ ∃ y : List Γ₁, y.length ≤ (ea.encode a).length ^ k ∧ R a y

def PEqNP (A : Oracle) : Prop :=
  ∀ L : Language (List Bool),
    InP A (fin_encoding_string Bool) L ↔ InNP A (fin_encoding_string Bool) L

def ClassEquality (A : Oracle) : Prop :=
  ∀ (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet] (L : Language (List alphabet)),
    InP A (fin_encoding_string alphabet) L ↔ InNP A (fin_encoding_string alphabet) L
```

One definition is added this session, needed to state query locality ("depth M"):

```lean
/-- Maximum number of pushes onto stack `k` along one root-to-leaf path of a statement. -/
def pushDepth (k : K) : TM2.Stmt Γ Λ σ → ℕ
  | .push k' _ q => (if k' = k then 1 else 0) + pushDepth k q
  | .peek _ _ q | .pop _ _ q | .load _ q => pushDepth k q
  | .branch _ q₁ q₂ => max (pushDepth k q₁) (pushDepth k q₂)
  | .goto _ | .halt => 0

/-- `depth M`: the most symbols one step can push onto the query stack. -/
def OracleFinTM2.depth (tm : OracleFinTM2) : ℕ :=
  Finset.univ.sup fun p : tm.Λ × Bool => pushDepth tm.kq (tm.m p.1 p.2)
```

`depth` counts pushes onto the query stack only. That is the smallest number for which the
growth lemma (L2 below) holds for every machine, so locality stated with it implies locality
stated with any coarser depth (pushes onto all stacks, or PvsNP's `Sit.depth`, which also counts
pops and peeks).

---

## 3. Target statements (PLAN §6.2 and §6.3), copied before any proof

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

/-- T8, stretch -/ theorem baker_gill_solovay_clay :
    (∃ A : Oracle, ClassEquality A) ∧ (∃ B : Oracle, ¬ ClassEquality B)
```

T5, T6, T7, T8 are **not** attempted this session.

---

## 4. Statements for session 1 (written before the Lean proofs)

### 4.1 Trivial oracle, binary alphabet (the form asked for in the session brief)

T1 and T2 hold for every encoding; these are their instances at `fin_encoding_string Bool`,
plus the class-equality form.

```lean
/-- E1 -/ theorem inP_empty_bool_iff (L : Language (List Bool)) :
    InP ∅ (fin_encoding_string Bool) L ↔
      Millennium.InPolynomialTime (fin_encoding_string Bool) L

/-- E2 -/ theorem inNP_empty_bool_iff (L : Language (List Bool)) :
    InNP ∅ (fin_encoding_string Bool) L ↔
      Millennium.InNondeterministicPolynomialTime (fin_encoding_string Bool) L

/-- E3 -/ theorem pEqNP_empty_iff :
    PEqNP ∅ ↔ ∀ L : Language (List Bool),
      Millennium.InPolynomialTime (fin_encoding_string Bool) L ↔
        Millennium.InNondeterministicPolynomialTime (fin_encoding_string Bool) L
```

### 4.2 Plain machines inside oracle machines (`P ⊆ P^A`)

An `OracleFinTM2` must have a query stack with alphabet `≃ Bool`; a `FinTM2` need not have any
such stack. So a plain machine becomes an oracle machine by **adding one unused stack**
(`K := Option M.K`, query stack `none`). This is a statement translation and a one-step
simulation, not a definitional unfolding (PLAN §3.4 called this direction immediate; it is not).

```lean
/-- S1 -/ def OTM2ComputableInPolyTime.ofPlain (A : Oracle) {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : TM2ComputableInPolyTime ea eb f) : OTM2ComputableInPolyTime A ea eb f

/-- S2 -/ def OTM2ComputableInPolyTime.toPlain {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : OTM2ComputableInPolyTime ∅ ea eb f) : TM2ComputableInPolyTime ea eb f

/-- S3, P ⊆ P^A -/ theorem inP_of_inPolynomialTime (A : Oracle) {α : Type} (ea : FinEncoding α)
    (L : Language α) : Millennium.InPolynomialTime ea L → InP A ea L
```

Both `ofPlain` and `toPlain` keep the alphabets' equivalences and the time polynomial unchanged.

### 4.3 Query locality

```lean
/-- L1 -/ theorem OracleFinTM2.step_congr (tm : OracleFinTM2) {A A' : Oracle} (c : tm.Cfg)
    (h : tm.query c ∈ A ↔ tm.query c ∈ A') : tm.step A c = tm.step A' c

/-- L2, growth -/ theorem OracleFinTM2.query_length_step (tm : OracleFinTM2) (A : Oracle)
    {c c' : tm.Cfg} (h : tm.step A c = some c') :
    (tm.query c').length ≤ (tm.query c).length + tm.depth

/-- L3 -/ theorem OracleFinTM2.query_length_iter (tm : OracleFinTM2) (A : Oracle) (n : ℕ)
    (c d : tm.Cfg) (h : (flip bind (tm.step A))^[n] (some c) = some d) :
    (tm.query d).length ≤ (tm.query c).length + n * tm.depth

/-- L4, sharp form: only the queries actually asked matter -/
theorem OracleFinTM2.iter_congr (tm : OracleFinTM2) {A A' : Oracle} (n : ℕ) (c : tm.Cfg)
    (h : ∀ j < n, ∀ d, (flip bind (tm.step A))^[j] (some c) = some d →
      (tm.query d ∈ A ↔ tm.query d ∈ A')) :
    (flip bind (tm.step A))^[n] (some c) = (flip bind (tm.step A'))^[n] (some c)

/-- L5, query locality -/
theorem OracleFinTM2.locality (tm : OracleFinTM2) {A A' : Oracle} (l : List (tm.Γ tm.k₀)) (t : ℕ)
    (h : ∀ z : List Bool, z.length ≤ l.length + t * tm.depth → (z ∈ A ↔ z ∈ A'))
    {n : ℕ} (hn : n ≤ t) :
    (flip bind (tm.step A))^[n] (some (tm.initList l)) =
      (flip bind (tm.step A'))^[n] (some (tm.initList l))

/-- L6, the same for outputs -/
theorem OracleFinTM2.outputsInTime_congr (tm : OracleFinTM2) {A A' : Oracle}
    (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) (t : ℕ)
    (h : ∀ z : List Bool, z.length ≤ l.length + t * tm.depth → (z ∈ A ↔ z ∈ A')) :
    Nonempty (OTM2OutputsInTime A tm l l' t) ↔ Nonempty (OTM2OutputsInTime A' tm l l' t)
```

"Input length" in L5 is `l.length`: the query stack starts as the input if `kq = k₀` and empty
otherwise, so its initial length is at most `l.length` in both cases.

### 4.4 Composition (needed for T4)

`P^A ⊆ NP^A` needs "plain polynomial-time function, then oracle machine". Millennium leaves
plain composition as a hypothesis (`PolynomialTimeComputableComposition`); PvsNP proved it in
`Comp.lean`. This is the port with an oracle machine in second position (F7 of the plan, moved
into this session because T4 was asked for).

```lean
/-- F7 -/ def oracleComp (A : Oracle) {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : OTM2ComputableInPolyTime A eβ eγ g) :
    OTM2ComputableInPolyTime A eα eγ (g ∘ f)
```

Supporting statements, all about one fixed machine and proved by induction on a statement or on
the number of steps: `length_stepAux` (a statement lengthens stack `k` by at most `pushDepth k`),
`stepAux_liftS` / `stepAux_lift₁` / `stepAux_lift₂` (a lifted statement acts on the lifted stacks
as the original does), `iter_map` (a step-commuting embedding commutes with iteration), the four
copy-loop steps and the two copy loops of the composite machine.

---

## 5. Paper proof: the self-referential oracle is well defined and gives `P^A = NP^A`

No Lean in this section. Everything here is to be formalised in later sessions (A1–A6) except
Lemmas 1–3, which are L2–L5 of §4.3 and are proved this session.

### 5.1 The model, in words

A machine `M` has finitely many stacks, one of which is the **query stack** (alphabet `≃ Bool`),
finitely many labels and states, and a program `m : label → Bool → statement`. A statement is a
finite tree of `push`, `peek`, `pop`, `load`, `branch`, ending in `goto` or `halt`.

A configuration `c` is (label or *halted*, state, contents of all stacks). Its **query string**
`q(c)` is the query stack read top first as bits. One step with oracle `O` from a live
configuration with label `l`: let `b = [q(c) ∈ O]` and execute the whole statement `m l b`.
A halted configuration has no successor.

* `init(u)`: label `main`, initial state, input stack `u`, other stacks empty.
* `halt(o)`: halted, initial state, output stack `o`, other stacks empty.
* "`M^O` outputs `o` on `u` within `t` steps": some `s ≤ t` has `step_O^s(init u) = halt(o)`.
* `D(M)` (`depth M`): the largest number of pushes **onto the query stack** on one root-to-leaf
  path of one statement `m l b`. One step executes one such path, so:

**One step can lengthen the query string by `D(M)`, not by 1.** A machine whose statements push
five symbols has `D = 5` and after `t` steps can hold a query of length `5t`. Every bound below
carries `D`.

A query is *asked* at a configuration when a step is taken from it. In a run of `t` steps from
`c₀` the queries asked are `q(c₀), …, q(c_{t−1})`; `q(c_t)` is not asked.

### 5.2 Three lemmas about one machine

**Lemma 1 (growth).** If `c →_O c'` then `|q(c')| ≤ |q(c)| + D(M)`.

*Proof.* The step executes one statement `s = m l b`. By induction on `s`, executing `s` from
stacks `S` leaves the query stack with length at most `|S(kq)| + pushDepth_kq(s)`: a `push` onto
the query stack adds one and is counted once; a `push` elsewhere, `peek`, `load` change nothing;
`pop` does not lengthen; `branch` executes one side and `pushDepth` takes the maximum of the two.
Finally `pushDepth_kq(m l b) ≤ D(M)` by definition of `D`. ∎

**Lemma 2 (queries of a run).** If `step_O^j(init u) = c` then `|q(c)| ≤ |u| + j·D(M)`.

*Proof.* `q(init u)` is `u` if the query stack is the input stack and empty otherwise, so its
length is at most `|u|`. Then Lemma 1, `j` times. ∎

**Lemma 3 (locality).** Let `t ≥ 0`. If `O` and `O'` agree on every string of length at most
`|u| + t·D(M)`, then `step_O^s(init u) = step_{O'}^s(init u)` for all `s ≤ t` (as partial
configurations: both undefined or both equal). In particular `M^O` outputs `o` on `u` within `t`
steps iff `M^{O'}` does.

Sharper: it is enough that `O` and `O'` agree on the queries asked, i.e. on `q(c_j)` for `j < s`,
and those have length at most `|u| + (s−1)·D(M)`. For `s = 0` nothing is needed.

*Proof.* Induction on `s`. `s = 0`: both sides are `init u`. Step: the two runs agree after `s`
steps by induction. If that common value is undefined or halted, both stay undefined. Otherwise
it is a configuration `c` with `|q(c)| ≤ |u| + s·D(M) ≤ |u| + t·D(M)` (Lemma 2), so
`[q(c) ∈ O] = [q(c) ∈ O']`, both runs execute the same statement from the same configuration and
agree after `s + 1` steps. ∎

**Lemma 4 (unique output).** If `M^O` outputs `o` on `u` within `t` steps and outputs `o'` on `u`
within `t'` steps, then `o = o'`.

*Proof.* Say `step^s(init u) = halt(o)` and `step^{s'}(init u) = halt(o')` with `s ≤ s'`.
A halted configuration has no successor, so `step^{s''}(init u)` is undefined for `s'' > s`;
hence `s' = s` and `halt(o) = halt(o')`. The output stack of `halt(o)` is `o`. ∎

(Lemma 4 is F4 of the plan. It is not formalised this session.)

### 5.3 Codes (assumed here; N1–N4 of the plan)

The proof uses one fact about machines that is not proved until the normal-form sessions:

> **(N)** There is a sequence `e : ℕ → VCode` of *verifier codes*. A code `i` consists of an
> oracle machine `M_i` whose input alphabet is identified with `{0, 1} ⊔ {#} ⊔ [g_i]` and whose
> output alphabet is identified with `Bool`, together with two numbers `g_i` (certificate
> alphabet size) and `k_i` (exponent). Write `D_i = D(M_i)`.
> For every oracle verifier `V` with certificate alphabet `Γ₁` and every exponent `k` there are
> a code `i` with `k_i = k` and a bijection `ρ : Γ₁ → [g_i]` such that **for every oracle `O`**,
> all `w ∈ {0,1}*`, `y ∈ Γ₁*`, `b`, `t`:
> `V^O` outputs `[b]` on `w#y` within `t` steps iff `M_i^O` outputs `[b]` on `w#ρ(y)` within `t`
> steps.

Two properties of (N) matter and are easy to lose:

1. Codes are oracle-independent objects. `e` is fixed before `A` is defined, and the code of a
   verifier does not depend on which oracle it is later run with.
2. `D_i` is the depth of the coded machine `M_i` itself, not of `V`. The definition of `A` and
   all bounds below mention only `M_i`.

### 5.4 Definition of `A`

**Frames.** `frame(i, T, v) = 1^i 0 1^T 0 v` for `i, T ∈ ℕ`, `v ∈ {0,1}*`. Every binary string
has at most one such decomposition (`i` = number of leading ones, then a zero, `T` = number of
following ones, then a zero, `v` = the rest), and `|frame(i, T, v)| = i + T + |v| + 2`.

For a frame `x = frame(i, T, v)` put

* `w = v` reversed, `n = |v| = |w|` (the reversal only makes the padding machine a single loop);
* `μ = n + 1 + n^{k_i}`: the longest verifier input `w#y` with `|y| ≤ n^{k_i}`;
* **step budget** `β = ⌊(T ∸ μ) / (D_i + 1)⌋`, with truncated subtraction.

**Membership condition.** For an oracle `O` and a string `x`:

> `Φ(O, x)` iff `x` is a frame `frame(i, T, v)` and there is `y ∈ [g_i]*` with `|y| ≤ n^{k_i}`
> such that `M_i^O` outputs `[true]` on `w#y` within `β` steps.

**Levels.** `A_0 = ∅`, `A_{m+1} = A_m ∪ { x : |x| = m and Φ(A_m, x) }`, and `A = ⋃_m A_m`.

This is a definition by recursion on `m` with no side conditions, so `A` exists. Two immediate
facts, by induction on `m`: every element of `A_m` has length `< m`; and
`A ∩ {z : |z| < m} = A_m`. Hence, for every `x`,

> (★)  `x ∈ A`  iff  `Φ(A_{|x|}, x)`  iff  `Φ(A ∩ {z : |z| < |x|}, x)`.

### 5.5 Every query within the budget is strictly shorter than the coded tuple

**Proposition 5.** Let `x = frame(i, T, v)`, let `y ∈ [g_i]*` with `|y| ≤ n^{k_i}`, let `O` be any
oracle, and let `c_0, c_1, …` be the run of `M_i^O` on `u = w#y`. Then for every `j < β`,

> `|q(c_j)| ≤ μ + j·D_i < T < |x|`.

So every query asked during the first `β` steps, on every admissible certificate and under every
oracle, is strictly shorter than `x`; the margin is at least `i + n + 3`.

*Proof.* If `β = 0` there is no `j < β`. Otherwise `β ≥ 1`, so `T ∸ μ ≥ (D_i + 1)·β ≥ 1`, hence
`T ≥ μ + (D_i + 1)·β`. By Lemma 2, `|q(c_j)| ≤ |u| + j·D_i`, and `|u| = n + 1 + |y| ≤ μ`. With
`j ≤ β − 1`:

`μ + j·D_i ≤ μ + (β − 1)·D_i < μ + (D_i + 1)·β ≤ T < i + T + n + 2 = |x|`. ∎

Where each source of query length is accounted for:

| Source | Bound | Where |
|---|---|---|
| Query stack is the input stack, so the first query is the input `w#y` itself | `n + 1 + |y| ≤ μ` | the `μ` subtracted from `T` |
| Certificate symbols copied or translated onto the query stack | each push is part of some step; at most `D_i` pushes per step | the divisor `D_i + 1` |
| Anything else pushed (constants, state-dependent symbols, parts of `w`) | same | same |
| Several pushes in one step | `D_i` per step, not 1 | the divisor `D_i + 1` |

(For a verifier the query stack cannot actually be the input stack, because the input alphabet
has at least three symbols and the query alphabet two. The bound does not use this.)

**What fails without the divisor.** With budget `β = T` (PLAN §4.1 as first written) a machine
with `D_i ≥ 2` can ask queries of length up to `μ + (T − 1)·D_i`, which exceeds
`|x| = i + T + n + 2` for large `T`. The claim "membership of `x` refers only to shorter strings"
is then false as a statement about the machine; it holds only because the definition cuts the
oracle off at length `|x|`. The classical argument (query tape, one symbol written per step, so
fewer than `n` steps give queries shorter than `n`) is the case `D = 1` and does not transfer
to TM2. See §5.8.

### 5.6 `A` is well defined: existence and uniqueness of the self-referential set

**Theorem 6.** `A` satisfies, for every `x`,

> (†)  `x ∈ A`  iff  `Φ(A, x)`,

and `A` is the only set of binary strings satisfying (†).

*Proof.* *Truncation is invisible.* Let `O` be any oracle and `x` any string, and put
`O_x = O ∩ {z : |z| < |x|}`. Claim: `Φ(O, x)` iff `Φ(O_x, x)`. If `x` is not a frame both are
false. Otherwise fix `y` with `|y| ≤ n^{k_i}`. By Proposition 5, under `O` every query asked in
the first `β` steps on `w#y` is shorter than `x`, where `O` and `O_x` agree. By the sharp form of
Lemma 3 the two runs agree for `β` steps, so `M_i^O` outputs `[true]` on `w#y` within `β` steps
iff `M_i^{O_x}` does. The claim follows by quantifying over `y`.

*Existence.* By (★), `x ∈ A` iff `Φ(A ∩ {|z| < |x|}, x)`, and by the claim with `O = A` this is
`Φ(A, x)`.

*Uniqueness.* Let `B` satisfy (†). Show `B ∩ {|z| < m} = A_m` by induction on `m`. `m = 0`: both
empty. Step: for `|x| = m`, `x ∈ B` iff `Φ(B, x)` iff `Φ(B ∩ {|z| < m}, x)` (claim) iff
`Φ(A_m, x)` (induction hypothesis) iff `x ∈ A_{m+1}`; strings shorter than `m` are covered by the
induction hypothesis and `A_{m+1} ∩ {|z| < m} = A_m`. Taking the union over `m`, `B = A`. ∎

So `A` is exactly "the set of `(i, T, v)` such that verifier `i`, **with oracle `A` itself**,
accepts `v` reversed with some short certificate within the budget", and that description
determines `A`.

### 5.7 `NP^A ⊆ P^A`

**Theorem 7.** For every `L ⊆ {0,1}*`: if `L ∈ NP^A` then `L ∈ P^A`. With T4 (`P^A ⊆ NP^A`,
proved this session for every oracle) this gives `PEqNP A`.

*Proof.* Unfold `L ∈ NP^A`: there are a finite `Γ₁`, a relation `R`, an exponent `k`, a function
`f : {0,1}* × Γ₁* → Bool`, an oracle machine `V` and a polynomial `p` with natural coefficients
such that

* (a) `L w` iff there is `y ∈ Γ₁*` with `|y| ≤ |w|^k` and `R w y`;
* (b) `R w y` iff `f(w, y) = true`;
* (c) for **all** `w, y` (no length restriction): `V^A` outputs `[f(w, y)]` on `w#y` within
  `p(|w| + 1 + |y|)` steps.

Take the code `i` and bijection `ρ` of (N) for `V`, `Γ₁`, `k`; so `k_i = k`. Write `D = D_i`,
`μ(n) = n + 1 + n^k`, and choose any `T : ℕ → ℕ` with

> `T(n) ≥ μ(n) + (D + 1)·p(μ(n))`  for all `n`.

(The plan takes `T(n) = (n + c')^d`; such `c', d` exist because the right side is a polynomial in
`n`.) Define `pad(w) = frame(i, T(|w|), w reversed)`.

*Claim: `L w` iff `pad(w) ∈ A`.* Fix `w`, `n = |w|`, `x = pad(w)`. Its budget is
`β = ⌊(T(n) − μ(n)) / (D + 1)⌋ ≥ p(μ(n))`.

For every `y' ∈ [g_i]*` with `|y'| ≤ n^k`, write `y' = ρ(y)`. By (c), `V^A` outputs `[f(w, y)]`
on `w#y` within `p(n + 1 + |y|)` steps; `p` is monotone and `n + 1 + |y| ≤ μ(n)`, so within
`p(μ(n)) ≤ β` steps. By (N) with `O = A`, `M_i^A` outputs `[f(w, y)]` on `w#y'` within `β` steps.
By Lemma 4, `M_i^A` outputs `[true]` on `w#y'` within `β` steps iff `f(w, y) = true`. Therefore

`pad(w) ∈ A`
iff `Φ(A, x)`                                                        (†)
iff there is `y'` with `|y'| ≤ n^k` and `M_i^A` outputs `[true]` on `w#y'` within `β` steps
iff there is `y ∈ Γ₁*` with `|y| ≤ n^k` and `f(w, y) = true`          (`ρ` preserves length)
iff `L w`                                                             (a), (b).

*Conclusion.* `pad` is computed by a plain polynomial-time machine (A4 of the plan: copy and
count the input, a fixed power in unary, constants). `A ∈ P^A` (T3). By `oracleComp` (F7) the
function `w ↦ [pad(w) ∈ A]` is polynomial-time with oracle `A`, and it decides `L`. ∎

Where the hypotheses are used:

* (c) for all `y`, not only short ones: only short `y` occur, because `Φ` quantifies over
  `|y'| ≤ n^{k_i}` and `k_i = k`. This is why a code carries its exponent.
* `p` evaluated at `μ(n)`: monotonicity of `Polynomial ℕ` evaluation (`eval_mono` in PvsNP).
* The oracle in the run is `A` itself on both sides, so no locality argument is needed here.
  Locality was used once, in Theorem 6.
* Lemma 4 turns "outputs `[f(w,y)]` within the budget" into "outputs `[true]` within the budget
  iff `f(w,y) = true`". Without it a machine that had not halted yet could not be excluded.

### 5.8 Difference from PLAN §4.1, for decision

PLAN §4.1 defines membership with budget `T` and oracle `A ∩ {|z| < |x|}`, and chooses
`T(n) ≥ n + 1 + n^k + (c + 1)·q(n + 1 + n^k)`. That version is also correct, by a different
argument: on `pad(w)` the *real* run halts within `p(μ)` steps, its queries have length at most
`μ + D·p(μ) < |x|`, so the truncated run coincides with it for those steps, and Lemma 4 applies
to the truncated run. But in that version:

* queries asked between step `p(μ)` and step `T` may be longer than `x` when `D ≥ 2`;
* `A` satisfies only (★), with the cut-off oracle on the right, not (†);
* on frames that are not of the form `pad(w)` the machine is run against an oracle that is not `A`.

The version in §5.4 changes one thing: the budget is `⌊(T ∸ μ)/(D_i + 1)⌋` instead of `T`. The
padding function, the choice of `T(n)` and the machine `pad` are the same as in the plan. The
cost is one definition (`D_i` read off the code, three lines of arithmetic); the gain is
Proposition 5 for every frame and the cleaner equation (†). **This is a change to D6 of the plan
(not yet formalised) and needs your approval; nothing in this session's Lean depends on it.**

### 5.9 Not yet formal, and what could still go wrong

* (N) is assumed. In particular the normal form must preserve "outputs `[b]` within `t` steps"
  exactly, for every oracle, with the same query strings (so that `M_i^A` really is the verifier
  run with `A`). `D_i` is whatever depth the normal form has; it need not equal `D(V)`.
* `pad` as a machine (A4) and the power bound `(n + c')^d` are not built.
* Lemma 4 (F4) is not formalised.
* The certificate bound `|y| ≤ |w|^k` is the Clay one, including `0^0 = 1`. `A` and `L` use the
  same expression with the same `k`, so nothing depends on its behaviour at small `n`.

---

## 6. Literature for the construction

**Provenance of this section.** The search was done by a web-search subagent, which reports that
it read the PDF text of the two sources marked (read) directly. I then tried to re-read both PDFs
myself: the fetch tool returned undecoded binary and no PDF reader is installed on this machine,
so **I have not seen the quoted text with my own tools.** Quotes below are as relayed by the
subagent; page numbers are its. Treat the citation as found and the exact wording as unconfirmed
until someone opens the paper.

**Result: a published source exists, and it is the original paper.**

* **T. Baker, J. Gill, R. Solovay, "Relativizations of the P =? NP question", SIAM J. Comput.
  4(4), 1975, 431–442.** (read, per subagent, at
  `cse.ucdenver.edu/~cscialtman/complexity/Relativizations of the P=NP Question (Original).pdf`.)
  * Lemma 1 (p. 433): "For any oracle X, define the language K(X) to be {⟨i, x, 0^n⟩ : some
    computation of NP_i^X accepts x in fewer than n steps}. Then K(X) is Karp-complete in NP^X."
  * Proof of Theorem 1 (p. 434): "We construct an oracle A such that A = K(A). Let
    A = {⟨i, x, 0^n⟩ : NP_i^A accepts x in < n steps}. This is a valid inductive definition of a
    set. In a computation of length < n, no string of length ≥ n can be queried. To simulate
    NP_i^A on input x for < n steps, we need know only which elements of length
    < n ≤ |⟨i, x, 0^n⟩| belong to A. Therefore A is well-defined, and by definition A = K(A).
    Since K(A) = A ∈ P^A, we conclude P^A = NP^A by Lemma 1."
  * The PSPACE-complete oracle is a separate result (Theorem 2, p. 434).
  * Model (p. 432): a multitape Turing machine with a distinguished query tape. The bound "in a
    computation of length < n, no string of length ≥ n can be queried" is asserted, not derived;
    it rests on one tape cell written per step. The authors note (pp. 436–437) that with other
    oracle-access conventions their proofs of Theorems 1–3 are no longer valid.
* **D. van Melkebeek, CS 810 lecture notes (UW-Madison, 2007), Lecture 4, scribe B. Aydinlioglu.**
  (read, per subagent.) Same construction, built in phases by length, with the assumption stated:
  "if the simulated machine has n steps to execute, the longest query it can make to the oracle
  is of length n − 1, since it needs 1 step to actually perform the query." Also: "The usual
  proof of this fact uses a PSPACE-complete language as the oracle A. We give an alternate
  proof…"
* Sources that use a different oracle (per subagent): the Arora-Barak draft and several course
  notes use an EXP-complete set (`EXPCOM`); Katz, Immerman, Trevisan use a PSPACE-complete set
  or TQBF.
* Not opened by anyone this session: Hopcroft-Ullman 1979, Balcázar-Díaz-Gabarró, Du-Ko,
  Papadimitriou, Sipser, Goldreich, Homer-Selman, Kozen. No claim is made about them.

**Consequences for this project.**

1. The oracle of §5 is the Baker-Gill-Solovay Theorem 1 oracle (`A = K(A)`), not a new one.
   PLAN §4.1 ("I have not traced a citation") and PLAN §7 ("the cheap oracle is not the textbook
   one") are out of date: it is not the usual textbook oracle, but it is the original paper's
   first one.
2. The published well-definedness argument is exactly the step that does not transfer: "fewer
   than `n` steps, so no query of length ≥ `n`" is the case `D = 1`. In TM2 the right statement
   is Lemma 2 of §5.2 (`|u| + j·D`), and the definition must spend budget accordingly (§5.4).
   No source was found that treats a machine model with several pushes per step.
3. Differences from the published construction, all forced by the model or by Lean:
   verifier-with-certificate machines instead of nondeterministic machines (the Millennium
   definition of NP); the certificate bound `|y| ≤ n^{k_i}` inside the definition; the budget
   `⌊(T ∸ μ)/(D_i + 1)⌋`; an abstract surjection from `ℕ` onto codes instead of a Gödel numbering.

---

## 7. Lemma table and checks (session 1, 2026-10-07)

### 7.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Oracle.lean` | 367 (311) | D1, D2; generic iteration lemmas; `pushDepth`, `depth`; T0; L1–L6 |
| `Relativization/Classes.lean` | 40 (31) | D3 |
| `Relativization/Plain.lean` | 230 (195) | `toOracle`; S1–S3; T1, T2, T2'; E1–E3 |
| `Relativization/Self.lean` | 128 (106) | `selfTM`; T3 |
| `Relativization/Comp.lean` | 547 (472) | F7 `oracleComp`; T4 |
| `Relativization.lean` | 19 (15) | imports |
| **Total** | **1,331 (1,130)** | 339 constants: 169 named, 170 compiler-generated |

### 7.2 Results asked for in the session brief

All **proved**. Axioms are from the literal `#print axioms` output in §7.5.

| Id | Lean name | File:line | Statement | Hypotheses beyond the plan | Axioms |
|---|---|---|---|---|---|
| T0 | `OracleFinTM2.step_empty` | Oracle:275 | `tm.step ∅ c = (tm.toFinTM2 false).step c` | none | the three |
| T1 | `inP_empty_iff` | Plain:196 | `InP ∅ ea L ↔ Millennium.InPolynomialTime ea L`, every encoding | none | the three |
| T2 | `inNP_empty_iff` | Plain:201 | `InNP ∅ ea L ↔ Millennium.InNondeterministicPolynomialTime ea L` | none | the three |
| T2' | `classEquality_empty_iff` | Plain:207 | `ClassEquality ∅ ↔ Millennium.ClayPVersusNP` | none | the three |
| E1 | `inP_empty_bool_iff` | Plain:212 | T1 at `fin_encoding_string Bool` | none | the three |
| E2 | `inNP_empty_bool_iff` | Plain:217 | T2 at `fin_encoding_string Bool` | none | the three |
| E3 | `pEqNP_empty_iff` | Plain:223 | `PEqNP ∅ ↔ ∀ L, P ↔ NP` over `Bool` | none | the three |
| S1 | `OTM2ComputableInPolyTime.ofPlain` | Plain:163 | plain poly-time machine ⇒ oracle poly-time machine, any `A`, same alphabets and time | none | the three |
| S2 | `OTM2ComputableInPolyTime.toPlain` | Plain:173 | oracle poly-time machine with `∅` ⇒ plain one, same alphabets and time | none | the three |
| S3 | `inP_of_inPolynomialTime` | Plain:191 | `P ⊆ P^A` for every `A`, every encoding | none | the three |
| T3 | `oracle_inP` | Self:111 | `InP A (fin_encoding_string Bool) (· ∈ A)` for every `A` | none | the three |
| F7 | `oracleComp` | Comp:523 | plain poly-time `f`, then oracle poly-time `g` ⇒ oracle poly-time `g ∘ f` | none | the three |
| T4 | `inP_subset_inNP` | Comp:535 | `InP A … L → InNP A … L` for every `A` and every finite alphabet with `[Nontrivial alphabet]` | `[Nontrivial alphabet]`, as in the plan's T4; inherited from `Millennium.LeftProjection`; holds for `Bool` | the three |
| L1 | `OracleFinTM2.step_congr` | Oracle:283 | a step depends on the oracle only through the current query | none | the three |
| L2 | `OracleFinTM2.query_length_step` | Oracle:292 | one step lengthens the query by at most `tm.depth` | none | the three |
| L3 | `OracleFinTM2.query_length_iter` | Oracle:298 | `n` steps lengthen it by at most `n * tm.depth` | none | the three |
| L4 | `OracleFinTM2.iter_congr` | Oracle:305 | oracles agreeing on the queries asked in the first `n` steps give the same `n`-step run | none | the three |
| L5 | `OracleFinTM2.locality` | Oracle:338 | oracles agreeing on strings of length `≤ l.length + t * tm.depth` give the same run for every `n ≤ t` | none | the three |
| L6 | `OracleFinTM2.outputsInTime_congr` | Oracle:358 | same, for `Nonempty (OTM2OutputsInTime …)` | none | the three |

"The three" = `[propext, Classical.choice, Quot.sound]`.

No faithfulness lemma turned out false and none needed a hypothesis that was not already in its
statement in §3 or §4. No definition of §2 was changed to make a lemma provable; the Lean
definitions are the ones of PLAN §3.2 field for field.

### 7.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Oracle | `Oracle`, `OracleFinTM2`, `decidableEqK`, `toFinTM2`, `Cfg`, `query`, `step`, `initList`, `haltList`, `OTM2OutputsInTime`, `OTM2ComputableInPolyTime`; `iter_none`, `iter_step`, `iter_map`, `iter_sim`, `iter_le`; `pushDepth`, `length_stepAux`, `length_step_le`; `depth`, `pushDepth_le_depth`, `query_length`, `iter_congr_of_length`, `query_initList_length_le`, `OutputsInTime.congr` |
| Classes | `InP`, `InNP`, `PEqNP`, `ClassEquality` |
| Plain | `Plain.PΓ`, `liftS`, `toOracle`, `mkStk`, `update_mkStk`, `stepAux_liftS`, `emb`, `step_emb`, `initList_toOracle`, `haltList_toOracle`, `outputs` |
| Self | `Self.QΛ`, `prog`, `selfTM`, `cfg`, `initList_eq`, `haltList_eq`, `step_start`, `step_drain_cons`, `step_drain_nil`, `step_emit`, `drain`, `selfTM_run`, `selfTM_outputs` |
| Comp | `Comp.CK`, `X`, `CΓ`, `CΛ`, `Cσ`, `pop1`, `push1`, `pop2`, `push2`, `tmp`, `lift₁`, `lift₂`, `prog`, `compTM`, `mkStk`, `update_mkStk_inl/inr/tmp`, `lab₁`, `stepAux_lift₁`, `stepAux_lift₂`, `CCfg`, `cstep`, `emb₁`, `emb₂`, `query_emb₂`, `step_emb₁`, `step_emb₂`, `step_pop1_cons`, `step_pop1_nil`, `step_push1`, `step_pop2_cons`, `step_pop2_nil`, `step_push2`, `copy₁`, `copy₂`, `outDepth`, `length_iter`, `eval_mono`, `initList_stk_length_le`, `haltList_stk_self`, `update_haltList_stk`, `update_nil_eq_initList`, `initList_compTM`, `haltList_compTM`, `glue`, `midPoly`, `compTime`, `compOutputs` |

### 7.4 Things a reviewer should know

1. **`P ⊆ P^∅` is not a definitional unfolding.** PLAN §3.4 said both directions of T1 were
   immediate. `P^∅ ⊆ P` is (fix the bit `false`). The other direction needs a query stack that a
   plain `FinTM2` does not have, so `Plain.toOracle` adds a stack `none : Option M.K` and
   `stepAux_liftS` proves the one-step simulation. The definitions were not changed; the cost was
   134 lines instead of about 20. The same construction gives `P ⊆ P^A` for every `A`.
2. **`depth` counts pushes onto the query stack only**, maximised over paths (not summed over
   branches, as PvsNP's `pushes` did). It is the tightest bound for which L2 holds. The plain
   analogue for the output stack is `Comp.outDepth`.
3. **L5 is stated for `n ≤ t` with the bound `t * depth`.** The sharp form is L4: only queries
   actually asked matter. The collapse proof (§5.6) needs L4, because for budget 0 the length
   form has a non-vacuous hypothesis.
4. **`A ∈ P^A` uses `kq = k₀ = k₁`**: one binary stack is input, query and output stack. The
   machine runs `w.length + 3` steps. The oracle's bit is read in the first step and carried in
   the label.
5. **T4's `[Nontrivial alphabet]`** comes from
   `Millennium.LeftProjection.polynomial_time_computable`, which is only stated for such
   alphabets. Nothing in the oracle part needs it.
6. **`oracleComp` runs the oracle machine second.** The composite query stack is `M₂`'s; while
   `M₁` and the copy loops run, the query stack is empty and the program ignores the answer.
   Oracle-then-plain and oracle-then-oracle are not provided (the structure has one query stack).
7. **Proof-engineering note.** `OracleFinTM2.Cfg` and `Comp.compTM` are ordinary `def`s, so terms
   typed through them are not type-correct at instance transparency and `rw` fails on them. The
   composite machine's lemmas are therefore stated over the raw type `Comp.CCfg` with
   `Comp.cstep`, as PvsNP's `Comp.lean` did with `TM2.step (prog …)`.
8. **Not done, by instruction or by scope:** F4 (unique output; used in the paper proof, Lemma 4),
   N1–N4, B1–B6, A1–A6, T5–T8. `NP ⊆ NP^A` is not stated (it follows from S3 in a few lines).
9. **Local attributes.** `attribute [local instance]` is used three times (for the `Fintype`
   fields of `FinTM2`/`OracleFinTM2`) and `@[reducible]` twice (`Plain.PΓ`, `Comp.CΓ`), as in
   PvsNP. One global instance is declared: `OracleFinTM2.decidableEqK`, mirroring
   `FinTM2.decidableEqK`. No macros, syntax, elaborators, `deriving`, `set_option`, or `#eval`.

### 7.5 Check outputs

Full logs are in `logs/` (not committed): `session1-axioms-all.txt`, `session1-print-axioms.txt`,
`session1-build.txt`.

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`; the audit script is outside the repository). Last lines of
`logs/session1-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 339 (169 named, 170 auxiliary)
UNION of axioms used: [Classical.choice, Quot.sound, propext]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: []
```

**(b) Literal `#print axioms` on each of the 169 named declarations**
(`logs/session1-print-axioms.txt`, 169 output lines, 0 errors). Distribution:

```
      1 depends on axioms: [Quot.sound]
     86 depends on axioms: [propext, Classical.choice, Quot.sound]
     74 depends on axioms: [propext, Quot.sound]
      1 depends on axioms: [propext]
      7 does not depend on any axioms
```

`grep -c sorryAx` on both logs prints `0` and `0`. The results of §7.2:

```
'Relativization.OracleFinTM2.step_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inP_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inNP_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.classEquality_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inP_empty_bool_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inNP_empty_bool_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.pEqNP_empty_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2ComputableInPolyTime.ofPlain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2ComputableInPolyTime.toPlain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inP_of_inPolynomialTime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.oracle_inP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.oracleComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inP_subset_inNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.step_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.query_length_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.query_length_iter' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.iter_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.locality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.outputsInTime_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.depth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.InP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.InNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.PEqNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.ClassEquality' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`. First scan:
`grep -n -w -E "sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|partial"`.

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
Relativization/Comp.lean:27:attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
Relativization/Comp.lean:39:@[reducible] def CΓ : CK M₁ M₂ → Type
Relativization/Oracle.lean:261:attribute [local instance] OracleFinTM2.ΛFin
Relativization/Plain.lean:23:attribute [local instance] FinTM2.kFin
Relativization/Plain.lean:28:@[reducible] def PΓ : Option M.K → Type
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

The second scan looked for lines starting with `macro`, `syntax`, `elab`, `run_cmd`, `run_meta`,
`initialize`, `declare_syntax_cat`, `notation`, `infix`, `#eval`, `#exit`, `set_option`,
`open Lean`, `import Lean`, `deriving`, `attribute`, or an `@[…]` of kind `simp`, `instance`,
`reducible`, `implemented_by`, `extern`, `csimp`. The five hits are the local attributes of
§7.4 item 9. The third looked for `opaque`, `unsafeCast`, `lcProof`, `ofReduceBool`,
`trustCompiler`, `#print`, `#check`.

**(d) `lake build`**, after deleting this project's own `.olean` files so that every module was
recompiled (`logs/session1-build.txt`; `grep -c -i -E "warning|error"` on it prints `0`):

```
✔ [1211/1217] Built Relativization.Oracle (8.2s)
✔ [1212/1217] Built Relativization.Classes (7.6s)
✔ [1213/1217] Built Relativization.Plain (10s)
✔ [1214/1217] Built Relativization.Self (10s)
✔ [1215/1217] Built Relativization.Comp (10s)
✔ [1216/1217] Built Relativization (7.8s)
Build completed successfully (1217 jobs).
exit: 0
```

`lake env leanchecker --fresh` was not run this session (it is an acceptance check for T7).
