# NOTES — Baker-Gill-Solovay in Lean 4 + Mathlib

Working notes. `PLAN.md` holds the approved plan; this file holds the statements (rule 2), the
paper proofs, the lemma table and the check outputs.

Status legend: **stated** = written here, no Lean proof; **proved** = Lean proof compiled and
axiom-checked (output quoted in §7, §8, §9 or §10). Nothing is committed.

Contents: §1 setup record · §2 definitions · §3 target statements · §4 statements for sessions 1 to 7 ·
§5 paper proof of the collapse oracle · §6 literature · §7 lemma table and checks (session 1) ·
§8 lemma table and checks (session 2) · §9 (session 3) · §10 (session 4) · §11 (session 5) · §12 (session 6) · §13 (session 7).

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

T5, T6, T7, T8 are **not** attempted this session. *(Session 7: T5, T6 and T7 are proved as
stated here, `Relativization/BakerGillSolovay.lean`; §4.13 and §13. T8 is not attempted.)*

---

## 4. Statements, written before the Lean proofs (§4.1–4.4 session 1; §4.5–4.7 session 2; §4.8–4.9 session 3; §4.10 session 4; §4.11 session 5; §4.12 session 6; §4.13 session 7)

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

### 4.5 Session 2 (2026-10-07): what the collapse proof needs, and what the plan had

The §5 proof uses (N) of §5.3 and Lemma 4 of §5.2. Compared with PLAN §6.4:

1. **N1 as the plan states it is false.** "`Countable (TM2.Stmt Γ Λ σ)` for finite `σ`,
   countable `K`, `Λ`, `Γ k`" fails when some `Γ k` is infinite: `pop k f q` carries
   `f : σ → Option (Γ k) → σ`, and `Option ℕ → Bool` is uncountable. N1 is stated below with
   `Finite (Γ k)` for every `k`; the normal form only ever needs it over `Fin` alphabets.
2. **N3 needs a finite output alphabet to give an output-alphabet equivalence.** `OracleFinTM2`
   has `Fintype (Γ k₀)` and `Γ kq ≃ Bool` but says nothing about `Γ k₁`. The normal form is built
   for *every* machine (N3a, with the output translated by a decoding map); the form with
   equivalences on both ends (N3b, the plan's statement) is stated for `[Finite (tm.Γ tm.k₁)]`,
   which every machine inside an `OTM2ComputableInPolyTime` with finite `βΓ` satisfies.
3. **Time overhead is zero**, not polynomial: the normal form runs the same number of steps and
   outputs the same list, for every oracle and every input. This is the form (N) uses ("within
   `t` steps iff within `t` steps") and the plan's form; it is stronger than the session brief's
   "within a stated polynomial overhead" (the overhead is the identity).
4. **Codes carry their parameters.** A verifier code carries `g` (certificate alphabet size) and
   `k` (exponent), as §5.3 requires; a decider code carries its time polynomial, so that the
   separation's requirements `(code, polynomial)` are one countable type.
5. Nothing stronger than (N) is needed by §5; (N) is N4v below, word for word.

### 4.6 Statements for session 2: normal form (N1–N4) and unique output (F4)

Namespace `Relativization`. `κ` below is `Fintype.equivFin tm.K`.

```lean
/-- Normal-form machines: every type is `Fin n`, every alphabet `Fin (a k)`. -/
structure NFMachine where
  nK nΛ nσ : ℕ
  a : Fin nK → ℕ
  k₀ k₁ kq : Fin nK
  main : Fin nΛ
  init : Fin nσ
  qAlpha : Fin (a kq) ≃ Bool
  m : Fin nΛ → Bool → Turing.TM2.Stmt (fun j => Fin (a j)) (Fin nΛ) (Fin nσ)

def NFMachine.toOracleFinTM2 (N : NFMachine) : OracleFinTM2    -- field for field

/-- N1 -/ instance TM2.Stmt.countable {K : Type} {Γ : K → Type} {Λ σ : Type}
    [Countable K] [∀ k, Finite (Γ k)] [Countable Λ] [Finite σ] : Countable (TM2.Stmt Γ Λ σ)

/-- N2 -/ instance : Countable NFMachine
/-- N2 -/ instance : Countable DCode
/-- N2 -/ instance : Countable VCode
/-- N2, the enumerations (noncomputable, from `exists_surjective_nat`) -/
noncomputable def dEnum : ℕ → DCode
theorem dEnum_surjective : Function.Surjective dEnum
noncomputable def vEnum : ℕ → VCode
theorem vEnum_surjective : Function.Surjective vEnum

/-- Reachable symbols of stack `k`: everything some statement can push there, all of the input
and query alphabets, and a finite seed `X k` (used with `X k = {x | k = k₁}` when `Γ k₁` is
finite, so that the output alphabet is carried over whole). -/
def NF.symSet (tm : OracleFinTM2) (X : ∀ k, Set (tm.Γ k)) (k : tm.K) : Set (tm.Γ k)
noncomputable def NF.nf (tm : OracleFinTM2) (X : ∀ k, Set (tm.Γ k)) (hX : ∀ k, (X k).Finite) :
    NFMachine
noncomputable def NF.enc … (k : tm.K) : tm.Γ k → Fin ((NF.nf tm X hX).a (κ k))
noncomputable def NF.dec … (k : tm.K) : Fin ((NF.nf tm X hX).a (κ k)) → tm.Γ k
theorem NF.enc_dec … (k) (i) : NF.enc tm X hX k (NF.dec tm X hX k i) = i
theorem NF.dec_enc … (k) {x} (hx : x ∈ NF.symSet tm X k) : NF.dec tm X hX k (NF.enc tm X hX k x) = x

/-- N3a, every machine: the normal form outputs `o` on `enc l` within `t` steps iff the machine
outputs `dec o` on `l` within `t` steps, for every oracle, input, output and `t`. -/
theorem NF.nf_outputs_iff (tm : OracleFinTM2) (X) (hX) (A : Oracle) (l : List (tm.Γ tm.k₀))
    (o : Option (List (Fin ((NF.nf tm X hX).a (κ tm.k₁))))) (t : ℕ) :
    Nonempty (OTM2OutputsInTime A tm l (o.map (List.map (NF.dec tm X hX tm.k₁))) t) ↔
      Nonempty (OTM2OutputsInTime A (NF.nf tm X hX).toOracleFinTM2
        (l.map (NF.enc tm X hX tm.k₀)) o t)

/-- N3b, the plan's form: finite output alphabet, equivalences on both ends. -/
theorem exists_nf (tm : OracleFinTM2) [Finite (tm.Γ tm.k₁)] :
    ∃ (N : NFMachine) (e₀ : Fin (N.a N.k₀) ≃ tm.Γ tm.k₀) (e₁ : Fin (N.a N.k₁) ≃ tm.Γ tm.k₁),
      ∀ (A : Oracle) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) (t : ℕ),
        Nonempty (OTM2OutputsInTime A tm l l' t) ↔
          Nonempty (OTM2OutputsInTime A N.toOracleFinTM2 (l.map e₀.symm)
            (l'.map (List.map e₁.symm)) t)

/-- N3c, alphabet form (what N4 uses): the same through given alphabet equivalences. -/
theorem exists_nf_equiv {αΓ βΓ : Type} [Finite βΓ] (tm : OracleFinTM2)
    (ι₀ : tm.Γ tm.k₀ ≃ αΓ) (ι₁ : tm.Γ tm.k₁ ≃ βΓ) :
    ∃ (N : NFMachine) (e₀ : Fin (N.a N.k₀) ≃ αΓ) (e₁ : Fin (N.a N.k₁) ≃ βΓ),
      ∀ (A : Oracle) (u : List αΓ) (o : Option (List βΓ)) (t : ℕ),
        Nonempty (OTM2OutputsInTime A tm (u.map ι₀.symm) (o.map (List.map ι₁.symm)) t) ↔
          Nonempty (OTM2OutputsInTime A N.toOracleFinTM2 (u.map e₀.symm)
            (o.map (List.map e₁.symm)) t)

/-- Decider codes: binary input and output alphabets, and a time polynomial. -/
structure DCode where
  N : NFMachine
  inE : Fin (N.a N.k₀) ≃ Bool
  outE : Fin (N.a N.k₁) ≃ Bool
  time : Polynomial ℕ

/-- Verifier codes: input alphabet `{0,1} ⊔ {#} ⊔ [g]` (the `pair_encoding` alphabet, which is
`Bool ⊕ Option (Fin g)`), output alphabet `Bool`, exponent `k`. -/
structure VCode where
  N : NFMachine
  g : ℕ
  k : ℕ
  inE : Fin (N.a N.k₀) ≃ Bool ⊕ Option (Fin g)
  outE : Fin (N.a N.k₁) ≃ Bool

/-- N4d: every polynomial-time oracle decider has a code with the same polynomial that runs
exactly like it under every oracle. -/
theorem exists_dcode {A : Oracle} {f : List Bool → Bool}
    (h : OTM2ComputableInPolyTime A (fin_encoding_string Bool).encode
      finEncodingBoolBool.encode f) :
    ∃ c : DCode, c.time = h.time ∧ ∀ (O : Oracle) (w : List Bool) (b : Bool) (t : ℕ),
      Nonempty (OTM2OutputsInTime O h.tm (w.map h.inputAlphabet.symm)
        (some [h.outputAlphabet.symm b]) t) ↔
      Nonempty (OTM2OutputsInTime O c.N.toOracleFinTM2 (w.map c.inE.symm)
        (some [c.outE.symm b]) t)

/-- N4d', the form the separation stage uses: the code decides `f` under `A` within its own
polynomial. -/
theorem exists_dcode_decides … (h : OTM2ComputableInPolyTime A … f) :
    ∃ c : DCode, c.time = h.time ∧ ∀ w : List Bool,
      Nonempty (OTM2OutputsInTime A c.N.toOracleFinTM2 (w.map c.inE.symm)
        (some [c.outE.symm (f w)]) (c.time.eval w.length))

/-- N4v, statement (N) of §5.3: for every oracle verifier with certificate alphabet `Γ₁` and
every exponent `k` there are a code `i` with `k_i = k` and a bijection `ρ : Γ₁ ≃ Fin g_i` such
that, for every oracle `O` and all `w`, `y`, `b`, `t`, `V^O` outputs `[b]` on `w#y` within `t`
steps iff `M_i^O` outputs `[b]` on `w#ρ(y)` within `t` steps. -/
theorem exists_vcode {Γ₁ : Type} [Fintype Γ₁] (V : OracleFinTM2)
    (ι₀ : V.Γ V.k₀ ≃ Bool ⊕ Option Γ₁) (ι₁ : V.Γ V.k₁ ≃ Bool) (k : ℕ) :
    ∃ (i : ℕ) (ρ : Γ₁ ≃ Fin (vEnum i).g), (vEnum i).k = k ∧
      ∀ (O : Oracle) (w : List Bool) (y : List Γ₁) (b : Bool) (t : ℕ),
        Nonempty (OTM2OutputsInTime O V
          (((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)).encode (w, y)).map
            ι₀.symm) (some [ι₁.symm b]) t) ↔
        Nonempty (OTM2OutputsInTime O (vEnum i).N.toOracleFinTM2
          (((pair_encoding (fin_encoding_string Bool)
            (fin_encoding_string (Fin (vEnum i).g))).encode (w, y.map ρ)).map (vEnum i).inE.symm)
          (some [(vEnum i).outE.symm b]) t)

/-- N4v', the same for the verifier structure inside `InNP`, with the output written as
`outputsFun` writes it (`finEncodingBoolBool.encode b = [b]`). -/
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
          (some [(vEnum i).outE.symm b]) t)

/-- F4, Lemma 4 of §5.2: halting configurations are terminal, so a machine has at most one
output on an input, whatever the time bounds. -/
theorem OracleFinTM2.step_haltList (tm : OracleFinTM2) (A : Oracle) (o : List (tm.Γ tm.k₁)) :
    tm.step A (tm.haltList o) = none
theorem OracleFinTM2.haltList_injective (tm : OracleFinTM2) : Function.Injective tm.haltList
theorem OTM2OutputsInTime.output_unique {A : Oracle} {tm : OracleFinTM2} {l : List (tm.Γ tm.k₀)}
    {o o' : List (tm.Γ tm.k₁)} {t t' : ℕ}
    (h : OTM2OutputsInTime A tm l (some o) t) (h' : OTM2OutputsInTime A tm l (some o') t') :
    o = o' ∧ h.steps = h'.steps
/-- F4', the form §5.7 uses: given one output, any other candidate within at least the same
time is the output iff it is equal to it. -/
theorem OTM2OutputsInTime.outputs_iff_eq … (h : OTM2OutputsInTime A tm l (some o) t)
    (o' : List (tm.Γ tm.k₁)) {t' : ℕ} (ht : t ≤ t') :
    Nonempty (OTM2OutputsInTime A tm l (some o') t') ↔ o' = o
theorem OTM2OutputsInTime.bool_iff {βΓ : Type} (ι : tm.Γ tm.k₁ ≃ βΓ) {b : βΓ}
    (h : OTM2OutputsInTime A tm l (some [ι.symm b]) t) (b' : βΓ) :
    Nonempty (OTM2OutputsInTime A tm l (some [ι.symm b']) t) ↔ b' = b
```

How (N) of §5.3 is read off N4v: `M_i := (vEnum i).N.toOracleFinTM2`, `g_i := (vEnum i).g`,
`k_i := (vEnum i).k`, `D_i := M_i.depth`; "`M_i^O` outputs `[b]` on `w#y'`" is
`Nonempty (OTM2OutputsInTime O M_i (((pair_encoding …).encode (w, y')).map inE.symm)
(some [outE.symm b]) t)`. Codes are oracle-independent: `vEnum` is a closed term, and the `i`
of N4v does not depend on the oracle `O` quantified after it.

### 4.7 Construction of the normal form (paper proof, before the Lean)

Fix `tm` and a finite seed `X`. `κ : tm.K ≃ Fin nK`, `λ : tm.Λ ≃ Fin nΛ`, `ς : tm.σ ≃ Fin nσ` are
`Fintype.equivFin`. For each `k`, `symSet k ⊆ tm.Γ k` is finite (finitely many statements,
each pushing finitely many `Set.range (f ·)` with `σ` finite; the input alphabet is finite; the
query alphabet is `≃ Bool`; `X k` is finite), so `ε k : symSet k ≃ Fin (Nat.card (symSet k))`.
Put `a j := Nat.card (symSet (κ.symm j))`, so `a (κ k) = Nat.card (symSet k)` propositionally;
`enc k` and `dec k` are `ε k` and its inverse composed with `Fin.cast` of that equation (with a
junk value for `enc k x` when `x ∉ symSet k`, never reached). The statement translation `tr`
replaces `push k f` by `push (κ k) (enc k ∘ f ∘ ς.symm)`, `pop`/`peek` by the same with
`o.map (dec k)` on the read symbol, states by `ς`, labels by `λ`; the program is
`m l' b := tr (tm.m (λ.symm l') b)`; `qAlpha := tm.queryAlphabet ∘ dec kq` (a bijection because
`symSet kq` is everything).

Simulation map `e : N.Cfg → tm.Cfg`, from the normal form **to** the original (so that no
reachability invariant is needed): label `λ.symm`, state `ς.symm`, stack `k` is
`(c.stk (κ k)).map (dec k)`. One step commutes: `tm.step O (e c) = (N.step O c).map e`, because
(i) the query strings agree, `tm.query (e c) = N.query c`; (ii) by induction on the statement,
`stepAux (tr q) v S` maps to `stepAux q (ς.symm v) (e S)`: at a `push k f` the pushed symbol
`f v` is in `symSet k`, so `dec (enc (f v)) = f v`; at `pop`/`peek`, `head?` commutes with
`map`; `Fin.cast` only ever appears as `Fin.cast h (Fin.cast h.symm i) = i`, and `κ.symm (κ k)`
never has to be rewritten because `e` evaluates `κ` forwards only. Then `iter_map` transports
runs. `e (N.initList (l.map enc)) = tm.initList l` (input alphabet is in `symSet`), and
`e d = tm.haltList (o.map dec) ↔ d = N.haltList o` (`e` is injective on labels, states and
stacks since `enc ∘ dec = id`). N3a follows; N3b/N3c compose with the alphabet equivalences,
using `X k := {x | k = k₁}` so that `dec k₁` is a bijection. N4 is N3c at the two alphabets,
with `ρ := Fintype.equivFin Γ₁` and `Sum.map id (Option.map ρ)` on the pair alphabet, plus the
enumeration.

---

### 4.8 Session 3 (2026-10-07): what `Prog` and `Emb` assume about the machine model

Written before the port. Source: `D:\PvsNP` at `c271016`, `Prog.lean` (958 lines, 823 non-blank)
and `Emb.lean` (179 lines, 155 non-blank), both importing Mathlib only (`Emb` imports `Prog`).
Target: `Relativization/Prog.lean`, `Relativization/Emb.lean`, namespaces `Relativization.Prog`,
`Relativization.Emb`. `D:\PvsNP` is not modified.

**Assumptions common to every definition and lemma of `Prog`.**

| | Assumption | Status with the oracle query stack |
|---|---|---|
| P1 | **Fixed program.** The machine is `M : Λ → TM2.Stmt Γ Λ σ`, the step is `TM2.step M`, and the statement run at a label depends on the label only. Every run lemma has hypotheses `M l = …` for the labels it occupies and concludes `Run M n c d := (flip bind (TM2.step M))^[n] (some c) = some d`. | **Breaks.** An oracle machine's program is `tm.m : Λ → Bool → Stmt` and its step is `TM2.step (fun l => tm.m l (decide (tm.query c ∈ A))) c`: the statement depends on the configuration through the query stack. So `Run M` is not the oracle run, and no `Prog` lemma says anything about `tm.step A` as it stands. It does *not* break at a label `l` where `tm.m l true = tm.m l false` ("oblivious" label): there the oracle step is the plain step of `fun l => tm.m l false`. Bridges O1–O3 below. |
| P2 | **Halting convention.** `Run` is only ever used between live configurations `⟨some l, v, S⟩`; one step at a live label is `stepAux (M l)`; a halted configuration `⟨none, …⟩` is absorbing (`step = none`, used through `iter_none`). | Unchanged: `OracleFinTM2.step` is `TM2.step` of some program, so a halted configuration steps to `none` for every oracle. |
| P3 | **No distinguished stacks.** `Prog` never mentions `k₀`, `k₁`, `initList`, `haltList` or `FinTM2`; stacks are an arbitrary `K` with `DecidableEq K`. | Unchanged. The query stack `kq` is one more stack to `Prog`. A primitive that pushes onto `kq` changes the query string; that is harmless for the primitive's own lemma (P1 is about the statement, not the query) but it means a bridge may not assume the query string is constant along a run. |
| P4 | **One bit of state.** `[Flag σ]`: after a pop the primitives overwrite the whole state with `Flag.tag o.isSome` and branch on `Flag.untag`. | Unchanged. The oracle's answer is fed to the program, not stored in `σ`; `Prog` primitives cannot look at it, which is exactly P1. |
| P5 | **Step-count notions.** `Run` (exact), `RunLe`, `Bud` (bounded), `Reach` (some length) are all about `TM2.step M`. | Oracle analogue `ORun` added (O1); the bounded forms are not duplicated (the separation and collapse need exact counts of plain machines plus one composition). |
| P6 | `cnt`, `addU`, `pushAll`, `pushList`, `rep`, `sumFrom` and their lemmas: lists and arithmetic. | Model-free. |
| P7 | `stepAux_pushAll`, `stepAux_pushList`: about `TM2.stepAux` only. | Hold verbatim in both models (`stepAux` is shared). |
| P8 | **Global instance and simp attributes.** `instance : Flag Bool`; `attribute [simp] Flag.untag_tag`; `@[simp] cnt_length`, `cnt_zero`, `rep_zero`. | Copied. `Flag` and the three definitions are new, so no earlier declaration can elaborate differently (checked by rebuilding, §9.4). |

**Lemma by lemma** (what each one assumes beyond P1–P3; all are copied verbatim):

| `Prog` declarations | Assumes | Oracle status |
|---|---|---|
| `Run`, `Run.zero/head/trans/of_eq/single` | P1, P2 | sequencing lemmas; oracle twins for `zero`, `head`, `trans`, `single` are O1 |
| `cnt`, `cnt_*` | P6 | — |
| `incr`, `decr`, `incr_run`, `incr_run_cnt`, `decr_run_pos/cnt/zero` | P1, P4 | via O2/O3 |
| `pushAll`, `addU`, `addU_*`, `stepAux_pushAll` | P6, P7 | — |
| `xfer`, `xfer_run`, `addU_single_*`, `single_nodupKeys` | P1, P4; `k ∉ ps.keys` | via O2/O3 |
| `cmpStep`, `cmpLoop_run`, `cmp_run`, `compare_succ_succ` | P1, P4; five distinct stacks | via O2/O3 |
| `sumFrom`, `sumFrom_const`, `sumFrom_le` | P6 | — |
| `forHead`, `forLoop_run` | P1, P4; `c ≠ cd`; caller invariant `P` | via O2/O3 |
| `pushList`, `stepAux_pushList`, `emit`, `emit_run` | P7, P1 | via O2/O3 |
| `pair_nodupKeys`, `addU_pair_*`, `copy_run`, `add_run`, `mul_run` | P1, P4 | via O2/O3 |
| `rep`, `rep_*`, `emitR`, `emitR_run`, `xferE`, `xferE_run`, `emitDiff_run` | P6, P1, P4 | via O2/O3 |
| `Reach`, `Reach.*`, `forLoop_reach` | P1, P5 | not duplicated |
| `RunLe`, `Bud`, `Run.le`, `RunLe.*`, `Bud.*`, `forLoop_le` | P1, P5 | not duplicated |

"Via O2/O3": the lemma holds for an oracle machine `tm` at labels where `tm.m l b` does not depend
on `b`; because `Prog`'s conclusions do not list the labels a run visits, the bridge usable for
a whole machine is O2 (every label oblivious, e.g. `Plain.toOracle M`), and the sharp bridge O3
needs the visited labels from the caller.

**`Emb`.**

| `Emb` declarations | Assumes | Oracle status |
|---|---|---|
| `SEmb` (injective stack renaming, alphabet bijections) | nothing about steps | model-free |
| `mapS` (statement translation) | `stepAux` level | model-free |
| `Embeds E φ M M'` | **host is a plain program** `M' : Λ' → Stmt` (P1 for the host); sub-machine plain | **Breaks** for an oracle host: the type is wrong. Oracle variant `OEmbeds E φ M tm := ∀ l, (∀ b, tm.m (φ l) b = mapS E φ (M l)) ∨ M l = .halt` (O4): the host ignores the oracle on the image of `φ`. The sub-machine stays plain (it is built with `Prog`). |
| `Agree`, `Frame`, `Frame.refl/trans/update`, `Agree.update` | stacks only | model-free. For an oracle host: if `kq` is outside the image of `e`, `Frame` says the embedded run leaves the query string alone; if inside, the query string changes, which is irrelevant because the host ignores the answer at those labels. |
| `stepAux_mapS` | `stepAux` only | verbatim |
| `iter_none` | generic | **dropped**: duplicate of `Relativization.iter_none` (Oracle.lean) |
| `run_embed`, `runLe_embed` | sub-machine plain; host plain (P1); halting labels of the sub-machine excluded (`M l = .halt` escape, so the host may do anything there) | `run_embed` holds verbatim for plain hosts (the `pad` host of A4 is plain). Oracle-host version `run_embed_oracle` (O4) added: same induction, with the host step `tm.step A` and the statement at `φ l` rewritten by `OEmbeds`. The halting escape is the hook by which an oracle host continues (for instance with a query) after a plain sub-machine. `runLe_embed` not duplicated. |

**What the port adds** (the adaptation; all in `Prog.lean` and `Emb.lean` under a final section
"Oracle machines"):

```lean
/-- O1 -/ def ORun (tm : OracleFinTM2) (A : Oracle) (n : ℕ) (c d : tm.Cfg) : Prop :=
  (flip bind (tm.step A))^[n] (some c) = some d
theorem ORun.zero, ORun.head, ORun.trans, ORun.of_eq      -- as for `Run`
/-- one oracle step at a live label runs the statement selected by the oracle's answer -/
theorem OracleFinTM2.step_live (tm) (A) (l : tm.Λ) (v) (S) :
    tm.step A ⟨some l, v, S⟩ =
      some (TM2.stepAux (tm.m l (decide (tm.query ⟨some l, v, S⟩ ∈ A))) v S)
/-- O2 -/ theorem OracleFinTM2.step_eq_plain {M : tm.Λ → TM2.Stmt tm.Γ tm.Λ tm.σ}
    (hl : ∀ b, tm.m l b = M l) (v) (S) : tm.step A ⟨some l, v, S⟩ = TM2.step M ⟨some l, v, S⟩
theorem ORun.of_run (h : ∀ l b, tm.m l b = M l) : Run M n c d → ORun tm A n c d
/-- O3, sharp: only the labels visited before step `n` must be oblivious -/
theorem ORun.of_run_visited (hM : ∀ l, ∀ b, tm.m l b = M l ∨ ∀ j < n, ∀ e,
      (flip bind (TM2.step M))^[j] (some c) = some e → e.l ≠ some l) :
    Run M n c d → ORun tm A n c d
/-- O5, packaging -/
def TM2OutputsInTime.ofRun {tm : FinTM2} (h : Run tm.m n (initList tm l) (haltList tm l'))
    (hn : n ≤ t) : TM2OutputsInTime tm l (some l') t
def OTM2OutputsInTime.ofORun {tm : OracleFinTM2} (h : ORun tm A n (tm.initList l) (tm.haltList l'))
    (hn : n ≤ t) : OTM2OutputsInTime A tm l (some l') t
/-- O4, in `Emb` -/
def OEmbeds (E : SEmb Γ tm.Γ) (φ : Λ → tm.Λ) (M : Λ → TM2.Stmt Γ Λ tm.σ) : Prop :=
  ∀ l, (∀ b, tm.m (φ l) b = mapS E φ (M l)) ∨ M l = .halt
theorem run_embed_oracle (hM : OEmbeds E φ M) … : Run M n ⟨l, v, S⟩ ⟨some l', v', T⟩ → Agree E S S' →
    ∃ T', ORun tm A n ⟨l.map φ, v, S'⟩ ⟨some (φ l'), v', T'⟩ ∧ Agree E T T' ∧ Frame E S' T'
```

O3 is stated with the visited-label condition on the *plain* run (which the caller has), so it
needs no invariant about the oracle run. No session 1 or 2 definition changes.

**What is not adapted, and why.** `Prog` stays a library for plain programs. Every machine the
plan builds with it is plain (`revTM` below, `pad` in A4), and every oracle machine of the
project is either hand-written (`selfTM`, 4 labels) or a composition (`oracleComp`,
`Plain.toOracle`). Generalising `Run` to a configuration-dependent program would touch every
`simp only [TM2.step, hp, …]` call in 958 lines for no present consumer; O1–O5 give the same
reach for machines that read the oracle at hand-written labels only.

### 4.9 Statements for session 3: B1 and B2, in the form the separation argument uses

The separation (PLAN §4.2, B3–B6) uses B2 exactly once: assuming `PEqNP B` for the constructed
oracle `B`, `InNP B (fin_encoding_string Bool) (sepLang B)` gives `InP B … (sepLang B)`, hence
(N4d') a decider code and its stage; the stage's inspection of the language is through the
unfolding `0^n ∈ sepLang B ↔ ∃ y, |y| ≤ n ∧ y.reverse ++ 0^n ∈ B`. So the form needed is
`InNP B … (sepLang B)` for *every* `B` (the oracle is fixed only in B6), with `sepLang` as the
plan writes it. B1 is used only inside B2. Checked against PLAN §6.4: both forms are strong
enough and true as written; `(w ++ y).reverse = y.reverse ++ w.reverse`, and the certificate
bound of `InNP` at `k = 1` is `y.length ≤ w.length ^ 1`, which is the bound in `sepLang`. No
correction of the kind N1 needed.

```lean
/-- The one-loop machine: input alphabet `Bool ⊕ Option Bool` (the `pair_encoding` alphabet),
output alphabet `Bool`, one label, state = the symbol just popped. Each step pops one input
symbol and pushes its bit on the output (the separator pushes nothing); on empty input it halts.
`|w| + 1 + |y| + 1` steps. -/
def Sep.revTM : FinTM2

/-- B1 -/ noncomputable def Sep.revComputable :
    TM2ComputableInPolyTime
      (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Bool)).encode
      (fin_encoding_string Bool).encode
      (fun p : List Bool × List Bool => (p.1 ++ p.2).reverse)
-- `time := X + 1`; `revComputable.tm = revTM`, both alphabet equivalences are `Equiv.refl`.

/-- The separating language (PLAN §4.2, verbatim). -/
def sepLang (B : Oracle) : Language (List Bool) :=
  fun w => ∃ y : List Bool, y.length ≤ w.length ∧ y.reverse ++ w.reverse ∈ B

/-- B2 -/ theorem sepLang_inNP (B : Oracle) : InNP B (fin_encoding_string Bool) (sepLang B)
-- witnesses: `Γ₁ := Bool`, `R w y := y.reverse ++ w.reverse ∈ B`, `k := 1`, decider
-- `oracleComp B revComputable (the T3 machine)`.

/-- For B6 (stated now, used later): on `0^n` the certificate is a prefix of length `≤ n`. -/
theorem sepLang_replicate_iff (B : Oracle) (n : ℕ) :
    sepLang B (List.replicate n false) ↔
      ∃ u : List Bool, u.length ≤ n ∧ u ++ List.replicate n false ∈ B
```

---

### 4.10 Statements for session 4: the stage construction, B3–B6, in the form the separation proof uses

Written before any Lean. Plan items: PLAN §6.4 B3–B6 and §4.2 "Stages". Everything below is in
namespace `Relativization`; the stage internals are in `Relativization.Stage`.

**How the final separation proof will use this (B6).** Assume `InP B (fes Bool) (sepLang B)`
for the constructed `B = sepOracle`: a function `f`, a polynomial-time oracle decider `h` for `f`
under `B`, and `∀ w, sepLang B w ↔ f w = true`. N4d' (`exists_dcode_decides`) gives a code
`c : DCode` with `c.time = h.time` and, for every `w`, the code's machine outputs `[f w]` on `w`
under `B` within `c.time.eval |w|` steps. N2 gives `i` with `dEnum i = c`. Stage `i` chose a
length `n = lenAt i`, ran that machine on `0^n` under the finite oracle `F_i = oracleAt i` for
`t = c.time.eval n` steps, and either (i) saw it output `[true]` and added nothing, or (ii) did
not and added one string `u ++ 0^n` with `|u| = n`. By B5 the run under `B` is the run under
`F_i` for `t` steps, so the output `[f 0^n]` is the stage's observation; by F4' (`bool_iff`)
`f 0^n = true` iff the stage saw `[true]`. In case (i) `f 0^n = true`, so `0^n ∈ sepLang B`,
so (`sepLang_replicate_iff`) some `u ++ 0^n ∈ B` with `|u| ≤ n`, of length in `[n, 2n]`; but
every string of `B` has length `< n` (earlier stages) or `> 2n` (later stages). In case (ii)
`u ++ 0^n ∈ B`, so `0^n ∈ sepLang B`, so `f 0^n = true`, so the machine outputs `[true]` under
`B`, hence under `F_i`: the stage did see `[true]`. Both cases are contradictions.
`¬ PEqNP sepOracle` then follows from B2 (`sepLang_inNP`). T6 (`∃ B, ¬ PEqNP B`) is the
final assembly and is **not** stated this session.

#### B3: counting (`Relativization/Count.lean`)

Plan form (§6.4 B3): "a set of fewer than `2^n` strings misses some `u ++ 0^n` with `|u| = n`;
every polynomial is eventually below `2^n`." Both parts are true as written and strong enough.
The construction uses the second in the weaker form "for every `ℓ` and `p` there is `n > ℓ`
with `p.eval n < 2^n`", derived from the eventual form.

```lean
/-- The `2^n` strings `u ++ 0^n` with `|u| = n`, as `List.ofFn f ++ 0^n` for `f : Fin n → Bool`. -/
def padded (n : ℕ) : Finset (List Bool)
theorem card_padded (n : ℕ) : (padded n).card = 2 ^ n

/-- B3a: the counting inequality. If `S.card < 2^n` then some `u ++ 0^n`, `|u| = n`, is not in `S`. -/
theorem exists_free (n : ℕ) (S : Finset (List Bool)) (h : S.card < 2 ^ n) :
    ∃ u : List Bool, u.length = n ∧ u ++ List.replicate n false ∉ S

/-- `p(n) ≤ p(1) · n^deg p` for `n ≥ 1` (`p(1)` is the sum of the coefficients). -/
theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) {n : ℕ} (hn : 1 ≤ n) :
    p.eval n ≤ p.eval 1 * n ^ p.natDegree

/-- `C · n^d < 2^n` once `n ≥ C · (d+1)^(d+1)` (elementary: with `m = n / (d+1)`,
`C n^d ≤ C (d+1)^d (m+1)^d ≤ m (m+1)^d < (m+1)^(d+1) ≤ (2^m)^(d+1) ≤ 2^n`, using `m < 2^m`). -/
theorem mul_pow_lt_two_pow (C d : ℕ) {n : ℕ} (hn : C * (d + 1) ^ (d + 1) ≤ n) :
    C * n ^ d < 2 ^ n

/-- B3b, the plan's form: every polynomial is eventually below `2^n`. -/
theorem eventually_eval_lt_two_pow (p : Polynomial ℕ) : ∃ N, ∀ n, N ≤ n → p.eval n < 2 ^ n

/-- B3b, the form the stage uses: a length above any bound with `p(n) < 2^n`. -/
theorem exists_len (ℓ : ℕ) (p : Polynomial ℕ) : ∃ n, ℓ < n ∧ p.eval n < 2 ^ n
```

#### The queries of a run, and the instance of locality each stage uses (`Relativization/Queries.lean`)

**Which locality lemma.** The stage-`i` run must be the same under the finite oracle `F_i` and
under the final `B`. `B ∖ F_i` consists of the strings added at stages `j ≥ i`. Those of stages
`j > i` have length `2 n_j > bound_j ≥ bound_{i+1} ≥ n_i + t_i · D_i`, above the query-length
bound of L3, so for them the length form **L5/L6** (`OracleFinTM2.locality`,
`outputsInTime_congr`, session 1) would do. The string `x_i = u_i ++ 0^{n_i}` added at stage `i`
itself has length `2 n_i`, which is in general **below** `n_i + t_i · D_i` (whenever
`t_i · D_i ≥ n_i`). So the length form is **not strong enough** for a stage's own string; what
makes the run stable is that `x_i` was chosen *unqueried*. The lemma that gives this is the
sharp form **L4** (`OracleFinTM2.iter_congr`, session 1, NOTES §4.3): two oracles that agree on
every query actually asked during the first `n` steps give the same `n`-step run. L4 is strong
enough as it stands; no session 1 definition changes (§7.4 item 3 anticipated this use). What is
added is a finite set of the queries asked, so that the counting argument and L4 speak about the
same object:

```lean
namespace OracleFinTM2
variable (tm : OracleFinTM2)

/-- The query asked at step `j` of the run on `l` under `A` (`[]` once the run has stopped). -/
noncomputable def queryAt (A : Oracle) (l : List (tm.Γ tm.k₀)) (j : ℕ) : List Bool :=
  (((flip bind (tm.step A))^[j] (some (tm.initList l))).map tm.query).getD []

/-- The queries asked during the first `t` steps (plus the junk value `[]`): at most `t` strings. -/
noncomputable def queries (A : Oracle) (l : List (tm.Γ tm.k₀)) (t : ℕ) : Finset (List Bool) :=
  (Finset.range t).image (tm.queryAt A l)

theorem card_queries_le (A : Oracle) (l : List (tm.Γ tm.k₀)) (t : ℕ) : (tm.queries A l t).card ≤ t

theorem query_mem_queries {A : Oracle} {l : List (tm.Γ tm.k₀)} {t j : ℕ} (hj : j < t) {d : tm.Cfg}
    (hd : (flip bind (tm.step A))^[j] (some (tm.initList l)) = some d) :
    tm.query d ∈ tm.queries A l t

/-- L3 for the query set. -/
theorem length_le_of_mem_queries {A : Oracle} {l : List (tm.Γ tm.k₀)} {t : ℕ} {z : List Bool}
    (hz : z ∈ tm.queries A l t) : z.length ≤ l.length + t * tm.depth

/-- L4', the instance of L4 each stage uses: oracles agreeing on `tm.queries A l t` give the
same run for every `n ≤ t` steps. -/
theorem iter_congr_queries {A A' : Oracle} (l : List (tm.Γ tm.k₀)) (t : ℕ)
    (h : ∀ z ∈ tm.queries A l t, (z ∈ A ↔ z ∈ A')) {n : ℕ} (hn : n ≤ t) :
    (flip bind (tm.step A))^[n] (some (tm.initList l)) =
      (flip bind (tm.step A'))^[n] (some (tm.initList l))

/-- L6', the same for outputs within `t` steps (both directions from the one hypothesis, since
L4' is an equality of runs). -/
theorem outputsInTime_congr_queries {A A' : Oracle} (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) (t : ℕ) (h : ∀ z ∈ tm.queries A l t, (z ∈ A ↔ z ∈ A')) :
    Nonempty (OTM2OutputsInTime A tm l l' t) ↔ Nonempty (OTM2OutputsInTime A' tm l l' t)
end OracleFinTM2
```

The instance used at stage `i`: `tm := (dEnum i).N.toOracleFinTM2`, `A := F_i`, `A' := B`,
`l := 0^{n_i}` as the code reads it, `t := t_i`. Its hypothesis is discharged by
`Stage.agree_on_queries` below.

#### B4: the stages (`Relativization/Stage.lean`)

Plan form (§6.4 B4): "stage sequence: definition by recursion with choice; invariants (length
bounds strictly increase, finite oracle below the bound is final, added string was unqueried)".
True as written and strong enough; the three invariants are `boundAt_lt_lenAt` with
`lenAt_lt_boundAt_succ`, `mem_oracleAt_of_length_le`, and `strAt_not_mem_Q` below.

**The stage-`i` machine** is the code `dEnum i : DCode` (N2, session 2): machine
`M_i := (dEnum i).N.toOracleFinTM2` with binary input and output alphabets `inE`, `outE`, and
time polynomial `p_i := (dEnum i).time`. `D_i := M_i.depth`. Every polynomial-time oracle
decider is some `dEnum i` with the same polynomial, by N4d' and `dEnum_surjective`.

**State.** A stage state is `(bound, F)`: a length bound and the set of strings added so far.
`st 0 = (0, ∅)`, `st (i+1) = step i (st i)`. Write `bound_i`, `F_i` for the fields of `st i`.

**The stage-`i` input length** is `n_i := lenAt i`, chosen by `Classical.choose` on B3b with
`ℓ := bound_i`, `p := p_i`: so `n_i > bound_i` and `t_i := p_i(n_i) < 2^{n_i}`. The next bound is

> `bound_{i+1} := 2 n_i + t_i · D_i`.

By L3 every query asked during the `t_i` steps of stage `i` has length `≤ n_i + t_i · D_i ≤
bound_{i+1}`, and the string stage `i` may add has length `2 n_i ≤ bound_{i+1}`. Since
`n_i > bound_i ≥ 0`, `bound_{i+1} ≥ 2 n_i > n_i > bound_i`: the bounds strictly increase, and
for `j > i`, `n_j > bound_j ≥ bound_{i+1}`, so `n_j` exceeds every query length of every earlier
stage and `|x_j| = 2 n_j > 2 n_i`.

**The counting argument.** Let `Q_i := M_i.queries F_i (0^{n_i}) t_i`, the queries asked during
the stage-`i` run under `F_i`. Then

> `|Q_i| ≤ t_i = p_i(n_i) < 2^{n_i} = |{u ++ 0^{n_i} : |u| = n_i}|`,

so by B3a some `u_i` with `|u_i| = n_i` has `x_i := u_i ++ 0^{n_i} ∉ Q_i`; `u_i` is
`Classical.choose` of that statement.

**The decision.** `acc_i :⇔ M_i^{F_i}` outputs `[true]` on `0^{n_i}` within `t_i` steps
(`Nonempty (OTM2OutputsInTime F_i M_i (0^{n_i}) (some [outE.symm true]) t_i)`). Then
`F_{i+1} := F_i ∪ {z | ¬ acc_i ∧ z = x_i}` (a set-builder, so no decidability is needed).

**The oracle.** `B := sepOracle := {z | ∃ i, z ∈ F_i}`. By induction on `i`,
`z ∈ F_i ↔ ∃ j < i, ¬ acc_j ∧ z = x_j`, hence `z ∈ B ↔ ∃ j, ¬ acc_j ∧ z = x_j`.

**Why `B` is well defined.** `st` is a primitive recursion on `ℕ`: `st (i+1)` is a function of
`i` and `st i` only, through two uses of `Classical.choose` on proved existence statements (B3b
for `n_i`, B3a for `u_i`, whose hypothesis `|Q_i| < 2^{n_i}` is proved inside the definition)
and one `Prop`-valued decision `acc_i`. There is no fixpoint equation to solve, unlike the
collapse oracle of §5.6: `B` is simply the union of the `F_i`, and the only property of `B`
the proof uses is the membership characterisation above.

```lean
/-- The input `0^n` as decider code `c` reads it. -/
def DCode.input (c : DCode) (n : ℕ) : List (Fin (c.N.a c.N.k₀)) :=
  (List.replicate n false).map c.inE.symm
theorem DCode.input_length (c : DCode) (n : ℕ) : (c.input n).length = n

namespace Stage

/-- The state carried from stage to stage. -/
structure State where
  bound : ℕ
  F : Oracle

/-- The machine of stage `i`. -/
abbrev M (i : ℕ) : OracleFinTM2 := (dEnum i).N.toOracleFinTM2

noncomputable def len (i : ℕ) (s : State) : ℕ         -- Classical.choose (exists_len s.bound (dEnum i).time)
theorem bound_lt_len (i : ℕ) (s : State) : s.bound < len i s
theorem eval_len_lt (i : ℕ) (s : State) : (dEnum i).time.eval (len i s) < 2 ^ len i s
noncomputable def tim (i : ℕ) (s : State) : ℕ := (dEnum i).time.eval (len i s)
noncomputable def Q (i : ℕ) (s : State) : Finset (List Bool) :=
  (M i).queries s.F ((dEnum i).input (len i s)) (tim i s)
theorem card_Q_lt (i : ℕ) (s : State) : (Q i s).card < 2 ^ len i s
noncomputable def free (i : ℕ) (s : State) : List Bool   -- Classical.choose (exists_free (len i s) (Q i s) (card_Q_lt i s))
theorem free_length (i : ℕ) (s : State) : (free i s).length = len i s
noncomputable def str (i : ℕ) (s : State) : List Bool := free i s ++ List.replicate (len i s) false
theorem str_not_mem_Q (i : ℕ) (s : State) : str i s ∉ Q i s
theorem str_length (i : ℕ) (s : State) : (str i s).length = 2 * len i s
def acc (i : ℕ) (s : State) : Prop :=
  Nonempty (OTM2OutputsInTime s.F (M i) ((dEnum i).input (len i s))
    (some [(dEnum i).outE.symm true]) (tim i s))

noncomputable def step (i : ℕ) (s : State) : State where
  bound := 2 * len i s + tim i s * (M i).depth
  F := s.F ∪ {z | ¬ acc i s ∧ z = str i s}

noncomputable def st : ℕ → State
  | 0 => ⟨0, ∅⟩
  | i + 1 => step i (st i)

/-- Shorthands for the data of stage `i`. -/
noncomputable def boundAt (i : ℕ) : ℕ := (st i).bound
noncomputable def oracleAt (i : ℕ) : Oracle := (st i).F
noncomputable def lenAt (i : ℕ) : ℕ := len i (st i)
noncomputable def timeAt (i : ℕ) : ℕ := tim i (st i)
noncomputable def strAt (i : ℕ) : List Bool := str i (st i)
def accAt (i : ℕ) : Prop := acc i (st i)
noncomputable def inputAt (i : ℕ) : List (Fin ((dEnum i).N.a (dEnum i).N.k₀)) :=
  (dEnum i).input (lenAt i)
end Stage

/-- The oracle `B` of the separation: everything some stage added. -/
def sepOracle : Oracle := {z | ∃ i, z ∈ Stage.oracleAt i}

namespace Stage
theorem st_succ (i : ℕ) : st (i + 1) = step i (st i)
theorem boundAt_succ (i : ℕ) : boundAt (i + 1) = 2 * lenAt i + timeAt i * (M i).depth
theorem mem_oracleAt_succ (i : ℕ) (z : List Bool) :
    z ∈ oracleAt (i + 1) ↔ z ∈ oracleAt i ∨ (¬ accAt i ∧ z = strAt i)
theorem boundAt_lt_lenAt (i : ℕ) : boundAt i < lenAt i
theorem timeAt_lt (i : ℕ) : timeAt i < 2 ^ lenAt i
theorem lenAt_lt_boundAt_succ (i : ℕ) : lenAt i < boundAt (i + 1)
theorem boundAt_mono : Monotone boundAt
theorem strAt_length (i : ℕ) : (strAt i).length = 2 * lenAt i
theorem strAt_not_mem_Q (i : ℕ) : strAt i ∉ Q i (st i)
theorem mem_oracleAt (i : ℕ) (z : List Bool) : z ∈ oracleAt i ↔ ∃ j < i, ¬ accAt j ∧ z = strAt j
theorem oracleAt_subset_sepOracle (i : ℕ) : oracleAt i ⊆ sepOracle
theorem mem_sepOracle (z : List Bool) : z ∈ sepOracle ↔ ∃ j, ¬ accAt j ∧ z = strAt j
/-- The finite oracle of stage `i` is final below its bound. -/
theorem mem_oracleAt_of_length_le {i : ℕ} {z : List Bool} (hz : z ∈ sepOracle)
    (hl : z.length ≤ boundAt i) : z ∈ oracleAt i
end Stage
```

#### B5: run stability

Plan form (§6.4 B5): "the stage-`i` run on `0^n` is the run under the final oracle for `p(n)`
steps." True as written; proved through L4' (not L5/L6, see above).

```lean
namespace Stage
/-- `F_i` and `B` agree on every query asked during the stage-`i` run under `F_i`: a string of
`B` is some `x_j`; `j < i` puts it in `F_i`; `j = i` contradicts the choice of `u_i`; `j > i`
contradicts L3 (`|x_j| = 2 n_j > bound_{i+1} ≥ n_i + t_i D_i`). -/
theorem agree_on_queries (i : ℕ) : ∀ z ∈ Q i (st i), (z ∈ oracleAt i ↔ z ∈ sepOracle)

/-- B5. -/
theorem outputs_iff (i : ℕ) (o : Option (List (Fin ((dEnum i).N.a (dEnum i).N.k₁)))) :
    Nonempty (OTM2OutputsInTime (oracleAt i) (M i) (inputAt i) o (timeAt i)) ↔
      Nonempty (OTM2OutputsInTime sepOracle (M i) (inputAt i) o (timeAt i))
end Stage
```

#### B6: `sepLang B ∉ P^B`

Plan form (§6.4 B6): "`sepLang sepOracle ∉ P^sepOracle`, hence T6". True as written. Proved as
the two statements below; the `∃ B` form (T6) is left to the final assembly, as instructed.

```lean
namespace Stage
/-- If stage `i` saw `[true]`, no string of `B` has length in `[n_i, 2 n_i]`. -/
theorem length_lt_or_lt_of_accAt {i : ℕ} (h : accAt i) {z : List Bool} (hz : z ∈ sepOracle) :
    z.length < lenAt i ∨ 2 * lenAt i < z.length
/-- If stage `i` did not see `[true]`, it added `u_i ++ 0^{n_i}`. -/
theorem strAt_mem_sepOracle {i : ℕ} (h : ¬ accAt i) : strAt i ∈ sepOracle
end Stage

/-- B6. -/
theorem sepLang_not_inP : ¬ InP sepOracle (fin_encoding_string Bool) (sepLang sepOracle)

/-- B6, the form T6 will use. -/
theorem sepOracle_not_pEqNP : ¬ PEqNP sepOracle
```

Not stated this session (by instruction): T6 `separation : ∃ B, ¬ PEqNP B` (it is
`⟨sepOracle, sepOracle_not_pEqNP⟩`), T5, T7, T8, A1–A6.

---

### 4.11 Statements for session 5: the collapse oracle, A1–A3, in the form the §5 proof uses

Written before any Lean. Plan items: PLAN §6.4 A1–A3, §4.1 (D6, decided 2026-10-07), schedule
§6.10. Everything below is in namespace `Relativization`; the oracle internals are in
`Relativization.Univ`, the counter view in `Relativization.Counter`.

**How the final collapse proof will use this (A5/A6, not this session).** Assume
`L ∈ NP^A` for `A = univOracle`: a certificate alphabet `Γ₁`, a relation `R`, an exponent `k`,
a function `f` with a polynomial-time oracle decider `h` for `f` under `A` on `w#y`, and
`∀ w, L w ↔ ∃ y, |y| ≤ |w|^k ∧ R w y`, `R w y ↔ f (w, y) = true`. N4v'
(`exists_vcode_of_verifier h k`) gives `i` with `k_i = k` and `ρ : Γ₁ ≃ Fin g_i` such that
`h.tm` and `M_i` have the same outputs within the same time under every oracle on `w#y` /
`w#ρ(y)`. With `T(n) ≥ μ_i(n) + (D_i + 1) · p(μ_i(n))` and `pad w := frame i (T |w|) w.reverse`,
the budget of `pad w` is at least `p(μ_i(|w|))`, so for every `y'` with `|y'| ≤ |w|^k`, `M_i^A`
outputs `[f(w, ρ⁻¹ y')]` on `w#y'` within the budget (N4v' with `O := A`), and by F4' it
outputs `[true]` within the budget iff `f(w, ρ⁻¹ y') = true`. Then `pad w ∈ A` iff (†)
`Phi A (pad w)` iff (`Phi_frame`) `Acc A i (T |w|) w.reverse` iff
`∃ y', |y'| ≤ |w|^k ∧ f(w, ρ⁻¹ y') = true` iff `L w`. Composition with the `pad` machine (A4)
and T3 gives `L ∈ P^A`. The one property of `A` this uses is (†) below, at `x = pad w`, with
the oracle `A` itself on both sides.

#### A1: frames (`Relativization/Frame.lean`)

Plan form (§6.4 A1): "`decode (frame i T v) = (i, T, v)`, length of `frame`". True as written
(`decode` returns an `Option`, so `= some (i, T, v)`), and not enough on its own: Proposition 5
and (†) need the converse, `decode x = some (i, T, v) → x = frame i T v`, to read `|x|` off the
decoded data. Both directions are stated.

```lean
/-- `frame i T v = 1^i 0 1^T 0 v`. -/
def frame (i T : ℕ) (v : List Bool) : List Bool :=
  List.replicate i true ++ false :: (List.replicate T true ++ false :: v)
theorem frame_length (i T : ℕ) (v : List Bool) : (frame i T v).length = i + T + v.length + 2

/-- The number of leading `true`s, and the list after them. -/
def ones : List Bool → ℕ
def dropOnes : List Bool → List Bool
theorem replicate_ones_append_dropOnes (x : List Bool) :
    List.replicate (ones x) true ++ dropOnes x = x

/-- `decode x = some (i, T, v)` iff `x = frame i T v`. -/
def decode (x : List Bool) : Option (ℕ × ℕ × List Bool)
theorem decode_frame (i T : ℕ) (v : List Bool) : decode (frame i T v) = some (i, T, v)
theorem eq_frame_of_decode {x : List Bool} {i T : ℕ} {v : List Bool}
    (h : decode x = some (i, T, v)) : x = frame i T v
theorem decode_eq_some_iff {x : List Bool} {i T : ℕ} {v : List Bool} :
    decode x = some (i, T, v) ↔ x = frame i T v
theorem frame_inj {i T i' T' : ℕ} {v v' : List Bool} (h : frame i T v = frame i' T' v') :
    i = i' ∧ T = T' ∧ v = v'
theorem length_of_decode {x : List Bool} {i T : ℕ} {v : List Bool}
    (h : decode x = some (i, T, v)) : x.length = i + T + v.length + 2
```

#### A2: the oracle `A` (`Relativization/Univ.lean`)

Plan form (§6.4 A2): "`univOracle` by levels; fixpoint equation
`x ∈ A ↔ Φ (A ∩ {|z| < |x|}) x`". The levels are those of §5.4; the displayed equation is (★)
of §5.4. **(★) is true as written and too weak as the interface for A5**: §5.7 uses (†)
`x ∈ A ↔ Φ(A, x)` (PLAN §4.1 states (†) as well, citing §5.6; the §6.4 row only lists (★)).
The corrected form is (†). It is proved from (★) and the claim "truncation is invisible" of
§5.6, which is Proposition 5 (§5.5) plus the sharp locality lemma in its query-set form L4'/L6'
(`iter_congr_queries`, `outputsInTime_congr_queries`, session 4). Both (★) and (†) are stated
and proved below. Nothing in the proof of (†) is unproved at the start of this session except
Proposition 5 (arithmetic) and the elementary level lemmas; in particular no fixpoint theorem
is used: `A` is a primitive recursion on length and (†) is a consequence.

**The data of code `i`** (D6, §5.4; read off N4v as §4.6 explains): `M_i :=
(vEnum i).N.toOracleFinTM2`, `g_i := (vEnum i).g`, `k_i := (vEnum i).k`, `D_i := M_i.depth`,
and the alphabet equivalences `(vEnum i).inE`, `(vEnum i).outE`.

```lean
namespace Univ
/-- The machine of verifier code `i`. -/
noncomputable abbrev M (i : ℕ) : OracleFinTM2 := (vEnum i).N.toOracleFinTM2
/-- `μ_i(n) = n + 1 + n^{k_i}`: the longest verifier input `w#y` with `|w| = n`, `|y| ≤ n^{k_i}`. -/
noncomputable def mu (i n : ℕ) : ℕ := n + 1 + n ^ (vEnum i).k
/-- **D6.** The step budget `⌊(T ∸ μ_i(n)) / (D_i + 1)⌋`. -/
noncomputable def budget (i T n : ℕ) : ℕ := (T - mu i n) / ((M i).depth + 1)
/-- `w#y` as the machine of code `i` reads it. -/
noncomputable def input (i : ℕ) (w : List Bool) (y : List (Fin (vEnum i).g)) :
    List (Fin ((vEnum i).N.a (vEnum i).N.k₀)) :=
  ((pair_encoding (fin_encoding_string Bool) (fin_encoding_string (Fin (vEnum i).g))).encode
    (w, y)).map (vEnum i).inE.symm
theorem input_length (i : ℕ) (w : List Bool) (y : List (Fin (vEnum i).g)) :
    (input i w y).length = w.length + 1 + y.length

/-- `Acc O i T v`: some certificate `y ∈ [g_i]*` with `|y| ≤ |v|^{k_i}` makes `M_i^O` output
`[true]` on `v.reverse # y` within the budget `⌊(T ∸ μ_i(|v|)) / (D_i + 1)⌋`. -/
def Acc (O : Oracle) (i T : ℕ) (v : List Bool) : Prop :=
  ∃ y : List (Fin (vEnum i).g), y.length ≤ v.length ^ (vEnum i).k ∧
    Nonempty (OTM2OutputsInTime O (M i) (input i v.reverse y)
      (some [(vEnum i).outE.symm true]) (budget i T v.length))

/-- The membership condition `Φ(O, x)` of §5.4: `x` is a frame `frame i T v` and `Acc O i T v`. -/
def Phi (O : Oracle) (x : List Bool) : Prop :=
  ∃ i T v, decode x = some (i, T, v) ∧ Acc O i T v
theorem Phi_frame (O : Oracle) (i T : ℕ) (v : List Bool) : Phi O (frame i T v) ↔ Acc O i T v

/-- The levels `A_0 = ∅`, `A_{m+1} = A_m ∪ {x | |x| = m ∧ Φ(A_m, x)}`. -/
def level : ℕ → Oracle
  | 0 => ∅
  | m + 1 => level m ∪ {x | x.length = m ∧ Phi (level m) x}
end Univ

/-- **D6.** The oracle `A = ⋃_m A_m`. -/
def univOracle : Oracle := {x | ∃ m, x ∈ Univ.level m}
```

**The exact self-referential equation** (†), Theorem 6 of §5.6, in Lean:

```lean
theorem Univ.mem_univOracle (x : List Bool) : x ∈ univOracle ↔ Univ.Phi univOracle x
```

Unfolding `Phi` and `Acc`: `x ∈ A ↔ ∃ i T v, decode x = some (i, T, v) ∧ ∃ y : List (Fin g_i),
|y| ≤ |v|^{k_i} ∧ Nonempty (OTM2OutputsInTime A M_i (input i v.reverse y) (some [outE.symm true])
((T ∸ (|v| + 1 + |v|^{k_i})) / (D_i + 1)))`. The oracle on the right is `A` itself, untruncated.

**The exact well-definedness claim.** `A` is not defined by (†); it is defined by the
primitive recursion `level` on the length `m`, which needs no side condition, and (†) is then
*proved*. What makes (†) provable is Proposition 5 of §5.5, in Lean:

```lean
/-- **Proposition 5.** Every query asked within the budget, on every admissible certificate,
under every oracle, is strictly shorter than the frame. -/
theorem Univ.length_lt_of_mem_queries {O : Oracle} {i T : ℕ} {v : List Bool}
    {y : List (Fin (vEnum i).g)} (hy : y.length ≤ v.length ^ (vEnum i).k) {z : List Bool}
    (hz : z ∈ (Univ.M i).queries O (Univ.input i v.reverse y) (Univ.budget i T v.length)) :
    z.length < (frame i T v).length
```

The bound used, with `β = budget i T |v|`, `D = D_i`, `μ = μ_i(|v|)`:

* if `β = 0`: `(M i).queries O l 0 = ∅` (`Finset.range 0`), so there is nothing to prove. This
  is the budget-0 case of PLAN §7.4 item 3: the length-form bound `μ ≤ |x|` would be false
  here (take `T = 0`), and only the sharp form (queries actually asked) works;
* if `β ≥ 1`: L3 for the query set (`length_le_of_mem_queries`) gives `|z| ≤ |input| + β · D`
  with `|input| = |v| + 1 + |y| ≤ μ`; `β · (D + 1) ≤ T ∸ μ` (`Nat.div_mul_le_self`) with
  `β ≥ 1` gives `T ≥ μ + β · D + β > μ + β · D`; and `T < i + T + |v| + 2 = |frame i T v|`. So
  `|z| ≤ μ + β · D < T < |x|`, with margin at least `i + |v| + 3`.

This is the bound of §5.5 with `j · D_i` (`j < β`) replaced by the coarser `β · D_i` of L3 for
the query set; the slack `β ≥ 1` absorbs the difference.

**The fixpoint argument: full statement and proof, checked line by line against the Lean
definitions.**

Statement. (a) `∀ x, x ∈ univOracle ↔ Phi (univOracle ∩ {z | z.length < x.length}) x` (★);
(b) `∀ x, x ∈ univOracle ↔ Phi univOracle x` (†); (c) `∀ B : Oracle, (∀ x, x ∈ B ↔ Phi B x) →
B = univOracle` (uniqueness, the second half of Theorem 6; not needed for T5, cheap).

```lean
namespace Univ
theorem mem_level_succ (m : ℕ) (x : List Bool) :
    x ∈ level (m + 1) ↔ x ∈ level m ∨ (x.length = m ∧ Phi (level m) x)
theorem length_lt_of_mem_level {m : ℕ} {x : List Bool} (h : x ∈ level m) : x.length < m
theorem level_mono : Monotone level
theorem mem_level_iff_of_lt {m m' : ℕ} {x : List Bool} (hx : x.length < m) (h : m ≤ m') :
    x ∈ level m' ↔ x ∈ level m
theorem mem_univOracle_iff_level (x : List Bool) : x ∈ univOracle ↔ x ∈ level (x.length + 1)
theorem univOracle_inter_eq_level (m : ℕ) : univOracle ∩ {z | z.length < m} = level m
/-- (★), the plan's form. -/
theorem mem_univOracle_iff_trunc (x : List Bool) :
    x ∈ univOracle ↔ Phi (univOracle ∩ {z | z.length < x.length}) x
/-- Truncation is invisible: `Acc O i T v` and `Phi O x` depend on `O` only below the frame. -/
theorem Acc_congr {O O' : Oracle} (i T : ℕ) (v : List Bool)
    (h : ∀ z : List Bool, z.length < (frame i T v).length → (z ∈ O ↔ z ∈ O')) :
    Acc O i T v ↔ Acc O' i T v
theorem Phi_congr {O O' : Oracle} (x : List Bool)
    (h : ∀ z : List Bool, z.length < x.length → (z ∈ O ↔ z ∈ O')) : Phi O x ↔ Phi O' x
/-- (†), Theorem 6 of §5.6: the self-referential equation. -/
theorem mem_univOracle (x : List Bool) : x ∈ univOracle ↔ Phi univOracle x
/-- Uniqueness. -/
theorem eq_univOracle_of_fixpoint {B : Oracle} (hB : ∀ x, x ∈ B ↔ Phi B x) : B = univOracle
end Univ
```

Proof, checked against `Oracle.lean` (D1, D2), `Queries.lean` (L3, L4', L6'), `Codes.lean`
(`VCode`, `vEnum`, N4v') and D6 above:

1. *Levels.* `level (m + 1) = level m ∪ {x | x.length = m ∧ Phi (level m) x}` by `rfl`.
   `length_lt_of_mem_level` by induction on `m` (`level 0 = ∅`; an element of `level (m + 1)`
   is in `level m`, so of length `< m`, or has length `= m`). `level_mono` from
   `level m ⊆ level (m + 1)` (`Set.subset_union_left`). `mem_level_iff_of_lt`: induction on
   `m' ≥ m`; the strings a level `m'' ≥ m` adds have length `m'' ≥ m > |x|`.
2. *(★).* `x ∈ univOracle ↔ ∃ m, x ∈ level m ↔ x ∈ level (|x| + 1)`: `→` by
   `length_lt_of_mem_level` (`|x| < m`, i.e. `|x| + 1 ≤ m`) and `mem_level_iff_of_lt`; `←`
   trivial. Then `mem_level_succ` at `m = |x|`: the disjunct `x ∈ level |x|` is impossible
   (`length_lt_of_mem_level`), the other is `|x| = |x| ∧ Phi (level |x|) x`. Finally
   `level |x| = univOracle ∩ {z | |z| < |x|}` by `Set.ext` from `mem_univOracle_iff_level` and
   `mem_level_iff_of_lt` (`univOracle_inter_eq_level`). This is (★) with `Φ := Phi`, PLAN
   §6.4's A2 equation word for word.
3. *`Acc_congr`, `Phi_congr`.* For each `y` with `|y| ≤ |v|^{k_i}` apply **L6'**
   `(M i).outputsInTime_congr_queries (input i v.reverse y) (some [outE.symm true])
   (budget i T |v|)` with `A := O`, `A' := O'`; its hypothesis
   `∀ z ∈ (M i).queries O (input i v.reverse y) (budget i T |v|), (z ∈ O ↔ z ∈ O')` is
   Proposition 5 (`|z| < |frame i T v|`) followed by `h`. L6' is an iff, so both directions of
   `Acc O i T v ↔ Acc O' i T v` follow by `exists_congr`. `Phi_congr`: unfold `Phi`; for fixed
   `(i, T, v)` with `decode x = some (i, T, v)`, A1 gives `x = frame i T v`, so the hypothesis of
   `Acc_congr` is `h`. Checked: L6' is stated for `l : List (tm.Γ tm.k₀)`, and `M i` is a
   `noncomputable abbrev` (as `Stage.M`), so `(M i).Γ (M i).k₀` is reducibly
   `Fin ((vEnum i).N.a (vEnum i).N.k₀)`, the type of `input i w y` (§10.4 item 6); the `t` of
   L6' is the budget itself, the `t` of `Acc`; L6' needs `tm.queries A l t` for the *first*
   oracle `A := O`, which is the set Proposition 5 bounds; the depth in
   `length_le_of_mem_queries` is `(M i).depth`, the `D_i` of `budget`.
4. *(†).* (★) and `Phi_congr` with `O := univOracle ∩ {z | |z| < |x|}`, `O' := univOracle`,
   whose hypothesis is `z ∈ univOracle ∧ |z| < |x| ↔ z ∈ univOracle` for `|z| < |x|`, trivial.
   This is Theorem 6 (existence) of §5.6.
5. *Uniqueness.* With `hB`, show `∀ m x, |x| < m → (x ∈ B ↔ x ∈ level m)` by induction on
   `m`: `m = 0` vacuous; at `m + 1` with `|x| < m` use the induction hypothesis and
   `mem_level_iff_of_lt`; with `|x| = m`, `x ∈ B ↔ Phi B x` (`hB`) `↔ Phi (level m) x`
   (`Phi_congr`, hypothesis from the induction hypothesis since `|z| < |x| = m`)
   `↔ x ∈ level (m + 1)` (`mem_level_succ`, first disjunct impossible). Then `Set.ext` with
   `mem_univOracle_iff_level`.

Where the §5 proof's form could have failed and did not: (i) §5.6 says "by Proposition 5 every
query asked in the first `β` steps is shorter than `x`"; the Lean query set `queries O l β` is
exactly the queries asked at steps `0, …, β − 1` plus the junk value `[]` (§10.4 item 2), which
is shorter than any frame, so nothing is lost; (ii) §5.5's bound `μ + j · D_i` for `j < β` is
replaced by `μ + β · D_i` from L3 for the query set, still `< T` by the slack `β` (above);
(iii) the case `β = 0` is covered by `Finset.range 0 = ∅`, not by a length bound; (iv) the
oracle-independence of codes (§5.3 item 1) holds because `vEnum` is a closed term and `M`,
`mu`, `budget`, `input` mention no oracle; (v) no `Decidable` instance is needed: `Phi` is a
`Prop` in a set-builder, as in `Stage.step` (§10.4 item 3); (vi) (†) is an equation between
`Prop`s for every `x`, not a statement about a least or greatest fixpoint, and nothing
monotone in `O` is claimed or needed (`Phi` is not monotone in `O`: a verifier may accept
because a query is answered *no*).

Nothing in A2 depends on anything unproved: it uses A1, N2 (`vEnum`), L3/L4'/L6' for the query
set (session 4) and `Finset` facts. F4', N4v' and `oracleComp` enter only in A5.

#### A3: the counter view and the power loop (`Relativization/Counter.lean`)

Plan form (§6.4 A3): "counter view and power loop, extracted from PvsNP, E, 450 ported lines".
Adequate as written; made precise here. Source: `D:\PvsNP` at `c271016`, `D3OneHot.lean`
section `[LIB]` (lines 25–225: `SK`, `SΓ`, `st`, `st_c`, `st_out`, `update_st_c`,
`update_st_nil`, `update_st_out`, `addU_nil`, `emitS`, `emitOut`, `incS`, `drainS`, `xferES`,
`copyS`, `mulS`, `mulS_run`, `gapS`, `bud_st`, `st_eta`, `stLoop`) and `Pre.lean` section
`[LIB]` (lines 35–210: `decS_pos`, `decS_zero`, `tg`, `tg_keys`, `tg_nodupKeys`, `dlookup_tg`,
`dlookup_tg_out`, `xf`, `xferS`, `PW`, `powS`, `powB`, `pow_run`), plus the stage type `MS`
(`D3Fam.lean` line 302) and `outputsOfRunLe` (`Pkg.lean` lines 307–312). Both sections depend
only on `Prog` (ported verbatim in session 3) and Mathlib, so they are copied verbatim under one
namespace `Relativization.Counter`; `D:\PvsNP` is not modified. The logs will carry the diff of
the bodies, as `logs/session3-port-diff.txt` did.

```lean
namespace Relativization.Counter
/-- Stages of the multiplication loop. -/
inductive MS | head | body | l2 | rest
/-- Stacks of a counter machine: a Bool output and unit counters indexed by `C`. -/
inductive SK (C : Type) | out | c (x : C)
abbrev SΓ (C : Type) : SK C → Type          -- `.out ↦ Bool`, `.c _ ↦ Unit`
/-- Stacks from counter values `f` and output `o`. -/
def st (f : C → ℕ) (o : List Bool) : ∀ k, List (SΓ C k)
-- wrappers: each restates a `Prog` primitive in the `st f o` view with an exact step count
theorem emitS, emitOut, incS, drainS, xferES, copyS, mulS_run, gapS, decS_pos, decS_zero, xferS
theorem stLoop                                 -- a runtime `for` loop in the counter view (`RunLe`)
/-- Power-loop stages and program: `p ← p · b^kc`. -/
inductive PW | hd | mul (s : MS) | drn | mv
def powS (b kc p q ad t : C) (mk : PW → Λ) (exit : Λ) : PW → TM2.Stmt (SΓ C) Λ Bool
def powB (j p b : ℕ) : ℕ := j * (p * (b + 1) ^ j * (3 * b + 5) + 5) + 1
/-- **The power loop.** From `kc = j`, `q = ad = t = 0`: ends with `p ← p · b^j`, `kc = 0`,
within `powB j (F p) (F b)` steps. -/
theorem pow_run {b kc p q ad t : C} {mk : PW → Λ} {exit : Λ}
    (hp : ∀ s, M (mk s) = powS b kc p q ad t mk exit s) (hnd : [b, kc, p, q, ad, t].Nodup) :
    ∀ (j : ℕ) (F : C → ℕ), F kc = j → F q = 0 → F ad = 0 → F t = 0 →
      ∀ (v : Bool) (o : List Bool),
      RunLe M (powB j (F p) (F b)) ⟨some (mk .hd), v, st F o⟩
        ⟨some exit, false, st (update (update F p (F p * F b ^ j)) kc 0) o⟩
/-- A bounded run from `initList` to `haltList` is a `TM2OutputsInTime` certificate (PvsNP
`Pkg.outputsOfRunLe`). -/
noncomputable def _root_.Turing.TM2OutputsInTime.ofRunLe {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : List (tm.Γ tm.k₁)} {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l')) :
    TM2OutputsInTime tm l (some l') B
end Relativization.Counter
```

How A4 will use it (not this session): `pad w = frame i ((|w| + c')^d) w.reverse` is a plain
machine with an input stack, the output stack and counters. The copy loop (input to output,
counting `|w|`) is hand-written as `Sep.revTM` was; `(|w| + c')^d` is `emitS` (`c'` units) then
`pow_run` with `p = 1`, `b = |w| + c'`, `kc = d`; the frame's `1^T` is `xferES` from the counter
`p`, the constants are `emitOut`. The counter sub-machine has stacks `SK C` and is embedded into
the host with the input stack through `Emb.run_embed` (plain host; PvsNP `Pre.lean` `[FULL]` is
the template), or the view is given an input stack: A4's decision. `pow_run` is a `RunLe`, so
the packaging is `TM2OutputsInTime.ofRunLe`, not `ofRun`.

Two notes for the reviewer: `deriving DecidableEq, Fintype` on `SK`, `MS`, `PW` is copied from
PvsNP; sessions 1–4 had no `deriving`. The handlers generate ordinary instances (listed in
§11.4), checked by the kernel like any definition, on new types only. `nlinarith` (inside
`pow_run`) is used for the first time in this repository.

Not stated this session (by instruction): A4 (`pad`), A5, A6, T5–T8.

### 4.12 Statements for session 6: the pad machine, A4, in the form A5 uses

Written before any Lean. Plan items: PLAN §6.4 A4 ("`pad` as a `TM2ComputableInPolyTime`",
550 lines), §6.11 sessions 6–7, §7 "`pad` on the counter view". Everything below is in
namespace `Relativization`; the machine internals are in `Relativization.Pad`
(`Relativization/Pad.lean`). Sessions 1–5 are not modified.

**How A5 will use A4** (§4.11 "How the final collapse proof will use this", §5.7). A5 has
`i`, `ρ` with `(vEnum i).k = k` from N4v' (`exists_vcode_of_verifier`) and the verifier's
polynomial `p := h.time`. It needs `T : ℕ → ℕ` with `T n ≥ μ_i(n) + (D_i + 1) · p(μ_i(n))` for
every `n`. The right-hand side is `q.eval n` for the polynomial
`q := X + 1 + X^k + C (D_i + 1) * p.comp (X + 1 + X^k)` (`Univ.mu i n = n + 1 + n^(vEnum i).k`),
and `eval_le_pow q` (PvsNP `Pkg.lean` 395, to be ported in A5) gives `c' ≥ 1` and `d` with
`q.eval n ≤ (n + c')^d`. So `T n := (n + c')^d` and `pad w := frame i ((|w| + c')^d) w.reverse`.
A5 composes with T3: from `⟨g, hg, hgA⟩ := oracle_inP A`,
`oracleComp A (Pad.padComputable i c' d) hg : OTM2ComputableInPolyTime A
(fin_encoding_string Bool).encode finEncodingBoolBool.encode (g ∘ padFun i c' d)`, and
`L w ↔ g (padFun i c' d w) = true ↔ padFun i c' d w ∈ A ↔ Phi A (frame i T v) ↔ …`. The only
facts about `pad` that A5 uses are the definition of `padFun` (through `Phi_frame`/`decode_frame`
at `x = padFun i c' d w`) and `padComputable`. So A4 is one function and one
`TM2ComputableInPolyTime`, parametric in `i c' d : ℕ`:

```lean
/-- `padFun i c' d w = frame i ((|w| + c')^d) w.reverse = 1^i 0 1^{(|w| + c')^d} 0 w.reverse`. -/
def padFun (i c' d : ℕ) (w : List Bool) : List Bool :=
  frame i ((w.length + c') ^ d) w.reverse

namespace Pad
/-- Step bound of the pad machine on an input of length `n`. `i` does not enter: the constant
block `1^i 0` is emitted in one step. `powB` is A3's bound for the power loop. -/
def padB (c' d n : ℕ) : ℕ := 2 * n + c' + 9 + powB d 1 (n + c') + (n + c') ^ d

/-- The pad machine: input stack `inp` over `Bool`, output stack `cv .out` over `Bool`, six unit
counters, states `Bool`, initial state `false`. -/
def padTM (i c' d : ℕ) : FinTM2

/-- Correctness and time, in one statement: from `initList (padTM i c' d) w` the machine reaches
`haltList (padTM i c' d) (padFun i c' d w)` within `padB c' d |w|` steps. -/
theorem pad_run (i c' d : ℕ) (w : List Bool) :
    RunLe (padTM i c' d).m (padB c' d w.length) (initList (padTM i c' d) w)
      (haltList (padTM i c' d) (padFun i c' d w))

/-- `padB c' d` is the evaluation of a polynomial with natural coefficients. -/
theorem padB_poly (c' d : ℕ) : IsPoly (padB c' d)

/-- **A4.** `padFun i c' d` is computable by a plain machine in polynomial time, on the identity
encoding of binary strings on both sides. -/
noncomputable def padComputable (i c' d : ℕ) :
    TM2ComputableInPolyTime (fin_encoding_string Bool).encode (fin_encoding_string Bool).encode
      (padFun i c' d)
end Pad
```

with `inputAlphabet := Equiv.refl Bool`, `outputAlphabet := Equiv.refl Bool`,
`time := Classical.choose (padB_poly c' d)` and `outputsFun w := TM2OutputsInTime.ofRunLe` of
`pad_run` (A3's packaging, since `pow_run` is a `RunLe`). `IsPoly f := ∃ p : Polynomial ℕ,
∀ n, f n = p.eval n` with its five closure lemmas (`const`, `id`, `add`, `mul`, `pow`) is PvsNP
`Pre.lean` 717–735, to be ported verbatim into `Pad.lean`.

**Output format.** `haltList (padTM i c' d) l'` is the configuration with label `none`, state
`false` (= `initialState`), stack `cv .out = l'` and every other stack (`inp`, the six counters)
empty, exactly as Mathlib's `haltList` demands; `l' = padFun i c' d w` read top-down, so the top
symbol is the first `true` of `1^i` (for `i ≥ 1`) and the bottom is the last bit of `w.reverse`,
that is the first bit of `w`. Both alphabets are `Bool` itself, so
`(fin_encoding_string Bool).encode w = w` and the `List.map (Equiv.refl Bool).invFun` of the
structure's fields is handled as in `Sep.revComputable` (`List.map_id`).

**Exact time bound, as a function of the input.** For `n = |w|` and `T = (n + c')^d`:

| Phase | Label(s) | Steps | Effect |
|---|---|---|---|
| copy loop (host) | `rd` | `n + 1` (exact, one per bit plus the exit) | `inp = []`, `out = w.reverse`, counter `b = n`, state `false` |
| separator | `cp sep1` | 1 | `out = false :: w.reverse` (`emitOut`) |
| base | `cp addc` | 1 | `b = n + c'` (`emitS`, `c'` units) |
| power init | `cp one`, `cp exp` | 1 + 1 | `p = 1`, `kc = d` (`emitS`) |
| power loop | `cp (pw s)` | `≤ powB d 1 (n + c')` (`pow_run`) | `p = 1 · (n + c')^d = T`, `kc = 0`; `q = ad = t = 0` before and after |
| emit `1^T` | `cp emitT` | `T + 1` (exact, `xferES`) | `out = 1^T 0 w.reverse`, `p = 0` |
| prefix | `cp sep2` | 1 | `out = 1^i 0 1^T 0 w.reverse = frame i T w.reverse` (`emitOut`) |
| drain | `cp drn` | `n + c' + 1` (exact, `drainS`) | `b = 0`; all counters `0` |
| halt (host) | `cp fin` | 1 | label `none` |
| **total** | | `2n + c' + 9 + powB d 1 (n + c') + (n + c')^d = padB c' d n` | |

where `powB j p b = j * (p * (b + 1)^j * (3b + 5) + 5) + 1` (A3, `Counter.powB`), so `padB c' d`
has degree `d + 1` in `n` for `d ≥ 1`. The bound is `RunLe`, not `Run`: every phase is exact
except the power loop, whose `pow_run` is a `RunLe`.

**What the machine does with the counter and the frame from A1.**

* Stacks `PK := inp | cv (k : SK PC)` with `PC := b | kc | p | q | ad | t`; alphabets
  `PΓ .inp = Bool`, `PΓ (.cv k) = SΓ PC k` (so `cv .out` is the Bool output stack of the counter
  view and `cv (.c x)` a unit counter). Labels `PL := rd | cp (l : CL)` with
  `CL := sep1 | addc | one | exp | pw (s : PW) | emitT | sep2 | drn | fin`. States `Bool`: forced,
  because `Emb.mapS` keeps the state type and the counter view is over `Bool`; hence the copy
  loop cannot remember "popped `false`" versus "popped nothing" in the state and peeks first
  (as PvsNP's `rdT` does), unlike `Sep.revTM`, whose state is `Option _`.
* The copy loop (host, one label, hand-written as `Sep.revTM` was): `peek inp`; if nonempty,
  `pop inp` into the state, `push (cv .out)` the state, `push (cv (.c b)) ()`, `goto rd`; if
  empty, `goto (cp sep1)`. One `TM2.step` per iteration. Popping `w` head-first and pushing
  reverses it: `out = w.reverse` is the `v` of the frame, as `Sep.revTM` produced
  `(w ++ y).reverse`. The same loop counts `|w|` into the counter `b`.
* The counter sub-machine `cprog i c' d : CL → TM2.Stmt (SΓ PC) CL Bool` is a program of the
  counter view (A3) and is run with A3's wrappers in the `st F o` view: `emitOut`, `emitS` (×3),
  `pow_run` (`b kc p q ad t`, `mk := CL.pw`, `exit := .emitT`), `xferES`, `emitOut`, `drainS`,
  chained with `Bud` as PvsNP `cprog_run` chains them. `xferES` prepends `rep [true] T`, which
  is `List.replicate T true` (a three-line lemma `rep_singleton`, new). The output after `sep2`
  is `(replicate i true ++ [false]) ++ (replicate T true ++ false :: w.reverse)`, which is
  `frame i T w.reverse` by `List.append_assoc` and `List.singleton_append` against A1's
  definition `frame i T v = replicate i true ++ false :: (replicate T true ++ false :: v)`. The
  machine never decodes; `frame_length` and `decode` are not used in A4.
* The host program `pprog i c' d : PL → TM2.Stmt PΓ PL Bool` is the copy loop at `rd` and
  `mapS padEmb PL.cp (cprog i c' d l)` at `cp l`, where `padEmb : SEmb (SΓ PC) PΓ` is
  `e := PK.cv`, `ι := fun _ => Equiv.refl _`. At `cp fin` the host statement is
  `mapS … .halt = .halt`, one step from `⟨some (cp fin), false, S⟩` to `⟨none, false, S⟩`.
  `initList (padTM i c' d) w = ⟨some rd, false, pst w F0 []⟩` and
  `haltList (padTM i c' d) l' = ⟨none, false, pst [] F0 l'⟩` for the stack builder
  `pst (s : List Bool) (F : PC → ℕ) (o : List Bool)` (`inp ↦ s`, `cv k ↦ st F o k`) and
  `F0 := fun _ => 0`, as `Sep.initList_eq`/`haltList_eq` and PvsNP `initList_full`.

**The design decision: how the pad machine gets its counter.** Two routes, assessed before
choosing (brief item 2).

*Route E — embed the counter sub-machine with `Emb.run_embed` (PvsNP `Pre.lean` `[FULL]`,
`[COMP]`, `[REAL]` as template: `embC`, `embeds_C`, `agree_C`, `pre_run`, `fullTM`,
`initList_full`).*

* Reused unchanged: from A3 (`Counter.lean`) `SK`, `SΓ`, `st`, `st_c`, `st_out`, `emitS`,
  `emitOut`, `drainS`, `xferES`, `bud_st`, `MS`, `PW`, `powS`, `powB`, `pow_run`,
  `TM2OutputsInTime.ofRunLe`; from session 3 (`Emb.lean`) `SEmb`, `mapS`, `Embeds`, `Agree`,
  `Frame`, `runLe_embed`; from session 3 (`Prog.lean`) `Flag Bool`, `Run`, `Run.single`,
  `Run.head`, `Run.le`, `Run.bud`, `RunLe`, `RunLe.trans`, `RunLe.mono`, `Bud`, `Bud.start`,
  `Bud.fin`, `cnt`, `cnt_succ`, `rep`, `rep_succ`, `emitR`, `xferE`, `xfer`; from A1 `frame`;
  from Millennium/Mathlib `fin_encoding_string`, `TM2ComputableInPolyTime`, `initList`,
  `haltList`. New code: the types and programs, the copy loop, the embedding (three one-line
  proofs), `pad_run`, `IsPoly` (ported), `padB_poly`, `rep_singleton`, the packaging.
* Changes to session 1–5 definitions: **none**.
* Estimate: about 330 lines (types and programs 60; `cprog_run` 40; copy loop with `pst` and
  its three `update_pst_*` lemmas 60; embedding and reading the final host stacks off
  `Agree`/`Frame` 30; `pad_run` with `initList`/`haltList` 50; `IsPoly` and `padB_poly` 40;
  packaging 20; header 30). Under the plan's 550.
* Main risk: the host-side bookkeeping, not the arithmetic. (i) `List.map ⇑(Equiv.refl _) l`
  is `l` only up to defeq (PvsNP writes `(List.map_id _).symm` as a term, §11.4 item 7 style);
  (ii) `deriving Fintype` on the nested `PK | inp | cv (k : SK PC)` (PvsNP's
  `FK | h (k : HK) | raw | pc (x : PS)` derived without trouble); (iii) the `simp` set for the
  copy-loop step on `pst` (`Sep.step_cons` pattern). All three are patterns already used in
  this repository or in the template.

*Route V — give the counter view an input stack.*

* V1, extend `Counter.SK C` with a constructor `inp`: changes a session 5 definition and the
  statement of every wrapper over it (`st`, `emitS`, …, `pow_run`): **not allowed without
  stopping**, and `pow_run`'s 105-line proof would have to be re-checked against the changed
  type. Not taken.
* V2, a new view `SK' C := inp | out | c x` in the new file, with its own `st'` and
  `update_st'_*`, and every wrapper the pad needs re-proved over it (`emitS'`, `emitOut'`,
  `drainS'`, `xferES'`, `decS'_pos/zero`, `xferS'`, `mulS_run'`, `pow_run'`): changes no
  session 1–5 definition, but `pow_run` (105 lines), `mulS_run` and `xferS` (50) cannot be
  transported from `SK C` to `SK' C` without an embedding lemma — which is Route E — so they
  must be copied with the stack type changed. The `Prog` primitives are generic in `K`, so the
  copies are mechanical, but they duplicate about 200 lines of A3 and are exactly the
  duplication the counter view was introduced to avoid.
* Reused unchanged: `Prog` entirely, `Counter.powB`, `PW`, `MS` (the types), `ofRunLe`; `Emb`
  unused. Changes to session 1–5 definitions: none (V2) or `Counter.SK` (V1).
* Estimate (V2): about 480 lines (Route E minus the 30 embedding lines, plus about 200 of
  duplicated view lemmas, minus about 20 of host bookkeeping that becomes view bookkeeping).
* Main risk: two views that drift apart, and the duplicated `pow_run'`, whose `nlinarith` tail
  is the most fragile proof in `Counter.lean`.

**Choice: Route E.** It changes no earlier definition, reuses `pow_run` as it stands, follows
a template that is known to compile at this Mathlib commit (every PvsNP port so far compiled
unchanged, §9.4, §11.4), and is about 150 lines shorter. V1 is excluded by the rules; V2 is
strictly more code for the same theorem.

**Order of work** (brief item 3): statement (above), machine definition (`PC`, `PK`, `PΓ`,
`CL`, `PL`, `cprog`, `pprog`, `padTM`), correctness of the output (`cprog_run`, the copy loop,
`pad_run`), then the time bound (`IsPoly`, `padB_poly`, `padComputable`). The machine is named
explicitly in every wrapper application (`(M := cprog i c' d)`, `(M := pprog i c' d)`) and in
`runLe_embed (E := padEmb) PL.cp …`, as §10.4 item 5 advises.

Not done this session (by instruction): A5, A6, T5–T8. `eval_le_pow` is A5's.

### 4.13 Statements for session 7: the reduction (A5), the collapse (A6), and T5–T7

Written before any Lean. Plan items: PLAN §6.4 A5, A6 and "Main"; §6.2 T5, T6, T7; §6.12
"Exact remaining work for T7", items 1–7. Everything below is in namespace `Relativization`.
Items 1–6 (`eval_le_pow`, the exponent pair, the budget bound, the reduction, `NP^A ⊆ P^A`,
`PEqNP univOracle`) go into a new file `Relativization/Collapse.lean`; the three final theorems
T5, T6, T7 (item 7) into a second new file `Relativization/BakerGillSolovay.lean`, which imports
`Collapse` and `Stage` and nothing else new. PLAN §6.12 put all seven items into
`Collapse.lean`; the split keeps the collapse file independent of the separation half and puts
the main theorem in a file a reviewer can read in one screen. Sessions 1–6 are not modified.
Not done this session, by instruction: T8 and the red-team pass.

**Plan forms, assessed** (brief item 2).

* **A5**, PLAN §6.4: "Reduction is correct: `L w ↔ pad w ∈ univOracle` for
  `L ∈ NP^univOracle`." True, and adequate once `pad` is made explicit: `pad` depends on `L`
  through the code `i` of its verifier and the exponent pair `c', d` of the verifier's
  polynomial, so the statement quantifies them existentially,
  `∃ i c' d, ∀ w, L w ↔ padFun i c' d w ∈ univOracle`. Not false, not too weak: this is
  exactly what A6 consumes, and `padFun i c' d` is the function A4 computes.
* **A6**, PLAN §6.4: "T5", i.e. `∃ A, PEqNP A`. Adequate; proved through `PEqNP univOracle`
  (`univOracle_pEqNP`), whose two directions are T4 (`inP_subset_inNP`, session 1) and
  Theorem 7 of §5.7 (`inNP_subset_inP`, new, from A5 with F7, T3 and A4).
* **T5, T6, T7**, PLAN §6.2 / NOTES §3: proved word for word as stated there. T7 is a
  conjunction of two existentials about **the same** predicate `PEqNP : Oracle → Prop` of
  `Classes.lean`, both oracles of the one type `Oracle := Set (List Bool)` (brief item 4); it is
  not a conjunction of claims about two notions. T6 is `⟨sepOracle, sepOracle_not_pEqNP⟩` (B6,
  session 4), as §10.4 item 8 anticipated.
* **`eval_le_pow`**, PLAN §6.12 item 1: ported verbatim from PvsNP `Pkg.lean` 391–416
  (`pow_weaken`, `eval_le_pow`); `eval_mono'` of that file is already `Comp.eval_mono`.

**Statements, in the form the proofs use.**

```lean
/-- PvsNP `Pkg.pow_weaken`, `Pkg.eval_le_pow`, verbatim: every polynomial with natural
coefficients is bounded by some `(j + c)^e` with `c ≥ 1`. -/
theorem pow_weaken {j c e c' e' : ℕ} (hc : 1 ≤ c) (h1 : c ≤ c') (h2 : e ≤ e') :
    (j + c) ^ e ≤ (j + c') ^ e'
theorem eval_le_pow (p : Polynomial ℕ) : ∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c) ^ e

/-- Time weakening: an output within `t` steps is an output within any `t' ≥ t`. -/
def OTM2OutputsInTime.mono {A : Oracle} {tm : OracleFinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {t t' : ℕ} (h : OTM2OutputsInTime A tm l l' t)
    (ht : t ≤ t') : OTM2OutputsInTime A tm l l' t'

namespace Collapse
/-- `μ_i` as a polynomial: `X + 1 + X^{k_i}`. -/
noncomputable def muPoly (i : ℕ) : Polynomial ℕ := X + 1 + X ^ (vEnum i).k
theorem muPoly_eval (i n : ℕ) : (muPoly i).eval n = Univ.mu i n
/-- `μ_i + (D_i + 1) · (p ∘ μ_i)`: the polynomial `T` must dominate (§5.7). -/
noncomputable def padPoly (i : ℕ) (p : Polynomial ℕ) : Polynomial ℕ :=
  muPoly i + C ((Univ.M i).depth + 1) * p.comp (muPoly i)
theorem padPoly_eval (i : ℕ) (p : Polynomial ℕ) (n : ℕ) :
    (padPoly i p).eval n = Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n)
/-- The exponent pair (PLAN §6.12 item 2): `T(n) = (n + c')^d ≥ μ_i(n) + (D_i + 1) · p(μ_i(n))`. -/
theorem exists_exponents (i : ℕ) (p : Polynomial ℕ) :
    ∃ c' d : ℕ, ∀ n, Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n) ≤ (n + c') ^ d
/-- With such `c', d`, the budget of `frame i ((n + c')^d) v`, `|v| = n`, is at least `p(μ_i(n))`. -/
theorem eval_le_budget {i c' d : ℕ} {p : Polynomial ℕ}
    (hT : ∀ n, Univ.mu i n + ((Univ.M i).depth + 1) * p.eval (Univ.mu i n) ≤ (n + c') ^ d)
    (n : ℕ) : p.eval (Univ.mu i n) ≤ Univ.budget i ((n + c') ^ d) n
/-- `Acc` at a reversed string, the double reversal removed. -/
theorem Acc_reverse (O : Oracle) (i T : ℕ) (w : List Bool) :
    Univ.Acc O i T w.reverse ↔ ∃ y : List (Fin (vEnum i).g), y.length ≤ w.length ^ (vEnum i).k ∧
      Nonempty (OTM2OutputsInTime O (Univ.M i) (Univ.input i w y)
        (some [(vEnum i).outE.symm true]) (Univ.budget i T w.length))
/-- Membership of the pad in `A`: (†) `Univ.mem_univOracle`, `Univ.Phi_frame`, `Acc_reverse`. -/
theorem padFun_mem_iff (i c' d : ℕ) (w : List Bool) :
    padFun i c' d w ∈ univOracle ↔ ∃ y : List (Fin (vEnum i).g),
      y.length ≤ w.length ^ (vEnum i).k ∧
      Nonempty (OTM2OutputsInTime univOracle (Univ.M i) (Univ.input i w y)
        (some [(vEnum i).outE.symm true]) (Univ.budget i ((w.length + c') ^ d) w.length))
end Collapse

/-- **A5** (the claim of Theorem 7, §5.7). Every `L ∈ NP^A`, `A = univOracle`, is reduced to
`A` by some pad. -/
theorem exists_pad_reduction (L : Language (List Bool))
    (hL : InNP univOracle (fin_encoding_string Bool) L) :
    ∃ i c' d : ℕ, ∀ w, L w ↔ padFun i c' d w ∈ univOracle

/-- A pad reduction puts `L` in `P^A`: the pad machine (A4) followed by the self-decider (T3),
composed by F7. -/
theorem inP_of_pad_reduction {L : Language (List Bool)} {i c' d : ℕ}
    (h : ∀ w, L w ↔ padFun i c' d w ∈ univOracle) : InP univOracle (fin_encoding_string Bool) L

/-- Theorem 7 of §5.7: `NP^A ⊆ P^A` for `A = univOracle`. -/
theorem inNP_subset_inP (L : Language (List Bool)) :
    InNP univOracle (fin_encoding_string Bool) L → InP univOracle (fin_encoding_string Bool) L

/-- **A6.** `P^A = NP^A` for `A = univOracle`. -/
theorem univOracle_pEqNP : PEqNP univOracle

/-- **T5.** -/ theorem collapse : ∃ A : Oracle, PEqNP A
/-- **T6.** -/ theorem separation : ∃ B : Oracle, ¬ PEqNP B
/-- **T7.** -/ theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B)
```

**Proof of A5, checked against the Lean definitions** (PLAN §6.12 items 3–5; §5.7).

Unfold `InNP` (D3): `Γ₁` with `[Fintype Γ₁]`, `R : List Bool → List Γ₁ → Prop`, `k : ℕ`, the
`InP` clause as `⟨f, h, hR⟩` with
`h : OTM2ComputableInPolyTime univOracle (pair_encoding (fin_encoding_string Bool)
(fin_encoding_string Γ₁)).encode finEncodingBoolBool.encode f` and
`hR : ∀ p, R p.1 p.2 ↔ f p = true`; and `hLR : ∀ w, L w ↔ ∃ y, |y| ≤ |w|^k ∧ R w y`. N4v'
(`exists_vcode_of_verifier h k`, §4.6) gives `i`, `ρ : Γ₁ ≃ Fin g_i`, `k_i = k` (which is
substituted, `k := k_i`, everywhere) and `hsim`: for every oracle `O`, `w`, `y`, `b`, `t`,
`h.tm^O` outputs `[b]` on `w#y` within `t` iff `M_i^O` outputs `[outE.symm b]` on
`w#ρ(y)` within `t`. `exists_exponents i h.time` gives `c', d` with `hT`. Fix `w` and write
`β := Univ.budget i ((|w| + c')^d) |w|`.

*Item 3.* For `y : List Γ₁` with `|y| ≤ |w|^{k_i}`: `h.outputsFun (w, y)` is an output of
`h.tm` under `univOracle` within `h.time.eval |w#y|`; `|w#y| = |w| + 1 + |y|`
(`pair_encoding.length_eq`; both encodings are identities) `≤ μ_i(|w|)`, so by `Comp.eval_mono`
and `eval_le_budget hT |w|` it is an output within `β` (`OTM2OutputsInTime.mono`).
`hsim univOracle w y (f (w, y)) β` turns it into an output `[outE.symm (f (w, y))]` of `M_i`
on `Univ.input i w (y.map ρ)` within `β` (`Univ.input` unfolds to N4v's right-hand input; `Univ.M`
is an `abbrev`). F4' `OTM2OutputsInTime.bool_iff (tm := Univ.M i) (vEnum i).outE` then gives:
`M_i` outputs `[outE.symm true]` on `Univ.input i w (y.map ρ)` within `β` iff `true = f (w, y)`
iff `R w y` (by `hR (w, y)`, restated as `R w y ↔ f (w, y) = true` so that `rw` matches).

*Items 4–5.* `padFun_mem_iff` and `hLR w` reduce `L w ↔ padFun i c' d w ∈ univOracle` to

`(∃ y' : List (Fin g_i), |y'| ≤ |w|^{k_i} ∧ M_i outputs [outE.symm true] on Univ.input i w y'
within β) ↔ (∃ y : List Γ₁, |y| ≤ |w|^{k_i} ∧ R w y)`.

`→`: given `y'`, take `y := y'.map ρ.symm`; `|y| = |y'|` (`List.length_map`) and
`(y'.map ρ.symm).map ρ = y'` (`List.map_map`, `Equiv.self_comp_symm`, `List.map_id`), then
item 3. `←`: given `y`, take `y' := y.map ρ` and item 3.

Where each hypothesis is used: (c) of §5.7 is `h.outputsFun`, available for all `(w, y)` and
used only at `|y| ≤ |w|^{k_i}`; `k_i = k` compares the certificate bound of `Acc` with that of
`InNP`; `ρ` is a bijection so that lengths are preserved and the existential transports both
ways. Nothing is needed about `A` beyond (†) (`Univ.mem_univOracle`, inside `padFun_mem_iff`),
with `A = univOracle` on both sides, as §5.7 says; the budget enters only through
`eval_le_budget`, and `D_i` only through `padPoly`.

**A6.** `inP_of_pad_reduction`: `⟨g, hg, hgA⟩ := oracle_inP univOracle` (T3); the decider is
`g ∘ padFun i c' d` with the machine `oracleComp univOracle (Pad.padComputable i c' d) hg`
(F7 on A4; `eβ := (fin_encoding_string Bool).encode` on both sides of the composition, as A4
was stated for) and `L w ↔ padFun i c' d w ∈ A ↔ g (padFun i c' d w) = true`.
`inNP_subset_inP` composes it with A5; `univOracle_pEqNP L := ⟨inP_subset_inNP univOracle
Bool L, inNP_subset_inP L⟩` (T4 at `alphabet := Bool`; its `[Nontrivial Bool]` is Mathlib's
instance).

**T5, T6, T7.** `collapse := ⟨univOracle, univOracle_pEqNP⟩`;
`separation := ⟨sepOracle, sepOracle_not_pEqNP⟩`; `baker_gill_solovay := ⟨collapse, separation⟩`.

**The final results, read in plain language** (brief item 1b). The three statements, exactly as
they will appear in `Relativization/BakerGillSolovay.lean`:

```lean
theorem collapse : ∃ A : Oracle, PEqNP A
theorem separation : ∃ B : Oracle, ¬ PEqNP B
theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B)
```

*Hypotheses.* **None.** Each is a closed proposition: no variables, no instance arguments, no
section variables, no hypothesis on the oracles or on the languages, and (to be confirmed by
`#print axioms`, §13.5) no axiom beyond `propext`, `Classical.choice`, `Quot.sound`. The
witnesses are the explicit sets `univOracle` (D6, §4.11) and `sepOracle` (B4, §4.10). For the
record, the hypotheses of the intermediate results: A5 has `L : Language (List Bool)` and
`hL : InNP univOracle (fin_encoding_string Bool) L`; `inP_of_pad_reduction` has `L`, `i c' d`
and `∀ w, L w ↔ padFun i c' d w ∈ univOracle`; `inNP_subset_inP` has `L`; `univOracle_pEqNP`
has none.

*What the words mean*, unfolding `Relativization/Classes.lean` (D3) and `Oracle.lean` (D1, D2),
§2:

1. **Oracle.** `Oracle := Set (List Bool)`: an oracle is any set of finite binary strings, a
   classical set whose membership need not be decidable (`OracleFinTM2.step` reads the oracle's
   answer as a `Bool` through `Classical.propDecidable`).
2. **Oracle machine.** `OracleFinTM2` is Mathlib's `FinTM2` (a stack machine: a finite set `K`
   of stacks, stack `k` holding symbols of a type `Γ k`, finitely many labels `Λ`, finitely many
   internal states `σ`, an input stack `k₀` with finite alphabet, an output stack `k₁`) plus a
   query stack `kq` whose alphabet is in bijection with `Bool`, and a program
   `m : Λ → Bool → TM2.Stmt Γ Λ σ`. One step from a live configuration with label `l` reads the
   bit `b := decide (query c ∈ A)`, where `query c` is the content of the query stack, top first,
   read as bits, and executes the whole statement `m l b` (a finite tree of `push`, `pop`,
   `peek`, `load`, `branch`, ending in `goto` or `halt`). So the oracle is consulted at every
   step, at no cost, on the current query string; a halted configuration has no successor. The
   alphabets of the working stacks are arbitrary types, as in `FinTM2`.
3. **Running in time.** `OTM2OutputsInTime A tm l l' t`: iterating `tm.step A` from the initial
   configuration on `l` (label `main`, initial state, `l` on the input stack, every other stack
   empty) reaches, after some `s ≤ t` steps, the halting configuration with output `l'` (no
   label, initial state, `l'` on the output stack, every other stack empty). One step is one
   executed statement, however many symbols it pushes.
4. **Polynomial-time computable.** `OTM2ComputableInPolyTime A ea eb f`: a machine `tm`,
   bijections `tm.Γ tm.k₀ ≃ αΓ` and `tm.Γ tm.k₁ ≃ βΓ` between its input and output alphabets
   and the encoding alphabets, a polynomial `time : Polynomial ℕ` (natural coefficients), and
   for every `a` a run of `tm` with oracle `A` from `ea a` (transported to `tm`'s alphabet) to
   `eb (f a)` within `time.eval (ea a).length` steps.
5. **Encodings.** `fin_encoding_string Bool` is the identity encoding of binary strings
   (alphabet `Bool`, `encode := id`): a binary string is its own code, of length `|w|`.
   `finEncodingBoolBool` encodes `b : Bool` as the one-symbol string `[b]`.
   `pair_encoding (fin_encoding_string Bool) (fin_encoding_string Γ₁)` encodes a pair `(w, y)` as
   Cook's `w#y`: alphabet `Bool ⊕ Option Γ₁` (`{0,1} ⊔ {#} ⊔ Γ₁`), code
   `w.map inl ++ inr none :: y.map (inr ∘ some)`, of length `|w| + 1 + |y|`.
6. **`P^A`.** `InP A (fin_encoding_string Bool) L`: there are a function `f : List Bool → Bool`
   and a polynomial-time oracle machine (item 4) with oracle `A`, input alphabet `≃ Bool`,
   output alphabet `≃ Bool`, computing `f` on every binary string `w` within its polynomial of
   `|w|`, with `∀ w, L w ↔ f w = true`.
7. **`NP^A`.** `InNP A (fin_encoding_string Bool) L`: there are a finite certificate alphabet
   `Γ₁ : Type`, a relation `R : List Bool → List Γ₁ → Prop` and an exponent `k : ℕ` such that
   (i) the pair language `{(w, y) | R w y}` is in `P^A` under the pair encoding of item 5, i.e.
   a polynomial-time oracle machine with oracle `A` and input alphabet `≃ Bool ⊕ Option Γ₁`
   decides `R w y` on **every** `w#y` within its polynomial of `|w| + 1 + |y|`; and
   (ii) `∀ w, L w ↔ ∃ y : List Γ₁, |y| ≤ |w|^k ∧ R w y`.
8. **`PEqNP A`.** For every `L : Language (List Bool)`, i.e. every predicate `List Bool → Prop`
   on binary strings (every language, decidable or not; a language in neither class satisfies
   the biconditional vacuously), `InP A (fin_encoding_string Bool) L ↔ InNP A
   (fin_encoding_string Bool) L`.

So `collapse` says: *there is a set `A` of binary strings such that, for every language `L` of
binary strings, `L` is decided by a polynomial-time TM2 oracle machine with oracle `A` if and
only if `L` has a polynomially bounded certificate relation decided by a polynomial-time TM2
oracle machine with oracle `A`.* `separation` says: *there is a set `B` of binary strings and
a language `L` of binary strings for which that equivalence fails* (the proof exhibits
`L = sepLang B ∈ NP^B ∖ P^B`; the statement itself only says that the biconditional is not
true of every `L`). `baker_gill_solovay` is their conjunction, with the same `PEqNP` and the
same type `Oracle` in both conjuncts, so "`P^A = NP^A`" and "`P^B ≠ NP^B`" are one notion of
`P^X` and one of `NP^X` evaluated at two oracles.

*What makes the Lean statement weaker than, or different from, the textbook theorem.*

1. **Machine model.** `P^A` and `NP^A` are defined on Mathlib's `TM2` stack machines with the
   oracle read through a query stack and one oracle bit per step (PLAN §3, option H), not on
   multi-tape oracle Turing machines with a query tape and query state. The equivalence of
   the two relativized classes is a paper argument and is not formalised (PLAN §7, first
   risk). What **is** formalised is that at `A = ∅` the classes are exactly
   `Millennium.InPolynomialTime` and `Millennium.InNondeterministicPolynomialTime` (T1, T2,
   session 1), the definitions of `P` and `NP` in the LeanMillenniumPrizeProblems formulation
   of the Clay problem; the relativized definitions are those, word for word, with an oracle
   machine in place of a plain one (§2).
2. **Binary alphabet only.** `PEqNP A` quantifies over languages of binary strings. The Clay
   form `ClassEquality A` (every finite alphabet with at least two symbols) is T8, the stretch
   target, not done: `¬ ClassEquality B` would follow from `¬ PEqNP B` by taking
   `alphabet := Bool`, but `ClassEquality univOracle` needs the pad to encode symbols as bit
   blocks (PLAN §6.3).
3. **The collapse oracle is not PSPACE-complete.** `univOracle` is the self-referential oracle
   of D6; the textbook takes a PSPACE-complete `A`. The statement `∃ A, PEqNP A` does not say
   which `A` (PLAN §7, second risk), so it is the textbook statement; only the witness differs.
4. **Definition of `NP`.** The certificate bound is `|y| ≤ |w|^k` with `0^0 = 1`; the verifier
   must run in polynomial time on **all** pairs `w#y`, not only on short certificates; and the
   certificate relation `R` is an arbitrary `Prop`-valued relation that the `InP` clause
   requires to be decided (`R w y ↔ f (w, y) = true`). All three are inherited from
   `Millennium.InNondeterministicPolynomialTime` (PLAN §7, "certificate bound").
5. **"Polynomial time"** means at most `p(|input|)` steps for a polynomial `p` with natural
   coefficients, the input length being that of the encoded input (`|w|` for a string,
   `|w| + 1 + |y|` for a pair), one step executing one whole statement of the program (which
   may push several symbols; that is why the depth `D_i` appears in D6).
6. **Existence, not construction.** `∃ A` and `∃ B` are `Prop`-level existentials; the
   witnesses are explicit sets but `noncomputable` (they use the enumerations `vEnum`, `dEnum`
   of codes, which are `Classical.choose` of countability, and `sepOracle` chooses its free
   strings with `Classical.choose`). This is no weaker than the textbook, whose construction
   is also non-effective, but a reviewer should not expect to evaluate either oracle.
7. **`Type`, not `Type u`.** Alphabets, certificate alphabets and oracle machines live in
   `Type` (universe 0), as in `Millennium`; the languages are `List Bool → Prop`. No loss for
   the theorem, which concerns finite alphabets.

Nothing else differs: no hypothesis on the oracles, no restriction on the languages, no
`Decidable` or `Fintype` assumption beyond the finiteness of the certificate alphabet that
`Millennium` itself imposes, and no axiom beyond the three.

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

(Lemma 4 is F4 of the plan: `OTM2OutputsInTime.output_unique`, with the forms
`outputs_iff_eq` and `bool_iff` used in §5.7; stated in §4.6 and proved in session 2, §8.2.)

### 5.3 Codes (assumed here; N1–N4 of the plan)

The proof uses one fact about machines, stated in Lean form as N4v in §4.6 (session 2):

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

### 5.4 Definition of `A` (the chosen definition: decision D6, approved 2026-10-07)

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

### 5.8 The alternative with budget `T` (not used; D6 decided for §5.4)

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
Proposition 5 for every frame and the cleaner equation (†). **Decision D6 (approved 2026-10-07, session 2): the budget
`⌊(T ∸ μ)/(D_i + 1)⌋` of §5.4 is the chosen definition of `A`, recorded in PLAN §4.1. The
budget-`T` variant described in this subsection is not used.**

### 5.9 Not yet formal, and what could still go wrong

* (N) is proved: it is N4v (`exists_vcode`, session 2, §8.2), exact in time and for every
  oracle. `D_i` is the depth of the coded machine `(vEnum i).N.toOracleFinTM2`; no relation to
  `D(V)` is proved or needed.
* `pad` as a machine (A4) and the power bound `(n + c')^d` are not built.
* Lemma 4 (F4) is proved (session 2, §8.2).
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

---

## 8. Lemma table and checks (session 2, 2026-10-07)

### 8.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Halt.lean` | 103 (83) | F4: terminal halting configurations, unique output |
| `Relativization/Countable.lean` | 102 (84) | N1: `TM2.Stmt` over finite data is countable |
| `Relativization/Normal.lean` | 438 (374) | D4 `NFMachine`; the normal form `NF.nf`; N3a, N3b, N3c |
| `Relativization/Codes.lean` | 319 (263) | `DCode`, `VCode`; N2 (countability, `dEnum`, `vEnum`); N4d, N4d', N4v, N4v' |
| `Relativization.lean` | 32 (26) | imports (+4 lines) |
| **Session 2 total** | **962 (804) in the four new files; 815 non-blank with the root module** | |
| **Repository total** | **2,306 (1,945)** | 635 constants: 272 named, 363 auxiliary (session 2 audit classification, which counts `mk`/`injEq` as auxiliary and structure projections as named) |

Session 1 files are unchanged (byte for byte: no session 1 definition or proof was touched).

### 8.2 Results asked for in the session brief

All **proved**. Axioms are from the literal `#print axioms` output in §8.5.

| Id | Lean name | File:line | Statement | Differences from §4.6 as first written | Axioms |
|---|---|---|---|---|---|
| D4 | `NFMachine`, `NFMachine.toOracleFinTM2` | Normal:28, 53 | normal-form machines and their reading as oracle machines | `toOracleFinTM2` is an `abbrev` (see §8.4 item 3) | the three |
| N1 | `TM2.Stmt.countable` | Countable:97 | `Countable (TM2.Stmt Γ Λ σ)` for countable `K`, `Λ`, finite `σ`, finite `Γ k` | none (the plan's "countable `Γ k`" is false, §4.5 item 1) | the three |
| N2 | `NFMachine.countable`, `DCode.countable`, `VCode.countable` | Codes:60, 95, 140 | the three code types are countable | none | the three |
| N2 | `dEnum`, `dEnum_surjective`, `vEnum`, `vEnum_surjective` | Codes:268–278 | surjections `ℕ → DCode`, `ℕ → VCode` | none | the three |
| N3a | `NF.nf_outputs_iff` | Normal:364 | every machine: NF outputs `o` on `enc₀ l` within `t` iff `tm` outputs `o.map dec` on `l` within `t`, every oracle | `enc₀` (input alphabet) in place of `enc … tm.k₀` (§8.4 item 1) | the three |
| N3b | `exists_nf` | Normal:390 | `[Finite (tm.Γ tm.k₁)]`: ∃ NF and `e₀ : Fin (N.a N.k₀) ≃ tm.Γ tm.k₀`, `e₁ : … ≃ tm.Γ tm.k₁` with the same outputs in the same time, every oracle | none | the three |
| N3c | `exists_nf_equiv` | Normal:420 | the same through given alphabet equivalences `ι₀`, `ι₁` with `[Finite βΓ]` | none | the three |
| N4d | `exists_dcode` | Codes:149 | every polynomial-time oracle decider has a `DCode` with the same polynomial, same outputs in the same time under every oracle | none | the three |
| N4d' | `exists_dcode_decides` | Codes:161 | the code decides `f` under `A` within its own polynomial | none | the three |
| N4v | `exists_vcode` | Codes:285 | statement (N) of §5.3, with `i : ℕ`, `vEnum i` | `ι₀ : V.Γ V.k₀ ≃ pairΓ Γ₁` where `pairΓ Γ₁ := Bool ⊕ Option Γ₁` is the `pair_encoding` alphabet by `rfl` (`pair_encoding_Γ`) | the three |
| N4v' | `exists_vcode_of_verifier` | Codes:302 | the same for the verifier structure inside `InNP`, output written as `outputsFun` writes it | none; it is `exists_vcode` applied, by definitional unfolding | the three |
| F4 | `OracleFinTM2.step_haltList`, `OracleFinTM2.haltList_injective`, `OTM2OutputsInTime.output_unique` | Halt:26, 32, 65 | halting configurations are terminal; at most one output, reached at the same step, whatever the time bounds | none | the three |
| F4' | `OTM2OutputsInTime.outputs_iff_eq`, `OTM2OutputsInTime.bool_iff` | Halt:79, 90 | given one output, a candidate is an output iff equal to it | none | the three |

"The three" = `[propext, Classical.choice, Quot.sound]`.

### 8.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Halt | `OracleFinTM2.haltList_stk_self`, `iter_eq_some_of_terminal`, `OracleFinTM2.run_unique_aux` |
| Countable | `StmtCountable.Node`, `arity`, `arityFintype`, `arityEncodable`, `toW`, `ofW`, `ofW_toW`, `toW_injective` |
| Normal | `pushSyms`, `pushSyms_finite`; `NF.pushed`, `pushed_finite`, `symSet`, `mem_symSet_of_pushed`, `mem_symSet_k₀`, `mem_symSet_kq`, `mem_symSet_of_X`, `symSet_finite`, `κ`, `ℓ`, `ς`, `aFun`, `aFun_eq`, `ε`, `enc`, `dec`, `dec_mem`, `dec_enc`, `enc_dec`, `dec_injective`, `enc₀`, `dec_enc₀`, `qAlpha`, `pushSyms_subset_pushed`, `tr`, `nf`, `NCfg`, `eStk`, `eStk_update`, `eStk_injective`, `e`, `e_injective`, `stepAux_tr`, `query_e`, `step_e`, `iter_e`, `e_initList`, `e_haltList` |
| Codes | `equivCountable`, `polynomialNatCountable`; `NFMachine.Fiber`, `fiberCountable`, `Data`, `toData`, `ofData`, `ofData_toData`; `DCode.Data/toData/ofData/ofData_toData`; `pairΓ`, `pair_encoding_Γ`; `VCode.Data/toData/ofData/ofData_toData`; `pairMap`, `pairEquiv`, `pairMap_cert`, `pair_encode_map`, `exists_vcode_aux`; `d0`, `v0`, `DCode.nonempty`, `VCode.nonempty` |

### 8.4 Things a reviewer should know

1. **`NF.enc` is defined on the reachable symbols only.** §4.6 first wrote
   `NF.enc … (k) : tm.Γ k → Fin (…)`. That function cannot exist: a work stack may have a
   nonempty alphabet of which nothing is ever pushed, so its normal-form alphabet is `Fin 0` and
   there is no junk value to send unreachable symbols to. `NF.enc tm hX k : symSet tm X k → Fin …`
   takes a membership proof; the statement translation `NF.tr` carries the proof that every
   pushed symbol is reachable; `NF.enc₀` is the version on the whole input alphabet (which is
   reachable by definition of `symSet`). N3a is stated with `enc₀`. Nothing else in §4.6 changed.
2. **No session 1 definition was changed**, and none needed to be. The simulation map goes from
   the normal form to the original machine (§4.7), so no reachability invariant on
   configurations is needed, and `κ.symm (κ k)` never has to be rewritten: the only transport is
   `Fin.cast` of `a (κ k) = Nat.card (symSet k)`, and it only ever appears as
   `Fin.cast h (Fin.cast h.symm i) = i`.
3. **`NFMachine.toOracleFinTM2` is an `abbrev`.** With a plain `def`, terms such as
   `N.toOracleFinTM2.Γ N.toOracleFinTM2.k₀` and `Fin (N.a N.k₀)` are definitionally equal but
   not reducibly so, and `simp`/`rw` fail on `List.map`/`Option.map` whose implicit types differ
   that way (the same phenomenon as §7.4 item 7). Making the reading reducible removes it for
   everything downstream. The `OracleFinTM2.Cfg` of session 1 is left as it was.
4. **N1 needs finite alphabets**, not countable ones (§4.5 item 1). The proof writes a statement
   as a `WType` (`toW`), reads it back (`ofW`, a left inverse, so injectivity is `rfl`-level), and
   uses Mathlib's `Encodable (WType β)`; the node type is made `Encodable` by
   `Encodable.ofCountable` (classical).
5. **The time overhead is zero.** `OTM2OutputsInTime` transports with the same `steps`
   (`nf_outputs_iff` keeps `s`), so "within `t` steps" is preserved for every `t`, which is what
   (N) and the plan's N3 need. No polynomial overhead appears anywhere.
6. **Countability of the code data.** `NFMachine.Data` is a nested `Σ`; Lean's instance search
   for `Countable` of the whole nest exceeds the default `synthInstance.maxSize`, which is why
   the fiber `NFMachine.Fiber` has its own instance (`fiberCountable`): with it each search is
   small. No `set_option` is used.
7. **Global instances added:** `TM2.Stmt.countable` (N1), `equivCountable`
   (`Countable (α ≃ β)` from `Countable (α → β)`), `polynomialNatCountable`,
   `NFMachine.fiberCountable`, `NFMachine.countable`, `DCode.countable`, `VCode.countable`,
   `DCode.nonempty`, `VCode.nonempty`, and the two `Fintype`/`Encodable` instances on
   `StmtCountable.arity`. All are in namespace `Relativization`.
8. **`d0`, `v0`** are two trivial machines used only to show `DCode` and `VCode` are inhabited
   (needed by `exists_surjective_nat`). `v0`'s stack alphabets are `cond b (pairΓ (Fin 0)) Bool`
   so that no `Fin`-literal arithmetic has to reduce inside a type.
9. **Not done, by instruction:** no stage construction, no half of the main theorem, no `pad`
   machine, nothing of A1–A6 or B1–B6. `NFMachine.toOracleFinTM2.depth` is whatever it is; no
   relation to `tm.depth` is proved or needed (`D_i` in §5 is the depth of the coded machine).
10. **Local attributes.** One more `attribute [local instance]` line (Normal:96, the four
    `Fintype` fields of `OracleFinTM2`), as in session 1. No `@[reducible]` (the `abbrev`s are
    `NFMachine.toOracleFinTM2`, `NF.κ`/`ℓ`/`ς`, `NF.NCfg`, `StmtCountable.Node`,
    `NFMachine.Fiber`, the three `Data`s, `pairΓ`). No macros, syntax, elaborators, `deriving`,
    `set_option`, or `#eval`.

### 8.5 Check outputs

Full logs are in `logs/` (not committed): `session2-axioms-all.txt`, `session2-print-axioms.txt`,
`session2-build.txt`.

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`; the audit script is outside the repository). Last lines of
`logs/session2-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 635 (272 named, 363 auxiliary)
named in new modules (Halt, Countable, Normal, Codes): 129
UNION of axioms used: #[propext, Classical.choice, Quot.sound]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: #[]
```

**(b) Literal `#print axioms` on each of the 129 named declarations of the four new
modules** (`logs/session2-print-axioms.txt`, 129 output lines, 0 errors).
Distribution:

```
      1 depends on axioms: [Quot.sound]
     69 depends on axioms: [propext, Classical.choice, Quot.sound]
     21 depends on axioms: [propext, Quot.sound]
     38 does not depend on any axioms
```

`grep -c sorryAx` on both logs prints `0` and `0`. The results of §8.2:

```
'Relativization.NFMachine' does not depend on any axioms
'Relativization.NFMachine.toOracleFinTM2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.TM2.Stmt.countable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.NFMachine.countable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.DCode.countable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.VCode.countable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.dEnum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.dEnum_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.vEnum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.vEnum_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.NF.nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.NF.nf_outputs_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_nf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_nf_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_dcode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_dcode_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_vcode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_vcode_of_verifier' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.step_haltList' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.haltList_injective' depends on axioms: [propext, Quot.sound]
'Relativization.OTM2OutputsInTime.output_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2OutputsInTime.outputs_iff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2OutputsInTime.bool_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.DCode' depends on axioms: [propext, Quot.sound]
'Relativization.VCode' does not depend on any axioms
```

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`, the same three
scans as §7.5 (c):

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
Relativization/Comp.lean:27:attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
Relativization/Comp.lean:39:@[reducible] def CΓ : CK M₁ M₂ → Type
Relativization/Normal.lean:96:attribute [local instance] OracleFinTM2.kFin OracleFinTM2.ΛFin OracleFinTM2.σFin
Relativization/Oracle.lean:261:attribute [local instance] OracleFinTM2.ΛFin
Relativization/Plain.lean:23:attribute [local instance] FinTM2.kFin
Relativization/Plain.lean:28:@[reducible] def PΓ : Option M.K → Type
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

The five session 1 hits are unchanged; the one new hit is the local attribute of §8.4 item 10.

**(d) `lake build`**, after deleting this project's own build artifacts so that every module was
recompiled (`logs/session2-build.txt`; `grep -c -i -E "warning|error"` on it prints
`0`):

```
✔ [1235/1245] Built Relativization.Countable (11s)
✔ [1236/1245] Built Relativization.Oracle (12s)
✔ [1237/1245] Built Relativization.Classes (12s)
✔ [1238/1245] Built Relativization.Halt (12s)
✔ [1239/1245] Built Relativization.Normal (12s)
✔ [1240/1245] Built Relativization.Self (11s)
✔ [1241/1245] Built Relativization.Plain (11s)
✔ [1242/1245] Built Relativization.Comp (11s)
✔ [1243/1245] Built Relativization.Codes (11s)
✔ [1244/1245] Built Relativization (8.2s)
Build completed successfully (1245 jobs).
exit: 0
```

`lake env leanchecker --fresh` was not run this session (it is an acceptance check for T7).

---

## 9. Lemma table and checks (session 3, 2026-10-07)

### 9.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Prog.lean` | 1,074 (920) | `Prog` from PvsNP `c271016`, verbatim body (lines 40–968, 800 non-blank) under a new header (30) and namespace; section "Oracle machines" (969–1073, 89): O1 `ORun`, O2 `step_live`/`step_eq_plain`/`ORun.of_run`, O3 `ORun.of_run_visited`, O5 `TM2OutputsInTime.ofRun`/`OTM2OutputsInTime.ofORun` |
| `Relativization/Emb.lean` | 238 (207) | `Emb` from PvsNP, verbatim body (28–176, 133 non-blank) minus its `iter_none`, under a new header (20); section "Oracle hosts" (177–237, 53): O4 `OEmbeds`, `run_embed_oracle` |
| `Relativization/Sep.lean` | 198 (168) | B1 `Sep.revTM`, `Sep.revComputable` (1–169); `sepLang`, B2 `sepLang_inNP`, `sepLang_replicate_iff` (171–197) |
| `Relativization.lean` | 44 (36) | imports (+12 lines) |
| **Session 3 total** | **1,510 (1,295) in the three new files; 1,305 non-blank with the root module: 933 verbatim, 372 new** | |
| **Repository total** | **3,828 (3,250)** | 928 constants: 407 named, 521 auxiliary (same classification as session 2: 272 + 135 = 407) |

Session 1 and 2 files are unchanged (byte for byte; the `.olean`s of all nine earlier modules
are identical before and after the from-scratch rebuild, §9.5 (e)). `D:\PvsNP` is unchanged
(`git -C D:\PvsNP status` was not needed: nothing there was opened for writing).

### 9.2 Results asked for in the session brief

All **proved**. Axioms are from the literal `#print axioms` output in §9.5.

| Id | Lean name | File:line | Statement | Differences from §4.8/§4.9 as first written | Axioms |
|---|---|---|---|---|---|
| copy | `Relativization.Prog.*` (93 named declarations) | Prog:40–968 | PvsNP `Prog` verbatim | none (`logs/session3-port-diff.txt`: only the `namespace`/`end` lines differ) | all within the three |
| copy | `Relativization.Emb.*` (14 named declarations of the copy) | Emb:28–176 | PvsNP `Emb` verbatim | `iter_none` dropped (§4.8, E6) | all within the three |
| O1 | `Prog.ORun`, `ORun.zero/head/trans/of_eq` | Prog:981–1001 | oracle run, sequencing | none | the three |
| O2 | `OracleFinTM2.step_live`, `OracleFinTM2.step_eq_plain`, `Prog.ORun.of_run` | Prog:1004, 1012, 1020 | one oracle step at a live label; oblivious label ⇒ plain step; all labels oblivious ⇒ plain run is oracle run | declared in namespace `OracleFinTM2` (via `_root_`) rather than `Prog` | the three |
| O3 | `Prog.ORun.of_run_visited` | Prog:1032 | labels visited before the last step oblivious ⇒ plain run is oracle run | the visited-label condition is written as "every configuration reached in `j < n` plain steps has an oblivious label", not as the disjunction of §4.8 (same content, usable form) | the three |
| O5 | `Turing.TM2OutputsInTime.ofRun`, `Relativization.OTM2OutputsInTime.ofORun` | Prog:1060, 1066 | run from `initList` to `haltList` in `n ≤ t` steps ⇒ output within `t` | none; computable (no `Classical.choose`, unlike PvsNP's `outputsOfRunLe`) | `[propext, Quot.sound]`; the three |
| O4 | `Emb.OEmbeds`, `Emb.run_embed_oracle` | Emb:186, 193 | oracle host ignoring the answer on the image of `φ`; `run_embed` for it | none | the three |
| B1 | `Sep.revTM`, `Sep.revComputable` | Sep:50, 148 | `(w, y) ↦ (w ++ y).reverse` is `TM2ComputableInPolyTime` on `pair_encoding (fes Bool) (fes Bool)` → `fes Bool`, time `X + 1` | none | the three |
| B2 | `sepLang`, `sepLang_inNP` | Sep:173, 177 | `sepLang B ∈ NP^B` for every `B`; `sepLang` verbatim from PLAN §4.2 | none | `sepLang`: none; `sepLang_inNP`: the three |
| for B6 | `sepLang_replicate_iff` | Sep:189 | `0^n ∈ sepLang B ↔ ∃ u, |u| ≤ n ∧ u ++ 0^n ∈ B` | none | `[propext]` |

"The three" = `[propext, Classical.choice, Quot.sound]`.

### 9.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Prog (copy) | `Flag`, `instFlagBool`, `Run`, `Run.zero/head/trans/of_eq/single`, `cnt`, `cnt_length/succ/zero/add/injective`, `incr`, `decr`, `incr_run`, `incr_run_cnt`, `decr_run_pos/cnt/zero`, `pushAll`, `addU`, `addU_zero/addU/of_not_mem/update`, `stepAux_pushAll`, `xfer`, `xfer_run`, `addU_single_self/ne`, `single_nodupKeys`, `compare_succ_succ`, `cmpStep`, `cmpLoop_run`, `cmp_run`, `sumFrom`, `sumFrom_const/le`, `forHead`, `forLoop_run`, `pushList`, `stepAux_pushList`, `emit`, `emit_run`, `pair_nodupKeys`, `addU_pair_fst/snd/ne`, `copy_run`, `add_run`, `mul_run`, `rep`, `rep_zero/succ/succ'/add`, `emitR`, `emitR_run`, `xferE`, `xferE_run`, `emitDiff_run`, `Reach`, `Run.reach`, `Reach.refl/of_eq/trans`, `forLoop_reach`, `RunLe`, `Bud`, `Run.le`, `RunLe.reach/mono/refl/trans`, `Bud.start`, `Run.bud`, `RunLe.bud`, `Bud.fin`, `forLoop_le` (and the auto-generated `Run.congr_simp`, `addU.congr_simp`) |
| Emb (copy) | `SEmb`, `mapS`, `Embeds`, `Agree`, `Frame`, `Frame.refl/trans/update`, `Agree.update`, `stepAux_mapS`, `run_embed`, `runLe_embed` |
| Sep | `RΓ`, `Rσ`, `sym`, `hasBit`, `bitOf`, `prog`, `mk`, `update_mk_false/true`, `bits`, `bits_cons`, `bits_encode`, `step_nil`, `step_cons`, `loop_run`, `initList_eq`, `haltList_eq`, `revTM_run` |

### 9.4 Things a reviewer should know

1. **Global instance added: `Relativization.Prog.instFlagBool : Flag Bool`** (verbatim from
   PvsNP, Prog:47). Also global simp attributes on new lemmas: `Flag.untag_tag` (Prog:49),
   `cnt_length` (93), `cnt_zero` (98), `rep_zero` (656). `Flag`, `cnt`, `rep` are new, so no
   earlier declaration can mention them; and no earlier module imports a new one. Confirmed by
   the from-scratch rebuild: the `.olean` of every session 1 and 2 module has the same SHA-256
   before and after (§9.5 (e)). No other instance was added (`OEmbeds`, `ORun` are plain
   definitions).
2. **Verbatim means verbatim.** `logs/session3-port-diff.txt` is `diff` of the bodies
   (`namespace … end`): for `Prog` the only differing lines are the two namespace lines (plus one
   blank line added after `open`); for `Emb` the namespace/`open` lines and the removed
   `iter_none`. The appended oracle sections are the `a`/`c` hunks at the end.
3. **`Prog` stays a library for plain programs** (NOTES §4.8, "What is not adapted"). The
   oracle layer is five lemmas and two packaging definitions. `ORun.of_run_visited` takes the
   visited-label condition on the *plain* run, so a caller who knows which labels a `Prog`-built
   block visits can transfer it into an oracle machine that reads the oracle elsewhere;
   `run_embed_oracle` does this for a whole embedded sub-machine (the host may read the oracle at
   any label outside the image of `φ`, and at the images of the sub-machine's halting labels).
4. **`step_live`, `step_eq_plain` live in `OracleFinTM2`**, `ofRun` in `Turing.TM2OutputsInTime`,
   `ofORun` in `Relativization.OTM2OutputsInTime` (declared with `_root_` from inside
   `Relativization.Prog`). They are stated over the raw `TM2.Cfg tm.Γ tm.Λ tm.σ` for the reason of
   §7.4 item 7; `ORun` itself is over `tm.Cfg`.
5. **`Sep.revTM`:** `K = Bool` (input `false`, output `true`), `Λ = Unit`, `σ = Option (Bool ⊕
   Option Bool)` (the symbol just popped; `none` initially and at the halt, so the halting
   configuration is `haltList`). One step per input symbol plus one halting step: `|w#y| + 1`.
   `RΓ` is an `abbrev` by `match` on `Bool`; `Γk₀Fin` is given explicitly with `inferInstanceAs`.
   The machine does not use the `Prog` counter primitives (PLAN §6.9 item 10); it uses `Run`,
   `Run.head`, `Run.zero`, `Run.of_eq` and `TM2OutputsInTime.ofRun`.
6. **Hidden implicit types again** (the phenomenon of §7.4 item 7 and §8.4 item 3): in
   `sepLang_inNP`, `y.length ≤ w.length` with `w : List Bool` and
   `y.length ≤ ((fin_encoding_string Bool).encode w).length ^ 1` print the same after `simp`, but
   the second `List.length` is at `List (fin_encoding_string Bool).Γ`; `simpa` fails and
   `rw [pow_one]; exact hy` succeeds (definitional at default transparency). In `revComputable`
   the input/output lists are matched by `List.map_id _` through the same defeq, as in T3.
7. **Audit classification.** The whole-environment audit classifies a constant as auxiliary when
   a name component is `mk`, so `Sep.mk` (the stack builder) is not in the `#print axioms` file;
   its line in the all-constants log is `Relativization.Sep Relativization.Sep.mk #[]`.
8. **Not done, by instruction:** no stage construction (B3–B6), nothing of A1–A6, T5–T8. Not
   duplicated for oracle machines: `RunLe`, `Bud`, `Reach`, `forLoop_le/reach`, `runLe_embed`
   (not needed by the plan).
9. **Local attributes, syntax.** No new `attribute [local instance]`, no `@[reducible]` (the new
   `abbrev`s are `RΓ`, `Rσ`). `Prog` and `Emb` use `omit [inst] in` (core syntax to drop an
   unused section instance). No macros, `syntax`, elaborators, `deriving`, `set_option`, `#eval`.

### 9.5 Check outputs

Full logs are in `logs/`: `session3-axioms-all.txt`, `session3-print-axioms.txt`,
`session3-build.txt`, `session3-scan.txt`, `session3-port-diff.txt`,
`session3-olean-before.txt`, `session3-olean-after.txt`. The audit scripts are outside the
repository.

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`, as in sessions 1 and 2). Last lines of `logs/session3-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 928 (407 named, 521 auxiliary)
named in new modules (Prog, Emb, Sep): 135
UNION of axioms used: #[propext, Classical.choice, Quot.sound]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: #[]
```

Per module: 192 constants in `Prog`, 53 in `Emb`, 48 in `Sep` (`grep -c "^Relativization.Prog "`
etc. on the log).

**(b) Literal `#print axioms` on each of the 135 named declarations of the three new
modules** (`logs/session3-print-axioms.txt`, 135 output lines, 0 errors). Distribution
(`sed -E "s/^'[^']*' //" | sort | uniq -c`; the `rep_succ'` line sorts apart because of the
quote in its name and is a `[propext]` line):

```
      1 'Relativization.Prog.rep_succ'' depends on axioms: [propext]
      6 depends on axioms: [Quot.sound]
     35 depends on axioms: [propext, Classical.choice, Quot.sound]
     20 depends on axioms: [propext, Quot.sound]
     21 depends on axioms: [propext]
     52 does not depend on any axioms
```

`grep -c sorryAx` on both logs prints `0` and `0`. The results of §9.2:

```
'Relativization.Prog.Run' does not depend on any axioms
'Relativization.Prog.instFlagBool' does not depend on any axioms
'Relativization.Prog.xfer_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Prog.forLoop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Prog.mul_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Prog.emitDiff_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Emb.stepAux_mapS' depends on axioms: [propext, Quot.sound]
'Relativization.Emb.run_embed' depends on axioms: [propext, Quot.sound]
'Relativization.Prog.ORun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.step_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.step_eq_plain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Prog.ORun.of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Prog.ORun.of_run_visited' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.TM2OutputsInTime.ofRun' depends on axioms: [propext, Quot.sound]
'Relativization.OTM2OutputsInTime.ofORun' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Emb.OEmbeds' depends on axioms: [propext, Quot.sound]
'Relativization.Emb.run_embed_oracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Sep.revTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Sep.loop_run' depends on axioms: [propext, Quot.sound]
'Relativization.Sep.revTM_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Sep.revComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.sepLang' does not depend on any axioms
'Relativization.sepLang_inNP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.sepLang_replicate_iff' depends on axioms: [propext]
```

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`, the same three
scans as §7.5 (c) (`logs/session3-scan.txt`):

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
Relativization/Comp.lean:27:attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
Relativization/Comp.lean:39:@[reducible] def CΓ : CK M₁ M₂ → Type
Relativization/Normal.lean:96:attribute [local instance] OracleFinTM2.kFin OracleFinTM2.ΛFin OracleFinTM2.σFin
Relativization/Oracle.lean:261:attribute [local instance] OracleFinTM2.ΛFin
Relativization/Plain.lean:23:attribute [local instance] FinTM2.kFin
Relativization/Plain.lean:28:@[reducible] def PΓ : Option M.K → Type
Relativization/Prog.lean:49:attribute [simp] Flag.untag_tag
Relativization/Prog.lean:93:@[simp] theorem cnt_length {α : Type} (u : α) (n : ℕ) : (cnt u n).length = n :=
Relativization/Prog.lean:98:@[simp] theorem cnt_zero {α : Type} (u : α) : cnt u 0 = [] := rfl
Relativization/Prog.lean:656:@[simp] theorem rep_zero {α : Type} (ys : List α) : rep ys 0 = [] := rfl
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

The six session 1–2 hits are unchanged; the four new hits are the simp attributes of §9.4
item 1 (verbatim from PvsNP). The scan does not match `instance : Flag Bool` (no `@[instance]`
attribute); it is reported in §9.4 item 1.

**(d) `lake build`**, after deleting this project's own build artifacts
(`.lake/build/lib/lean/Relativization*`, `.lake/build/ir/Relativization*`) so that every module
was recompiled (`logs/session3-build.txt`; `grep -c -i -E "warning|error"` on it prints `0`):

```
✔ [1237/1250] Built Relativization.Countable (10s)
✔ [1238/1250] Built Relativization.Oracle (10s)
✔ [1239/1250] Built Relativization.Classes (13s)
✔ [1240/1250] Built Relativization.Halt (13s)
✔ [1241/1250] Built Relativization.Normal (13s)
✔ [1242/1250] Built Relativization.Prog (13s)
✔ [1243/1250] Built Relativization.Plain (11s)
✔ [1244/1250] Built Relativization.Emb (11s)
✔ [1245/1250] Built Relativization.Self (12s)
✔ [1246/1250] Built Relativization.Codes (12s)
✔ [1247/1250] Built Relativization.Comp (12s)
✔ [1248/1250] Built Relativization.Sep (8.4s)
✔ [1249/1250] Built Relativization (8.2s)
Build completed successfully (1250 jobs).
exit: 0
```

**(e) Earlier modules elaborate unchanged.** SHA-256 of each session 1–2 `.olean` before any
change of this session (`logs/session3-olean-before.txt`) and after the from-scratch rebuild
with the new modules present (`logs/session3-olean-after.txt`):

```
== olean hashes: earlier modules, before vs after the from-scratch rebuild ==
Classes.olean: identical (43f4554b909236c7)
Codes.olean: identical (c5e2c117e4ebe67f)
Comp.olean: identical (c560c3c025efabec)
Countable.olean: identical (d4012351737c0774)
Halt.olean: identical (bbec64145c811dcf)
Normal.olean: identical (292ec4f641ebb808)
Oracle.olean: identical (aba34f40f7e4fc08)
Plain.olean: identical (538a20892c70be80)
Self.olean: identical (2a154bef41f53627)
```

`lake env leanchecker --fresh` was not run this session (it is an acceptance check for T7).

---

## 10. Lemma table and checks (session 4, 2026-10-07)

### 10.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Count.lean` | 86 (72) | B3: `padded`, `card_padded`, `exists_free` (B3a); `eval_le_eval_one_mul_pow`, `mul_pow_lt_two_pow`, `eventually_eval_lt_two_pow`, `exists_len` (B3b) |
| `Relativization/Queries.lean` | 82 (66) | the query set of a run: `queryAt`, `queries`, `card_queries_le`, `query_mem_queries`, `length_le_of_mem_queries` (L3), `iter_congr_queries` (L4'), `outputsInTime_congr_queries` (L6') |
| `Relativization/Stage.lean` | 308 (244) | `DCode.input` (1–35); B4: the stage `Stage.len/tim/Q/free/str/acc/step/st`, the per-stage data, `sepOracle`, invariants (36–210); B5: `agree_on_queries`, `outputs_iff` (211–240); B6: `length_lt_or_lt_of_accAt`, `strAt_mem_sepOracle`, `sepLang_not_inP`, `sepOracle_not_pEqNP` (241–308) |
| `Relativization.lean` | 56 (46) | imports (+12 lines) |
| **Session 4 total** | **476 (382) in the three new files; 392 non-blank with the root module** | |
| **Repository total** | **4,316 (3,642)** | 1,033 constants: 470 named, 563 auxiliary (same classification as sessions 2 and 3: 407 + 63 = 470) |

Session 1–3 files are unchanged (byte for byte; the `.olean` of each of the twelve earlier
modules has the same SHA-256 before any change of this session and after the from-scratch
rebuild, §10.5 (e)). `D:\PvsNP` was not opened.

### 10.2 Results asked for in the session brief

All **proved**. Axioms are from the literal `#print axioms` output in §10.5.

| Id | Lean name | File:line | Statement | Differences from §4.10 as first written | Axioms |
|---|---|---|---|---|---|
| B3a | `exists_free` | Count:30 | `S.card < 2^n → ∃ u, |u| = n ∧ u ++ 0^n ∉ S` | none | the three |
| B3b | `eventually_eval_lt_two_pow`, `exists_len` | Count:76, 82 | every `p : Polynomial ℕ` is eventually below `2^n`; `∃ n > ℓ, p.eval n < 2^n` | none | the three |
| L4' | `OracleFinTM2.iter_congr_queries` | Queries:60 | oracles agreeing on `tm.queries A l t` give the same run for every `n ≤ t` | none | the three |
| L6' | `OracleFinTM2.outputsInTime_congr_queries` | Queries:68 | the same for `Nonempty (OTM2OutputsInTime …)` within `t` | none | the three |
| B4 | `Stage.st`, `Stage.step`, `sepOracle` | Stage:102, 97, 133 | the stage states by primitive recursion from `(0, ∅)`; `B = {z | ∃ i, z ∈ F_i}` | none | the three |
| B4 | `Stage.boundAt_lt_lenAt`, `Stage.lenAt_lt_boundAt_succ`, `Stage.boundAt_mono` | Stage:152, 158, 164 | `bound_i < n_i < bound_{i+1}`; the bounds are monotone | none | the three |
| B4 | `Stage.strAt_not_mem_Q` | Stage:171 | the added string was unqueried | none | the three |
| B4 | `Stage.mem_sepOracle` | Stage:196 | `z ∈ B ↔ ∃ j, ¬ acc_j ∧ z = x_j` | none | the three |
| B4 | `Stage.mem_oracleAt_of_length_le` | Stage:201 | `z ∈ B`, `|z| ≤ bound_i` ⇒ `z ∈ F_i` (the finite oracle is final below its bound) | none | the three |
| B5 | `Stage.agree_on_queries`, `Stage.outputs_iff` | Stage:216, 234 | `F_i` and `B` agree on `Q_i`; the stage-`i` run under `F_i` has the same outputs within `t_i` steps as under `B` | none | the three |
| B6 | `sepLang_not_inP` | Stage:269 | `¬ InP sepOracle (fes Bool) (sepLang sepOracle)` | none | the three |
| B6 | `sepOracle_not_pEqNP` | Stage:305 | `¬ PEqNP sepOracle` | none | the three |

"The three" = `[propext, Classical.choice, Quot.sound]`.

No plan statement turned out false or too weak (§4.10 records the assessment of each: B3 and
B5 are used in a form implied by the plan's; B4's three invariants are the three named rows;
B6 is proved without its `∃ B` wrapper). No session 1–3 definition was changed, and no
hypothesis beyond the statements of §4.10 was needed.

### 10.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Count | `padded`, `card_padded`, `eval_le_eval_one_mul_pow`, `mul_pow_lt_two_pow` |
| Queries | `OracleFinTM2.queryAt`, `queries`, `card_queries_le`, `query_mem_queries`, `length_le_of_mem_queries` |
| Stage | `DCode.input`, `DCode.input_length`; `Stage.State` (fields `bound`, `F`), `M`, `len`, `bound_lt_len`, `eval_len_lt`, `tim`, `Q`, `card_Q_lt`, `free`, `free_length`, `str`, `str_not_mem_Q`, `str_length`, `acc`; `boundAt`, `oracleAt`, `lenAt`, `timeAt`, `strAt`, `accAt`, `inputAt`; `st_succ`, `boundAt_succ`, `oracleAt_zero`, `mem_oracleAt_succ`, `inputAt_length`, `timeAt_lt`, `strAt_length`, `mem_oracleAt`, `oracleAt_subset_sepOracle`, `length_lt_or_lt_of_accAt`, `strAt_mem_sepOracle` |

### 10.4 Things a reviewer should know

1. **Which locality lemma the stages use, and why not L5/L6.** Each stage uses L4
   (`OracleFinTM2.iter_congr`, session 1, the sharp form) through `iter_congr_queries`, with
   `tm := (dEnum i).N.toOracleFinTM2`, `A := F_i`, `A' := sepOracle`, `l := 0^{n_i}` as the code
   reads it, `t := t_i`. The length form L5/L6 is not strong enough on its own: `B ∖ F_i` may
   contain the stage's own string `x_i = u_i ++ 0^{n_i}`, of length `2 n_i`, which is within
   the L5 bound `n_i + t_i · D_i` whenever `t_i · D_i ≥ n_i`. The run is stable because `x_i`
   was chosen outside the query set `Q_i`, which only L4 can use. Strings of later stages are
   handled by length (L3, `length_le_of_mem_queries`), as the plan had it. No definition was
   changed for this; §7.4 item 3 had already noted that the collapse half needs L4 too.
2. **`queries` is a superset.** `queryAt` returns `[]` once the run has stopped, so
   `tm.queries A l t` may contain `[]` even if it was never asked. Only an upper bound on its
   size and the membership of every query actually asked are used, so this is harmless and
   avoids `Option`-valued bookkeeping.
3. **`B` is a primitive recursion, not a fixpoint.** `Stage.st (i+1) = Stage.step i (Stage.st i)`
   holds by `rfl`; the two `Classical.choose`s inside `step` are on `exists_len` and
   `exists_free`, whose hypothesis `(Q i s).card < 2 ^ len i s` is proved inside the definition
   (`card_Q_lt`). The decision `acc i s` is a `Prop` used in a set-builder
   (`s.F ∪ {z | ¬ acc i s ∧ z = str i s}`), so no `Decidable` instance and no `if` is needed.
   `sepOracle` is a plain `def` (its body is a `Prop`-valued predicate).
4. **Shorthands.** `boundAt`, `oracleAt`, `lenAt`, `timeAt`, `strAt`, `accAt`, `inputAt` are
   `def`s unfolding to the fields of `st i`; the equations `boundAt_succ`, `mem_oracleAt_succ`,
   `st_succ`, `oracleAt_zero` are `rfl`/`Iff.rfl`. All arithmetic in the invariants is `omega`
   over these atoms (the product `timeAt i * (M i).depth` is treated as an atom).
5. **Elaboration note.** `hB.bool_iff (dEnum i).outE b` fails to elaborate: the alphabet
   equivalence is elaborated before the machine is known, its expected type
   `?tm.Γ ?tm.k₁ ≃ ?βΓ` is stuck, and the postponed argument's synthetic metavariable can no
   longer be assigned by unification. Naming the machine,
   `OTM2OutputsInTime.bool_iff (tm := Stage.M i) (dEnum i).outE hB b`, fixes it.
6. **`Stage.M` is a `noncomputable abbrev`** (it mentions `dEnum`); as an abbrev, its `Γ`/`k₁`
   projections reduce under `whnfR`, so the hidden-implicit-type problem of §7.4 item 7 does
   not arise anywhere in this session.
7. **Global instances: none added.** No `instance`, no `attribute`, no `@[simp]`, no
   `@[reducible]`, no `set_option`, no macros, syntax, elaborators, `deriving`, or `#eval`.
   The new `abbrev` is `Stage.M`; `Stage.State` is a plain structure.
8. **T6 not stated**, by instruction (final assembly). It is
   `⟨sepOracle, sepOracle_not_pEqNP⟩`, one line, to be written with T5–T8.
9. **Not done, by instruction:** A1–A6, T5–T8.

### 10.5 Check outputs

Full logs are in `logs/`: `session4-axioms-all.txt`, `session4-print-axioms.txt`,
`session4-build.txt`, `session4-scan.txt`, `session4-olean-before.txt`,
`session4-olean-after.txt`. The audit scripts are outside the repository (scratchpad).

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`, as in sessions 1–3). Last lines of `logs/session4-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 1033 (470 named, 563 auxiliary)
named in new modules (Count, Queries, Stage): 63
UNION of axioms used: #[propext, Classical.choice, Quot.sound]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: #[]
```

Per module: 14 constants in `Count`, 10 in `Queries`, 81 in `Stage`
(`grep -c "^Relativization.Count "` etc. on the log).

**(b) Literal `#print axioms` on each of the 63 named declarations of the three new
modules** (`logs/session4-print-axioms.txt`, 63 output lines, 0 errors). Distribution
(`sed -E "s/^'[^']*' //" | sort | uniq -c`):

```
     58 depends on axioms: [propext, Classical.choice, Quot.sound]
      2 depends on axioms: [propext, Quot.sound]
      3 does not depend on any axioms
```

`grep -c sorryAx` on both logs prints `0` and `0`. The results of §10.2:

```
'Relativization.exists_free' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.eventually_eval_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_len' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.iter_congr_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OracleFinTM2.outputsInTime_congr_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.st' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.sepOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.boundAt_lt_lenAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.lenAt_lt_boundAt_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.boundAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.strAt_not_mem_Q' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.mem_sepOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.mem_oracleAt_of_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.agree_on_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Stage.outputs_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.sepLang_not_inP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.sepOracle_not_pEqNP' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(The three axiom-free lines are `Stage.State` and its two projections; the two
`[propext, Quot.sound]` lines are `DCode.input` and `DCode.input_length`.)

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`, the same three
scans as §7.5 (c) (`logs/session4-scan.txt`):

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
Relativization/Comp.lean:27:attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
Relativization/Comp.lean:39:@[reducible] def CΓ : CK M₁ M₂ → Type
Relativization/Normal.lean:96:attribute [local instance] OracleFinTM2.kFin OracleFinTM2.ΛFin OracleFinTM2.σFin
Relativization/Oracle.lean:261:attribute [local instance] OracleFinTM2.ΛFin
Relativization/Plain.lean:23:attribute [local instance] FinTM2.kFin
Relativization/Plain.lean:28:@[reducible] def PΓ : Option M.K → Type
Relativization/Prog.lean:49:attribute [simp] Flag.untag_tag
Relativization/Prog.lean:93:@[simp] theorem cnt_length {α : Type} (u : α) (n : ℕ) : (cnt u n).length = n :=
Relativization/Prog.lean:98:@[simp] theorem cnt_zero {α : Type} (u : α) : cnt u 0 = [] := rfl
Relativization/Prog.lean:656:@[simp] theorem rep_zero {α : Type} (ys : List α) : rep ys 0 = [] := rfl
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

The ten hits are exactly those of §9.5 (c); the three new files contribute none.

**(d) `lake build`**, after deleting this project's own build artifacts
(`.lake/build/lib/lean/Relativization*`, `.lake/build/ir/Relativization*`) so that every module
was recompiled (`logs/session4-build.txt`; `grep -c -i -E "warning|error"` on it prints `0`):

```
✔ [1320/1336] Built Relativization.Countable (9.5s)
✔ [1321/1336] Built Relativization.Count (10s)
✔ [1322/1336] Built Relativization.Oracle (10s)
✔ [1323/1336] Built Relativization.Classes (12s)
✔ [1324/1336] Built Relativization.Halt (12s)
✔ [1325/1336] Built Relativization.Queries (12s)
✔ [1326/1336] Built Relativization.Normal (12s)
✔ [1327/1336] Built Relativization.Prog (12s)
✔ [1328/1336] Built Relativization.Self (11s)
✔ [1329/1336] Built Relativization.Codes (12s)
✔ [1330/1336] Built Relativization.Emb (11s)
✔ [1331/1336] Built Relativization.Plain (12s)
✔ [1332/1336] Built Relativization.Comp (12s)
✔ [1333/1336] Built Relativization.Sep (8.2s)
✔ [1334/1336] Built Relativization.Stage (8.4s)
✔ [1335/1336] Built Relativization (8.1s)
Build completed successfully (1336 jobs).
exit: 0
```

**(e) Earlier modules elaborate unchanged.** SHA-256 of each session 1–3 `.olean` before any
change of this session (`logs/session4-olean-before.txt`) and after the from-scratch rebuild
with the new modules present (`logs/session4-olean-after.txt`):

```
== olean hashes: earlier modules, before vs after the from-scratch rebuild ==
Classes.olean SAME 43f4554b909236c7463f66a59da5add30adb3f4084b8e48de414a2381efe3896
Codes.olean SAME c5e2c117e4ebe67f687ef83b1d8d2573830c2ad11aeb4b589ea22c352fd1bb8e
Comp.olean SAME c560c3c025efabecdee7f093bf9946eaf00f2e9cfa03fd52ce3836bea892daf8
Countable.olean SAME d4012351737c0774a51826920bd5e637f07d5c135cc3b929966dc5d08aa6e351
Emb.olean SAME 7203cedb57039239eb3735ee203b3d00d4b141f5e6974c8f1bbda90077a0b42f
Halt.olean SAME bbec64145c811dcfdf6c5f1be0683a461b4c9478cf354a31201ecda23db125b5
Normal.olean SAME 292ec4f641ebb808ff8e37075405b7dea60e9f5ae22bf307e2a8b327de47c0a3
Oracle.olean SAME aba34f40f7e4fc0812b4a80bc0a42d472770e255cd15ff572793f04a5f8751da
Plain.olean SAME 538a20892c70be803e666d35140c75b811aca5ba27aa95032ef8ac94dc690561
Prog.olean SAME 9f91d8f0624f08e0a079ce2712a2bd5ec7f5d67053fa115d27386cc3a7b3ff7b
Self.olean SAME 2a154bef41f5362745a35ac188e0624a5afe435ffd3a9df2bad3f959aa019753
Sep.olean SAME b004c415b234932d33d7025328c104416eb924f01af127fc757bbe872dc72280
```

(These twelve values are also the twelve of `logs/session3-olean-after.txt`.)

`lake env leanchecker --fresh` was not run this session (it is an acceptance check for T7).

## 11. Lemma table and checks (session 5, 2026-10-08)

### 11.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Frame.lean` | 102 (85) | A1: `frame`, `frame_length`, `ones`, `dropOnes`, `decode`, `decode_frame`, `eq_frame_of_decode`, `decode_eq_some_iff`, `frame_inj`, `length_of_decode` |
| `Relativization/Univ.lean` | 204 (167) | D6: `Univ.M/mu/budget/input/Acc/Phi/level`, `univOracle` (1–80); A2: the level lemmas and (★) (81–139), Proposition 5 (140–160), `Acc_congr`, `Phi_congr`, (†) `mem_univOracle`, `eq_univOracle_of_fixpoint` (161–204) |
| `Relativization/Counter.lean` | 416 (365) | A3: the counter view (`SK`, `SΓ`, `st`, wrappers, `mulS_run`, `gapS`, `stLoop`; 27–227) and the power loop (`decS_*`, `xferS`, `PW`, `powS`, `powB`, `pow_run`; 229–404), verbatim from PvsNP (337 non-blank); `MS` (24); `TM2OutputsInTime.ofRunLe` (409) |
| `Relativization.lean` | 67 (55) | imports (+11 lines) |
| **Session 5 total** | **722 (617) in the three new files; 626 non-blank with the root module: 337 verbatim, 289 new** | |
| **Repository total** | **5,049 (4,268)** | 1,269 constants: 584 named, 685 auxiliary (same classification as sessions 2–4: 470 + 114 = 584) |

Session 1–4 files are unchanged (byte for byte; the `.olean` of each of the fifteen earlier
modules has the same SHA-256 before any change of this session and after the from-scratch
rebuild, §11.5 (e)). `D:\PvsNP` was opened read-only (`sed`, `diff`); nothing there was
written.

### 11.2 Results asked for in the session brief

All **proved**. Axioms are from the literal `#print axioms` output in §11.5.

| Id | Lean name | File:line | Statement | Differences from §4.11 as first written | Axioms |
|---|---|---|---|---|---|
| A1 | `frame`, `frame_length` | Frame:14, 17 | `frame i T v = 1^i 0 1^T 0 v`; `|frame i T v| = i + T + |v| + 2` | none | none; `[propext, Quot.sound]` |
| A1 | `decode`, `decode_frame` | Frame:59, 68 | `decode (frame i T v) = some (i, T, v)` | none | `[propext]` |
| A1 | `eq_frame_of_decode`, `decode_eq_some_iff`, `frame_inj`, `length_of_decode` | Frame:72, 88, 92, 98 | the converse; `decode x = some (i, T, v) ↔ x = frame i T v`; `frame` injective; `|x|` from `decode x` | none | `[propext]` (×3); `[propext, Quot.sound]` |
| D6 | `Univ.M`, `Univ.mu`, `Univ.budget`, `Univ.input` | Univ:32, 36, 39, 42 | `M_i`, `μ_i(n) = n + 1 + n^{k_i}`, `⌊(T ∸ μ_i(n)) / (D_i + 1)⌋`, `w#y` as `M_i` reads it | none | the three |
| D6 | `Univ.Acc`, `Univ.Phi`, `Univ.Phi_frame` | Univ:53, 59, 62 | the membership condition `Φ(O, x)` of §5.4; `Phi O (frame i T v) ↔ Acc O i T v` | none | the three |
| D6 | `Univ.level`, `univOracle` | Univ:72, 79 | `A_0 = ∅`, `A_{m+1} = A_m ∪ {x : |x| = m ∧ Φ(A_m, x)}`; `A = ⋃ A_m` | none | the three |
| A2 (★) | `Univ.mem_univOracle_iff_trunc` | Univ:128 | `x ∈ A ↔ Φ(A ∩ {z : |z| < |x|}, x)`, PLAN §6.4's equation | none | the three |
| A2, Prop. 5 | `Univ.length_lt_of_mem_queries` | Univ:141 | every query asked within the budget is shorter than the frame | none | the three |
| A2 | `Univ.Acc_congr`, `Univ.Phi_congr` | Univ:164, 171 | truncation is invisible: `Phi O x` depends on `O` only below `|x|` | none | the three |
| **A2 (†)** | **`Univ.mem_univOracle`** | **Univ:177** | **`x ∈ A ↔ Φ(A, x)`, Theorem 6 of §5.6** | none | the three |
| A2 | `Univ.eq_univOracle_of_fixpoint` | Univ:181 | `A` is the only oracle satisfying (†) | none | the three |
| A3 | `Counter.SK`, `SΓ`, `st`, `update_st_c/nil/out` | Counter:30, 35, 44, 53–65 | the counter view | none (verbatim) | none (×3); `[propext, Quot.sound]` (×3) |
| A3 | `Counter.emitS`, `emitOut`, `incS`, `drainS`, `xferES`, `copyS`, `mulS_run`, `gapS`, `stLoop` | Counter:76–177 | `Prog` primitives in the counter view, exact step counts; the runtime loop | none (verbatim) | the three, except `incS`: `[propext, Quot.sound]` |
| A3 | `Counter.decS_pos`, `decS_zero`, `xferS` | Counter:235, 242, 278 | decrement and multi-target transfer in the view | none (verbatim) | the three; `decS_pos`: `[propext, Quot.sound]` |
| **A3** | **`Counter.pow_run`** (with `PW`, `powS`, `powB`) | **Counter:315** (297, 305, 312) | **`p ← p · b^j` within `powB j p b` steps** | none (verbatim) | the three (`PW`, `powS`: none; `powB`: `[propext]`) |
| A3 | `Turing.TM2OutputsInTime.ofRunLe` | Counter:409 | a `RunLe` from `initList` to `haltList` is a time-bounded output | PvsNP `outputsOfRunLe`, renamed | the three |

"The three" = `[propext, Classical.choice, Quot.sound]`.

**Plan forms, assessed** (brief item 3). A1: true as written; the converse was added because
A2 needs it (§4.11). A2: the plan's equation (★) is true as written and is proved
(`mem_univOracle_iff_trunc`), but it is too weak as the interface for A5, which needs (†);
(†) is proved (`mem_univOracle`), and the proof of (†) from (★) uses only session-4 results
(L3/L6' for the query set) and Proposition 5. The fixpoint form in PLAN §4.1 ("then satisfies
the untruncated equation") is therefore correct and is now a theorem; it was not false, not
too weak, and did not depend on anything unproved beyond the arithmetic of Proposition 5. A3:
adequate as written; the exact content ported is listed in §4.11. No session 1–4 definition was
changed, and no hypothesis beyond the statements of §4.11 was needed.

### 11.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Frame | `ones_replicate`, `dropOnes_replicate`, `replicate_ones_append_dropOnes` |
| Univ | `Univ.input_length`, `mem_level_succ`, `length_lt_of_mem_level`, `level_mono`, `mem_level_iff_of_lt`, `mem_univOracle_iff_level`, `univOracle_inter_eq_level` |
| Counter (verbatim) | `MS`, `st_c`, `st_out`, `addU_nil`, `mulS`, `bud_st`, `st_eta`, `tg`, `tg_keys`, `tg_nodupKeys`, `dlookup_tg`, `dlookup_tg_out`, `xf`, the derived instances `instDecidableEqMS`, `instFintypeMS`, `instDecidableEqSK`, `instFintypeSK`, `instDecidableEqPW`, `instFintypePW` (and the auto-generated `xf.congr_simp`, `SK.proxyType`, `PW.proxyType`, `MS.enumList`, …) |

### 11.4 Things a reviewer should know

1. **(★) and (†).** The levels give (★) with the oracle truncated below `|x|`; (†) with the
   untruncated oracle is what A5 will use (§4.11, "How the final collapse proof will use
   this"). The step between them, `Phi_congr`, is one application of L6'
   (`outputsInTime_congr_queries`) per certificate, whose hypothesis is discharged by
   Proposition 5. The machine is named explicitly in these applications
   (`(M i).outputsInTime_congr_queries _ _ _ …`, `(M i).length_le_of_mem_queries hz`), as the
   session-4 elaboration note (§10.4 item 5) advises.
2. **Budget 0.** `Univ.length_lt_of_mem_queries` first shows `0 < budget`: if the budget is 0
   the query set `(M i).queries O l 0 = (Finset.range 0).image _` is empty, so the membership
   hypothesis is absurd. For `budget ≥ 1` the bound is `|z| ≤ μ + β·D < μ + β·D + β ≤ T < |x|`,
   with `Nat.div_mul_le_self` for `β·(D+1) ≤ T ∸ μ` and `Nat.mul_succ` to expose the atom
   `β·D` that L3 produces, then `omega`. This is the "locality argument with budget 0" of
   §7.4 item 3: the length form L5/L6 would need `μ ≤ |x|`, which fails for small `T`.
3. **Global instances added: six, all derived, on the three new inductive types** of the port:
   `Counter.instDecidableEqMS`, `instFintypeMS`, `instDecidableEqSK`, `instFintypeSK`,
   `instDecidableEqPW`, `instFintypePW`, from the `deriving DecidableEq, Fintype` clauses copied
   from PvsNP (`Counter.lean` 25, 33, 302). Sessions 1–4 had no `deriving`; the handlers
   generate ordinary definitions, kernel-checked and axiom-free (`#[]` in the audit log). Two
   global `@[simp]` lemmas, `Counter.st_c` and `st_out` (49, 51), are also verbatim. No earlier
   module can see any of these (new types; no earlier module imports a new one), confirmed by
   the olean hashes, §11.5 (e). No `attribute`, `@[reducible]`, `set_option`, macros, syntax,
   elaborators or `#eval`. The new `abbrev`s are `Univ.M` and `Counter.SΓ` (verbatim).
4. **The port is verbatim**, `logs/session5-port-diff.txt`: `diff` of `Counter.lean` against the
   concatenation of `D3OneHot.lean` 25–225 and `Pre.lean` 35–210 shows only the header hunk
   (`0a1,26`: imports, module docstring, namespace, `MS`) and the tail hunk (`378a405,416`: the
   packaging section and `end`). `MS` is identical to `D3Fam.lean` 301–303; `ofRunLe` differs
   from `Pkg.lean` 307–313 by its name (`_root_.Turing.TM2OutputsInTime.ofRunLe`) and one
   re-wrapped binder line. The one addition to the imports is `Mathlib.Tactic.Linarith`:
   `pow_run` ends with `nlinarith`, which `Prog`'s import closure does not provide (PLAN §6.11
   item 17). `nlinarith` is the first use of a `linarith`-family tactic in the repository.
5. **`eq_`-named declarations and the audit.** The audit's auxiliary rule (a name component
   starting with `eq_`, for the compiler's `eq_1` equation lemmas) also catches
   `eq_frame_of_decode` and `eq_univOracle_of_fixpoint`, so they are absent from the generated
   `#print axioms` file; they are printed in a supplement appended to the same log (§11.5 (b))
   and are in the all-constants log (`[propext]` and the three). The named count 114 excludes
   them, as `Sep.mk` was excluded in session 3.
6. **`Phi` and `level` are plain `def`s** (a `Prop`, and a set by primitive recursion), as
   `Stage.acc` and `sepOracle` were; `M`, `mu`, `budget`, `input` are `noncomputable` because
   they mention `vEnum`. `decode` is total: `none` on strings that are not frames, so
   `Phi O x` is simply false there.
7. **Hidden implicit types, again.** `input_length` cannot be proved by `rw [List.length_map,
   pair_encoding.length_eq]` (the rewritten goal is not type-correct at instance transparency:
   `(pair_encoding …).Γ` versus `pairΓ`); the term
   `(List.length_map _).trans (pair_encoding.length_eq _ _ _)` type-checks at default
   transparency. Two more tooling notes: `induction h` on `h : m ≤ m'` leaves `Nat.le`
   hypotheses that `omega` does not read (`mem_level_iff_of_lt` inducts on the difference
   instead); a `match` in a hypothesis is split with `split at h`, since `generalize … at h`
   leaves the matcher untouched (`eq_frame_of_decode`).
8. **Uniqueness** (`eq_univOracle_of_fixpoint`) is not needed for T5; it is the second half of
   Theorem 6 and cost 20 lines, so it is proved to close §5.6 completely.
9. **Not done, by instruction:** A4 (`pad`), A5, A6, T5–T8. The open design point for A4 is
   recorded in §4.11 (embed the counter sub-machine with `Emb.run_embed`, or give the counter
   view an input stack); `pow_run` is a `RunLe`, so `TM2OutputsInTime.ofRunLe` is the packaging.
   `Pkg.eval_le_pow` (PvsNP, 30 lines) is not yet ported; A5 needs it.

### 11.5 Check outputs

Full logs are in `logs/`: `session5-axioms-all.txt`, `session5-print-axioms.txt`,
`session5-build.txt`, `session5-scan.txt`, `session5-olean-before.txt`,
`session5-olean-after.txt`, `session5-port-diff.txt`. The audit scripts are outside the
repository (scratchpad).

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`, as in sessions 1–4). Last lines of `logs/session5-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 1269 (584 named, 685 auxiliary)
named in new modules (Frame, Univ, Counter): 114
UNION of axioms used: #[propext, Classical.choice, Quot.sound]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: #[]
```

Per module: 33 constants in `Frame`, 36 in `Univ`, 167 in `Counter`
(`grep -c "^Relativization.Frame "` etc. on the log).

**(b) Literal `#print axioms` on each of the 114 named declarations of the three new
modules, plus the two `eq_`-named ones** (`logs/session5-print-axioms.txt`, 114 + 2 output
lines, 0 errors). Distribution of the 114 (`sed -E "s/^'[^']*' //" | sort | uniq -c`):

```
     38 depends on axioms: [propext, Classical.choice, Quot.sound]
     11 depends on axioms: [propext, Quot.sound]
      8 depends on axioms: [propext]
     57 does not depend on any axioms
```

`grep -c sorryAx` on both logs prints `0` and `0`. The results of §11.2:

```
'Relativization.frame' does not depend on any axioms
'Relativization.frame_length' depends on axioms: [propext, Quot.sound]
'Relativization.decode' depends on axioms: [propext]
'Relativization.decode_frame' depends on axioms: [propext]
'Relativization.decode_eq_some_iff' depends on axioms: [propext]
'Relativization.frame_inj' depends on axioms: [propext]
'Relativization.length_of_decode' depends on axioms: [propext, Quot.sound]
'Relativization.Univ.M' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.mu' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.input' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.Acc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.Phi' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.Phi_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.level' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.univOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.mem_univOracle_iff_trunc' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.length_lt_of_mem_queries' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.Acc_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.Phi_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Univ.mem_univOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Counter.SK' does not depend on any axioms
'Relativization.Counter.st' does not depend on any axioms
'Relativization.Counter.emitS' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Counter.xferES' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Counter.mulS_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Counter.stLoop' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Counter.pow_run' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the supplement (the two names the audit rule classes as auxiliary):

```
== supplement: the two new declarations whose name starts with eq_ (classed auxiliary by the audit rule) ==
'Relativization.eq_frame_of_decode' depends on axioms: [propext]
'Relativization.Univ.eq_univOracle_of_fixpoint' depends on axioms: [propext, Classical.choice, Quot.sound]
exit: 0
```

(`Turing.TM2OutputsInTime.ofRunLe` is among the 38 with the three.)

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`, the same three
scans as §7.5 (c) (`logs/session5-scan.txt`):

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
Relativization/Comp.lean:27:attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
Relativization/Comp.lean:39:@[reducible] def CΓ : CK M₁ M₂ → Type
Relativization/Counter.lean:25:  deriving DecidableEq, Fintype
Relativization/Counter.lean:33:  deriving DecidableEq, Fintype
Relativization/Counter.lean:49:@[simp] theorem st_c (f : C → ℕ) (o : List Bool) (x : C) : st f o (.c x) = cnt () (f x) := rfl
Relativization/Counter.lean:51:@[simp] theorem st_out (f : C → ℕ) (o : List Bool) : st f o .out = o := rfl
Relativization/Counter.lean:302:  deriving DecidableEq, Fintype
Relativization/Normal.lean:96:attribute [local instance] OracleFinTM2.kFin OracleFinTM2.ΛFin OracleFinTM2.σFin
Relativization/Oracle.lean:261:attribute [local instance] OracleFinTM2.ΛFin
Relativization/Plain.lean:23:attribute [local instance] FinTM2.kFin
Relativization/Plain.lean:28:@[reducible] def PΓ : Option M.K → Type
Relativization/Prog.lean:49:attribute [simp] Flag.untag_tag
Relativization/Prog.lean:93:@[simp] theorem cnt_length {α : Type} (u : α) (n : ℕ) : (cnt u n).length = n :=
Relativization/Prog.lean:98:@[simp] theorem cnt_zero {α : Type} (u : α) : cnt u 0 = [] := rfl
Relativization/Prog.lean:656:@[simp] theorem rep_zero {α : Type} (ys : List α) : rep ys 0 = [] := rfl
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

The ten hits of §10.5 (c) plus the five verbatim lines of `Counter.lean` (§11.4 item 3);
`Frame.lean` and `Univ.lean` contribute none.

**(d) `lake build`**, after deleting this project's own build artifacts
(`.lake/build/lib/lean/Relativization*`, `.lake/build/ir/Relativization*`) so that every module
was recompiled (`logs/session5-build.txt`; `grep -c -i -E "warning|error"` on it prints `0`):

```
✔ [1323/1339] Built Relativization.Count (11s)
✔ [1324/1339] Built Relativization.Classes (12s)
✔ [1325/1339] Built Relativization.Halt (12s)
✔ [1326/1339] Built Relativization.Normal (12s)
✔ [1327/1339] Built Relativization.Queries (12s)
✔ [1328/1339] Built Relativization.Prog (13s)
✔ [1329/1339] Built Relativization.Plain (11s)
✔ [1330/1339] Built Relativization.Comp (12s)
✔ [1331/1339] Built Relativization.Codes (12s)
✔ [1332/1339] Built Relativization.Self (12s)
✔ [1333/1339] Built Relativization.Emb (16s)
✔ [1334/1339] Built Relativization.Counter (16s)
✔ [1335/1339] Built Relativization.Sep (10s)
✔ [1336/1339] Built Relativization.Univ (10s)
✔ [1337/1339] Built Relativization.Stage (8.8s)
✔ [1338/1339] Built Relativization (8.4s)
Build completed successfully (1339 jobs).

real	1m7.352s
user	0m0.015s
sys	0m0.015s
exit: 0
```

**(e) Earlier modules elaborate unchanged.** SHA-256 of each session 1–4 `.olean` before any
change of this session (`logs/session5-olean-before.txt`) and after the from-scratch rebuild
with the new modules present (`logs/session5-olean-after.txt`):

```
== olean hashes: earlier modules, before vs after the from-scratch rebuild ==
*Classes.olean SAME 43f4554b909236c7463f66a59da5add30adb3f4084b8e48de414a2381efe3896
*Codes.olean SAME c5e2c117e4ebe67f687ef83b1d8d2573830c2ad11aeb4b589ea22c352fd1bb8e
*Comp.olean SAME c560c3c025efabecdee7f093bf9946eaf00f2e9cfa03fd52ce3836bea892daf8
*Count.olean SAME 3221435b3f6dad351b0e01a73d991c923b6e25a3ee05ca4c4077825178625568
*Countable.olean SAME d4012351737c0774a51826920bd5e637f07d5c135cc3b929966dc5d08aa6e351
*Emb.olean SAME 7203cedb57039239eb3735ee203b3d00d4b141f5e6974c8f1bbda90077a0b42f
*Halt.olean SAME bbec64145c811dcfdf6c5f1be0683a461b4c9478cf354a31201ecda23db125b5
*Normal.olean SAME 292ec4f641ebb808ff8e37075405b7dea60e9f5ae22bf307e2a8b327de47c0a3
*Oracle.olean SAME aba34f40f7e4fc0812b4a80bc0a42d472770e255cd15ff572793f04a5f8751da
*Plain.olean SAME 538a20892c70be803e666d35140c75b811aca5ba27aa95032ef8ac94dc690561
*Prog.olean SAME 9f91d8f0624f08e0a079ce2712a2bd5ec7f5d67053fa115d27386cc3a7b3ff7b
*Queries.olean SAME 55dd84a847e3354d80daf7abe0563cc75fe312bd57ce7cc790c6a5dfdc58b7da
*Self.olean SAME 2a154bef41f5362745a35ac188e0624a5afe435ffd3a9df2bad3f959aa019753
*Sep.olean SAME b004c415b234932d33d7025328c104416eb924f01af127fc757bbe872dc72280
*Stage.olean SAME ddb07f381ae1823929f6b436b631bea29cd76e27762072058fbe49242581761b
```

(The first twelve values are those of `logs/session4-olean-after.txt`; the three of `Count`,
`Queries`, `Stage` are those of `logs/session5-olean-before.txt`, taken before any change.)

`lake env leanchecker --fresh` was not run this session (it is an acceptance check for T7).

## 12. Lemma table and checks (session 6, 2026-10-08)

### 12.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Pad.lean` | 363 (303) | A4: `padFun` (34); `IsPoly` and its closure lemmas, verbatim from PvsNP (39–57); the machine: `PC`, `PK`, `PΓ`, `CL`, `PL`, `cprog`, `padEmb`, `rdStmt`, `pprog`, `padTM`, `padB` (61–132); the sub-machine's run `cprog_run` with `F0`–`F3`, `cB`, `rep_singleton` (134–187); the copy loop `pst`, `update_pst_inp/cv/out/c`, `cons_cnt`, `stepAux_rd_cons/nil`, `rd_run` (189–264); the embedding `embeds`, `agree`, `eq_pst_of_agree` (266–282); `initList_pad`, `haltList_pad`, `pad_run` (284–328); `padB_poly`, `padComputable` (330–361) |
| `Relativization.lean` | 74 (60) | imports (+1 line), docstring (+6 lines, 5 non-blank) |
| **Session 6 total** | **363 (303) in the new file; 308 non-blank with the root module: 13 verbatim, 295 new** | |
| **Repository total** | **5,419 (4,576)** | 1,610 constants: 694 named, 916 auxiliary (same classification as sessions 2–5: 584 + 110 = 694) |

Session 1–5 files are unchanged (byte for byte; the `.olean` of each of the eighteen earlier
modules has the same SHA-256 before any change of this session and after the from-scratch
rebuild, §12.5 (e)). `D:\PvsNP` was opened read-only (`sed`, `diff`); nothing there was
written. Per section of `Pad.lean` (non-blank): header 28, `[POLY]` 14, `[DEF]` 61, `[CNT]` 47,
`[RD]` 67, `[EMB]` 14, `[RUN]` 42, `[PKG]` 30.

### 12.2 Results asked for in the session brief

All **proved**; A4 is complete (the brief allowed two sessions). Axioms are from the literal
`#print axioms` output in §12.5.

| Id | Lean name | File:line | Statement | Differences from §4.12 as first written | Axioms |
|---|---|---|---|---|---|
| A4, function | `padFun` | Pad:34 | `padFun i c' d w = frame i ((|w| + c')^d) w.reverse` | none | `[propext]` |
| A4, machine | `Pad.padTM` (with `PC`, `PK`, `PΓ`, `CL`, `PL`, `cprog`, `padEmb`, `rdStmt`, `pprog`) | Pad:120 (65–115) | the `FinTM2`: input stack `inp`, output stack `cv .out`, states `Bool`, program `pprog i c' d` | none | the three (`cprog`, `padEmb`, `rdStmt`: none; `pprog`: `[Quot.sound]`) |
| A4, bound | `Pad.padB` | Pad:132 | `2n + c' + 9 + powB d 1 (n + c') + (n + c')^d` | none | `[propext]` |
| A4, sub-machine | `Pad.cprog_run` | Pad:166 | from `out = o`, `b = n`, all else `0`: label `fin`, `out = frame i ((n + c')^d) o`, every counter `0`, within `cB c' d n` | none | the three |
| A4, copy loop | `Pad.rd_run` | Pad:243 | `|s| + 1` steps from `rd` to `cp sep1`; `inp = []`, `out = s.reverse ++ o`, `b += |s|`, state `false` | none | the three |
| A4, correctness and time | `Pad.pad_run` | Pad:306 | `RunLe (padTM i c' d).m (padB c' d |w|) (initList … w) (haltList … (padFun i c' d w))` | none | the three |
| A4, polynomial | `Pad.padB_poly` | Pad:332 | `IsPoly (padB c' d)` | none | the three |
| **A4** | **`Pad.padComputable`** | **Pad:342** | **`TM2ComputableInPolyTime (fin_encoding_string Bool).encode (fin_encoding_string Bool).encode (padFun i c' d)`** | none | the three |

"The three" = `[propext, Classical.choice, Quot.sound]`.

**Plan form, assessed** (brief item 1). PLAN §6.4 A4 says "`pad` as a `TM2ComputableInPolyTime`
on the counter view"; §4.12 fixes the exact form A5 consumes (identity encodings on both
sides, parametric in `i c' d`, `time := Classical.choose (padB_poly c' d)`), and that form is
what is proved. The §4.12 phase table was confirmed line by line by the proof: the final
`omega` of `pad_run` closes `(|w| + 1) + cB c' d |w| + 1 ≤ padB c' d |w|`, which is an equality.
**Design decision** (brief item 2): route E (embedding) was chosen and used; route V was
assessed in §4.12 and not taken (V1 would change `Counter.SK`, V2 duplicates `pow_run`). No
session 1–5 definition was changed and no hypothesis beyond §4.12 was needed.

### 12.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Pad (verbatim) | `IsPoly`, `IsPoly.const`, `IsPoly.id`, `IsPoly.add`, `IsPoly.mul`, `IsPoly.pow` |
| Pad (new) | `F0`, `F1`, `F2`, `F3`, `cB`, `rep_singleton`, `pst`, `update_pst_inp`, `update_pst_cv`, `update_pst_out`, `update_pst_c`, `cons_cnt`, `stepAux_rd_cons`, `stepAux_rd_nil`, `embeds`, `agree`, `eq_pst_of_agree`, `initList_pad`, `haltList_pad`; the derived instances `instDecidableEqPC`, `instFintypePC`, `instDecidableEqPK`, `instFintypePK`, `instDecidableEqCL`, `instFintypeCL`, `instDecidableEqPL`, `instFintypePL` (and the auto-generated `*.proxyType`, `*.enumList`, `*.ofNat`, `*.toCtorIdx`, …) |

### 12.4 Things a reviewer should know

1. **Route E, as decided in §4.12.** The counter sub-machine `cprog i c' d` is a program of A3's
   counter view (`TM2.Stmt (SΓ PC) CL Bool`), and `cprog_run` is proved entirely with A3's
   wrappers in the `st F o` view (`emitOut`, `emitS` ×3, `pow_run`, `xferES`, `emitOut`,
   `drainS`), chained with `Bud` exactly as PvsNP's `cprog_run`; `pow_run` is used unchanged
   with `b kc p q ad t := PC.b PC.kc PC.p PC.q PC.ad PC.t`, `mk := CL.pw`, `exit := .emitT`, its
   nodup hypothesis by `decide`. The host runs it through `Emb.runLe_embed (E := padEmb) PL.cp`;
   `padEmb` is `e := PK.cv`, `ι := fun _ => Equiv.refl _` (three one-line proofs: `embeds`,
   `agree`, `eq_pst_of_agree`). The input stack `inp` is outside the image of `PK.cv`, so
   `Emb.Frame` says it stays empty during the sub-run.
2. **Global instances added: eight, all derived, on the four new inductive types**
   `PC`, `PK`, `CL`, `PL` (`deriving DecidableEq, Fintype`, `Pad.lean` 66, 70, 79, 83). The
   `DecidableEq` instances are unavoidable (`Function.update` and `TM2.stepAux` need them, and
   `FinTM2.kDecidableEq` is a field); the `Fintype` instances fill the `FinTM2` fields `kFin`
   and `ΛFin`. No earlier module can see them (new types), confirmed by the olean hashes. No
   `@[simp]`, `attribute`, `set_option`, macro, syntax, elaborator or `#eval`; the one linter
   warning that appeared (`unnecessarySeqFocus`, a `<;>` with a single surviving goal) was
   fixed by restructuring the tactic, not silenced. The one new `abbrev` is `PΓ`.
3. **The state type is `Bool`**, forced because `Emb.mapS` keeps the state type and the counter
   view is over `Bool`. So the copy loop cannot encode "popped nothing" in the state as
   `Sep.revTM` (state `Option _`) does; it peeks first and branches (`rdStmt`), the pattern of
   PvsNP's `rdT`. One `TM2.step` per bit; the exit step takes the state to `false`, which is
   what `haltList` demands (`initialState = false`), and every later phase ends in `false`.
4. **`padB` does not depend on `i`**: the constant block `1^i 0` is one `emitR`, one step. The
   degree in `n` is `d + 1` for `d ≥ 1` (from `powB d 1 (n + c')`), and `padB_poly` is proved by
   the `IsPoly` closure lemmas, whose `fun n => f n + g n` shapes unify with the unfolded
   `padB`/`powB` by higher-order pattern unification (as PvsNP `gB_poly`).
5. **Tooling notes.** (a) `update_pst_c` did not fire as a `simp only` lemma in
   `stepAux_rd_cons`, with or without a type ascription on its `cnt () n`: the goal's `cnt`
   lives at the type `PΓ (PK.cv (SK.c PC.b))`, an `abbrev` applied to a constructor, which
   `simp`'s reducible unifier does not identify with `SΓ PC (SK.c PC.b)`; `rw [update_pst_c]`
   closes the goal. (b) `rintro l l' n rfl rfl hn` on `l = w` with both sides variables
   substitutes away the right-hand `w`, so the body refers to `l` (`pad_run i c' d l`).
   (c) `Run.single` takes a `TM2.stepAux` equation and `Run.head` a `TM2.step` equation; the
   copy-loop induction uses `Run.head` with `simp only [TM2.step, pprog, stepAux_rd_cons]`.
   (d) `initList_pad`/`haltList_pad` are `congr 1; funext k; rcases k …; rfl`, as
   `Sep.initList_eq` and PvsNP `initList_full`; the derived `DecidableEq` reduces on
   constructors.
6. **The port is verbatim**, `logs/session6-port-diff.txt`: `diff` of `Pad.lean` 39–57 against
   PvsNP `Pre.lean` 717–735 is empty (`IsPoly` and five lemmas, 13 non-blank lines). `IsPoly` is
   placed in namespace `Relativization` (PvsNP: `PvsNP.Pre`). `eval_le_pow` (A5) is not yet
   ported.
7. **`eq_`-named declaration and the audit.** `Pad.eq_pst_of_agree` is classed auxiliary by the
   audit rule (§11.4 item 5) and is absent from the generated `#print axioms` file; it is
   printed in the supplement appended to the same log (§12.5 (b)). The named count 110 excludes
   it.
8. **Where `Classical.choice` enters A4.** `padTM`, `pad_run`, `cprog_run`, `rd_run`,
   `padB_poly` and `padComputable` carry the three; `padFun`, `padB`, `rep_singleton` only
   `[propext]`; `cprog`, `padEmb`, `rdStmt` none. The audit log has every constant's list.
9. **Not done, by instruction:** A5, A6, T5–T8. PLAN §6.12 has the exact remaining work.

### 12.5 Check outputs

Full logs are in `logs/`: `session6-axioms-all.txt`, `session6-print-axioms.txt`,
`session6-build.txt`, `session6-scan.txt`, `session6-olean-before.txt`,
`session6-olean-after.txt`, `session6-port-diff.txt`. The audit scripts are outside the
repository (scratchpad).

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`, as in sessions 1–5). Last lines of `logs/session6-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 1610 (694 named, 916 auxiliary)
named in new modules (Pad): 110
UNION of axioms used: #[propext, Classical.choice, Quot.sound]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: #[]
```

Per module: 341 constants in `Pad` (`grep -c "^Relativization.Pad "` on the log).

**(b) Literal `#print axioms` on each of the 110 named declarations of the new module, plus
the one `eq_`-named declaration** (`logs/session6-print-axioms.txt`, 110 + 1 output lines,
0 errors, both `exit: 0`). Distribution of the 110 (`sed -E "s/^'[^']*' //" | sort | uniq -c`):

```
     18 depends on axioms: [propext, Classical.choice, Quot.sound]
      7 depends on axioms: [propext, Quot.sound]
     10 depends on axioms: [propext]
      2 depends on axioms: [Quot.sound]
     74 does not depend on any axioms
```

`grep -c sorryAx` on both logs prints `0` and `0`. The results of §12.2:

```
'Relativization.padFun' depends on axioms: [propext]
'Relativization.IsPoly' depends on axioms: [propext, Quot.sound]
'Relativization.Pad.cprog' does not depend on any axioms
'Relativization.Pad.padEmb' does not depend on any axioms
'Relativization.Pad.pprog' depends on axioms: [Quot.sound]
'Relativization.Pad.padTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Pad.padB' depends on axioms: [propext]
'Relativization.Pad.rep_singleton' depends on axioms: [propext]
'Relativization.Pad.cprog_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Pad.rd_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Pad.embeds' depends on axioms: [Quot.sound]
'Relativization.Pad.agree' depends on axioms: [propext, Quot.sound]
'Relativization.Pad.pad_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Pad.padB_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Pad.padComputable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and the supplement:

```
== supplement: the new declaration whose name starts with eq_ (classed auxiliary by the audit rule) ==
'Relativization.Pad.eq_pst_of_agree' depends on axioms: [propext, Quot.sound]
exit: 0
```

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`, the same three
scans as §7.5 (c) (`logs/session6-scan.txt`):

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
Relativization/Pad.lean:66:  deriving DecidableEq, Fintype
Relativization/Pad.lean:70:  deriving DecidableEq, Fintype
Relativization/Pad.lean:79:  deriving DecidableEq, Fintype
Relativization/Pad.lean:83:  deriving DecidableEq, Fintype
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

(the fifteen hits of §11.5 (c) in earlier files are unchanged and omitted here; the four
`Pad.lean` lines are §12.4 item 2).

**(d) `lake build`**, after deleting this project's own build artifacts
(`.lake/build/lib/lean/Relativization*`, `.lake/build/ir/Relativization*`) so that every module
was recompiled (`logs/session6-build.txt`; `grep -c -i -E "warning|error"` on it prints `0`;
`grep -c "Built Relativization"` prints `20`, the nineteen modules and the root):

```
✔ [1338/1340] Built Relativization.Stage (19s)
✔ [1339/1340] Built Relativization (13s)
Build completed successfully (1340 jobs).

real	2m33.866s
user	0m0.015s
sys	0m0.000s
exit: 0
```

The single-file check `lake env lean Relativization/Pad.lean` prints nothing (exit 0, about
21 s).

**(e) Earlier modules elaborate unchanged.** SHA-256 of each session 1–5 `.olean` before any
change of this session (`logs/session6-olean-before.txt`) and after the from-scratch rebuild
with the new module present (`logs/session6-olean-after.txt`):

```
== olean hashes: earlier modules, before vs after the from-scratch rebuild ==
*Classes.olean SAME 43f4554b909236c7463f66a59da5add30adb3f4084b8e48de414a2381efe3896
*Codes.olean SAME c5e2c117e4ebe67f687ef83b1d8d2573830c2ad11aeb4b589ea22c352fd1bb8e
*Comp.olean SAME c560c3c025efabecdee7f093bf9946eaf00f2e9cfa03fd52ce3836bea892daf8
*Count.olean SAME 3221435b3f6dad351b0e01a73d991c923b6e25a3ee05ca4c4077825178625568
*Countable.olean SAME d4012351737c0774a51826920bd5e637f07d5c135cc3b929966dc5d08aa6e351
*Counter.olean SAME 0e1120a345818dfe98fdec7c43a9c0ea4c5e35e03d1d76b1f59588b01a11d6fc
*Emb.olean SAME 7203cedb57039239eb3735ee203b3d00d4b141f5e6974c8f1bbda90077a0b42f
*Frame.olean SAME 07be8f33280c713459299e3942a46a5695c7c61173af4b5cc506f7f81fce0382
*Halt.olean SAME bbec64145c811dcfdf6c5f1be0683a461b4c9478cf354a31201ecda23db125b5
*Normal.olean SAME 292ec4f641ebb808ff8e37075405b7dea60e9f5ae22bf307e2a8b327de47c0a3
*Oracle.olean SAME aba34f40f7e4fc0812b4a80bc0a42d472770e255cd15ff572793f04a5f8751da
*Plain.olean SAME 538a20892c70be803e666d35140c75b811aca5ba27aa95032ef8ac94dc690561
*Prog.olean SAME 9f91d8f0624f08e0a079ce2712a2bd5ec7f5d67053fa115d27386cc3a7b3ff7b
*Queries.olean SAME 55dd84a847e3354d80daf7abe0563cc75fe312bd57ce7cc790c6a5dfdc58b7da
*Self.olean SAME 2a154bef41f5362745a35ac188e0624a5afe435ffd3a9df2bad3f959aa019753
*Sep.olean SAME b004c415b234932d33d7025328c104416eb924f01af127fc757bbe872dc72280
*Stage.olean SAME ddb07f381ae1823929f6b436b631bea29cd76e27762072058fbe49242581761b
*Univ.olean SAME 764ce3af55c8fd6bd56c16f1e848abff8cb19541e398c8a99c19849247480cb5
new module:
a893514d9d9a7b9ee198efefd4a46a9bc59129eb29f5f01884c43c5670167c6f *Pad.olean
```

(The first fifteen values are those of `logs/session5-olean-after.txt`; the three of
`Counter`, `Frame`, `Univ` are new in the "before" file, taken before any change of this
session.)

`lake env leanchecker --fresh` was not run this session (it is an acceptance check for T7).

---

## 13. Lemma table and checks (session 7, 2026-10-08)

### 13.1 Files

| File | Lines (non-blank) | Content |
|---|---|---|
| `Relativization/Collapse.lean` | 189 (156) | `[POLY]` `pow_weaken`, `eval_le_pow`, verbatim from PvsNP (32–57); `[TIME]` `OTM2OutputsInTime.mono` (59–67); `[EXP]` `Collapse.muPoly`, `muPoly_eval`, `padPoly`, `padPoly_eval`, `exists_exponents`, `eval_le_budget` (69–99); `[ACC]` `Collapse.Acc_reverse`, `padFun_mem_iff` (101–120); `[RED]` A5 `exists_pad_reduction` (122–166); `[COL]` `inP_of_pad_reduction`, `inNP_subset_inP`, A6 `univOracle_pEqNP` (168–187) |
| `Relativization/BakerGillSolovay.lean` | 33 (25) | T5 `collapse` (21), T6 `separation` (25), T7 `baker_gill_solovay` (30) |
| `Relativization.lean` | 85 (69) | imports (+2 lines), docstring (+9 lines, 7 non-blank) |
| **Session 7 total** | **222 (181) in the two new files; 190 non-blank with the root module: 25 verbatim, 165 new** | |
| **Repository total** | **5,652 (4,766)** | 1,642 constants: 712 named, 930 auxiliary (same classification as sessions 2–6: 694 + 18 = 712) |

Session 1–6 files are unchanged (byte for byte; the `.olean` of each of the nineteen earlier
modules has the same SHA-256 before any change of this session and after the from-scratch
rebuild, §13.5 (e)). `D:\PvsNP` was opened read-only (`sed`, `diff`); nothing there was
written. Per section of `Collapse.lean` (non-blank): header 20, `[POLY]` 26, `[TIME]` 7,
`[EXP]` 25, `[ACC]` 16, `[RED]` 44, `[COL]` 18.

### 13.2 Results asked for in the session brief

All **proved**. Axioms are from the literal `#print axioms` output in §13.5.

| Id | Lean name | File:line | Statement | Differences from §4.13 as first written | Axioms |
|---|---|---|---|---|---|
| port | `pow_weaken`, `eval_le_pow` | Collapse:32, 36 | `∃ c e, 1 ≤ c ∧ ∀ j, p.eval j ≤ (j + c)^e` | none (verbatim) | `[propext, Quot.sound]`; the three |
| A5, time | `OTM2OutputsInTime.mono` | Collapse:62 | an output within `t` is an output within `t' ≥ t` | none | the three |
| A5, polynomial | `Collapse.muPoly`, `muPoly_eval`, `padPoly`, `padPoly_eval` | Collapse:72, 74, 78, 81 | `μ_i` and `μ_i + (D_i + 1) · (p ∘ μ_i)` as polynomials, with their evaluations | none | the three |
| A5, exponents | `Collapse.exists_exponents` | Collapse:86 | `∃ c' d, ∀ n, μ_i(n) + (D_i + 1) · p(μ_i(n)) ≤ (n + c')^d` | none | the three |
| A5, budget | `Collapse.eval_le_budget` | Collapse:94 | with such `c', d`: `p(μ_i(n)) ≤ budget i ((n + c')^d) n` | none | the three |
| A5, pad in `A` | `Collapse.Acc_reverse`, `padFun_mem_iff` | Collapse:104, 111 | `padFun i c' d w ∈ A ↔ ∃ y, |y| ≤ |w|^{k_i} ∧ M_i^A outputs [true] on w#y within the budget` | none | the three |
| **A5** | **`exists_pad_reduction`** | **Collapse:126** | **`L ∈ NP^A → ∃ i c' d, ∀ w, L w ↔ padFun i c' d w ∈ univOracle`** | none | the three |
| A6, composition | `inP_of_pad_reduction` | Collapse:172 | a pad reduction puts `L` in `P^A` (A4, T3, F7) | none | the three |
| A6, Theorem 7 | `inNP_subset_inP` | Collapse:180 | `NP^A ⊆ P^A` for `A = univOracle` | none | the three |
| **A6** | **`univOracle_pEqNP`** | **Collapse:186** | **`PEqNP univOracle`** | none | the three |
| **T5** | **`collapse`** | **BakerGillSolovay:21** | **`∃ A : Oracle, PEqNP A`** | none | the three |
| **T6** | **`separation`** | **BakerGillSolovay:25** | **`∃ B : Oracle, ¬ PEqNP B`** | none | the three |
| **T7** | **`baker_gill_solovay`** | **BakerGillSolovay:30** | **`(∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B)`** | none | the three |

"The three" = `[propext, Classical.choice, Quot.sound]`.

**Plan forms, assessed** (brief item 2): recorded in §4.13 before the proofs. A5 was true and
adequate once `pad` was made explicit (the existential over `i c' d`); A6 adequate; T5, T6, T7
proved word for word as in PLAN §6.2 and §3. No statement turned out false or too weak. The
§4.13 proof sketch was followed step by step; the only departure is a tooling one (§13.4
item 3). No session 1–6 definition was changed, no hypothesis beyond §4.13 was needed, and no
global instance was added.

**T7 against brief item 4.** `baker_gill_solovay` is a conjunction of two existentials over the
one type `Oracle := Set (List Bool)` about the one predicate `PEqNP : Oracle → Prop` of
`Relativization/Classes.lean` (D3), which is `InP A (fin_encoding_string Bool) L ↔ InNP A
(fin_encoding_string Bool) L` for every `L`. The collapse half uses `PEqNP univOracle`
(`univOracle_pEqNP`) and the separation half `¬ PEqNP sepOracle` (`sepOracle_not_pEqNP`,
session 4); both go through the same `InP` and `InNP`.

### 13.3 Supporting declarations (all proved; names as in the files)

| File | Declarations |
|---|---|
| Collapse (verbatim) | `pow_weaken`, `eval_le_pow` |
| Collapse (new) | `OTM2OutputsInTime.mono`, `Collapse.muPoly`, `muPoly_eval`, `padPoly`, `padPoly_eval`, `exists_exponents`, `eval_le_budget`, `Acc_reverse`, `padFun_mem_iff`, `inP_of_pad_reduction`, `inNP_subset_inP` |

No `eq_`-named declaration and no `def mk` this session: the 18 named declarations of the
audit are exactly the 18 lines of the `#print axioms` file, so no supplement is needed.

### 13.4 Things a reviewer should know

1. **Two files, not one.** PLAN §6.12 scheduled items 1–7 for one file `Collapse.lean`;
   `Collapse.lean` holds items 1–6 (the collapse half, importing `Univ`, `Pad`, `Halt`, `Self`,
   `Comp`, nothing from the separation half) and `BakerGillSolovay.lean` holds item 7, the
   three final theorems, importing `Collapse` and `Stage`. The main theorem is thus in a
   33-line file whose only content is T5, T6, T7 and their docstrings; its proof terms are the
   three anonymous constructors of §4.13.
2. **Where the §5.7 hypotheses are used in `exists_pad_reduction`.** `k_i = k` from N4v' is
   `subst`ed (so `k` becomes `(vEnum i).k` everywhere, including in `hLR`); the verifier's
   output `h.outputsFun (w, y)` is used only for `|y| ≤ |w|^{k_i}` and is weakened from
   `h.time.eval (|w| + 1 + |y|)` to the budget by `Comp.eval_mono` (through `μ_i(|w|)`),
   `eval_le_budget` and `OTM2OutputsInTime.mono`; the machine is named explicitly in F4',
   `OTM2OutputsInTime.bool_iff (tm := Univ.M i) (vEnum i).outE hB true` (§10.4 item 5). The
   certificate is transported along `ρ` by hand (`List.length_map` for the bound,
   `List.map_map`, `Equiv.self_comp_symm`, `List.map_id` for `(y'.map ρ.symm).map ρ = y'`).
   (†) enters once, inside `padFun_mem_iff`, with `univOracle` on both sides.
3. **Hidden implicit type, once more** (§7.4 item 7, §11.4 item 7). After `rw [hLR w]` the
   certificate bound reads `((fin_encoding_string Bool).encode w).length ^ k_i`, whose
   `List.length` is at the type `(fin_encoding_string Bool).Γ`; the `simpa using hy` steps then
   failed with "Type mismatch: After simplification" on two visually identical types. Fix:
   restate the clause at type `Bool` first, `have hLR' : L w ↔ ∃ y : List Γ₁, y.length ≤
   w.length ^ (vEnum i).k ∧ R w y := hLR w` (defeq at default transparency), and rewrite
   with `hLR'`. Likewise `hR (w, y) : R (w, y).1 (w, y).2 ↔ …` is restated as
   `hR' : R w y ↔ f (w, y) = true` so that `rw` finds `R w y`. The `|w#y|` bound is
   `(pair_encoding.length_eq _ _ _).le.trans` followed by `show w.length + 1 + y.length ≤ _`,
   as `Univ.input_length` was proved (§11.4 item 7).
4. **The budget arithmetic** (`eval_le_budget`) is `Nat.le_div_iff_mul_le`, `mul_comm` and
   `Nat.le_sub_of_add_le' : m + n ≤ k → n ≤ k - m` (Lean core), no `omega` on products:
   from `μ + (D + 1) · P ≤ T` to `P · (D + 1) ≤ T ∸ μ` to `P ≤ (T ∸ μ) / (D + 1)`.
5. **Global instances added: none.** No `instance`, `deriving`, `attribute`, `@[simp]`,
   `@[reducible]`, `set_option`, macro, syntax, elaborator or `#eval` in either new file
   (§13.5 (c): the marker scan has no hit in them). No new `abbrev`. `OTM2OutputsInTime.mono`
   is a `def` because `OTM2OutputsInTime` is a `Type` (a structure), as `OutputsInTime.congr`
   is; `muPoly` and `padPoly` are `noncomputable` (they mention `vEnum`). `open Polynomial` is
   used for `X` and `C`.
6. **The port is verbatim**, `logs/session7-port-diff.txt`: `diff` of `Collapse.lean` 32–57
   against PvsNP `Pkg.lean` 391–416 is empty (`pow_weaken`, `eval_le_pow`; 25 non-blank
   lines). `eval_mono'` of that file (`Pkg.lean` 384–389) is `Comp.eval_mono` (session 1), used
   here as such. The port needs `ring`, available through `Pad`'s import closure
   (`Mathlib.Tactic.Linarith`, §11.4 item 4).
7. **What T5 proves about the oracle.** `collapse` is `⟨univOracle, univOracle_pEqNP⟩`, so the
   collapse oracle is the explicit D6 set and the theorem `PEqNP univOracle` is available on
   its own; likewise `¬ PEqNP sepOracle`. The reading of the final statements in terms of
   `Classes.lean`, and the list of what makes them weaker than or different from the textbook
   theorem (machine model, binary alphabet, the particular oracle, the Clay form of `NP`, the
   step count, non-constructive witnesses, universe `Type`), is §4.13 and is unchanged by the
   proofs.
8. **Not run:** `lake env leanchecker --fresh` (the acceptance check of PLAN §6.2 scheduled
   for the session-8 red-team pass, PLAN §6.12). **Not done, by instruction:** T8 and the
   red-team pass.

### 13.5 Check outputs

Full logs are in `logs/`: `session7-axioms-all.txt`, `session7-print-axioms.txt`,
`session7-build.txt`, `session7-scan.txt`, `session7-olean-before.txt`,
`session7-olean-after.txt`, `session7-port-diff.txt`. The audit scripts are outside the
repository (scratchpad).

**(a) Every constant, read-only audit** (`Lean.collectAxioms` over every constant whose module
is `Relativization*`, as in sessions 1–6). Last lines of `logs/session7-axioms-all.txt`:

```
TOTAL constants in Relativization modules: 1642 (712 named, 930 auxiliary)
named in new modules (Collapse, BakerGillSolovay): 18
UNION of axioms used: #[propext, Classical.choice, Quot.sound]
CONSTANTS using anything outside [propext, Classical.choice, Quot.sound]: #[]
```

Per module: 29 constants in `Collapse`, 3 in `BakerGillSolovay` (`grep -c` on the log). The
run printed `audit done: 1642 constants, 712 named, 18 named in new modules` and exited 0.

**(b) Literal `#print axioms` on each of the 18 named declarations of the new modules**
(`logs/session7-print-axioms.txt`, 18 output lines, 0 errors, `exit: 0`). Distribution
(`sed -E "s/^'[^']*' //" | sort | uniq -c`):

```
     17 depends on axioms: [propext, Classical.choice, Quot.sound]
      1 depends on axioms: [propext, Quot.sound]
```

`grep -c sorryAx` on both logs prints `0` and `0`. The whole file:

```
'Relativization.Collapse.Acc_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.eval_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.exists_exponents' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.muPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.muPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padFun_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.Collapse.padPoly_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.OTM2OutputsInTime.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.eval_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.exists_pad_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inNP_subset_inP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.inP_of_pad_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.pow_weaken' depends on axioms: [propext, Quot.sound]
'Relativization.separation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.univOracle_pEqNP' depends on axioms: [propext, Classical.choice, Quot.sound]
exit: 0
```

**(c) Banned-token scan** over `Relativization.lean` and `Relativization/*.lean`, the same three
scans as §7.5 (c) (`logs/session7-scan.txt`):

```
== banned tokens (whole word) in project Lean sources ==
grep exit: 1 (1 = no match)
== metaprogramming / environment-modifying markers ==
grep exit: 0
== opaque / unsafeCast / debug markers ==
grep exit: 1
```

The marker scan's hits are the nineteen lines of §11.5 (c) and §12.5 (c) in earlier files,
unchanged and omitted here; **no line of `Collapse.lean` or `BakerGillSolovay.lean` is a hit**
(`grep -c "Collapse\|BakerGillSolovay" logs/session7-scan.txt` prints `0`).

**(d) `lake build`**, after deleting this project's own build artifacts
(`.lake/build/lib/lean/Relativization*`, `.lake/build/ir/Relativization*`) so that every module
was recompiled (`logs/session7-build.txt`; `grep -c -i -E "warning|error"` on it prints
`0`; `grep -c "Built Relativization"` prints `22`, the twenty-one modules
and the root):

```
✔ [1339/1342] Built Relativization.Collapse (34s)
✔ [1340/1342] Built Relativization.BakerGillSolovay (24s)
✔ [1341/1342] Built Relativization (25s)
Build completed successfully (1342 jobs).

real	6m57.649s
user	0m0.031s
sys	0m0.062s
exit: 0
```

The single-file checks `lake env lean Relativization/Collapse.lean` and
`lake env lean Relativization/BakerGillSolovay.lean` print nothing (exit 0, about 68 s and
27 s).

**(e) Earlier modules elaborate unchanged.** SHA-256 of each session 1–6 `.olean` before any
change of this session (`logs/session7-olean-before.txt`) and after the from-scratch rebuild
with the new modules present (`logs/session7-olean-after.txt`):

```
== olean hashes: earlier modules, before vs after the from-scratch rebuild ==
*Classes.olean SAME 43f4554b909236c7463f66a59da5add30adb3f4084b8e48de414a2381efe3896
*Codes.olean SAME c5e2c117e4ebe67f687ef83b1d8d2573830c2ad11aeb4b589ea22c352fd1bb8e
*Comp.olean SAME c560c3c025efabecdee7f093bf9946eaf00f2e9cfa03fd52ce3836bea892daf8
*Count.olean SAME 3221435b3f6dad351b0e01a73d991c923b6e25a3ee05ca4c4077825178625568
*Countable.olean SAME d4012351737c0774a51826920bd5e637f07d5c135cc3b929966dc5d08aa6e351
*Counter.olean SAME 0e1120a345818dfe98fdec7c43a9c0ea4c5e35e03d1d76b1f59588b01a11d6fc
*Emb.olean SAME 7203cedb57039239eb3735ee203b3d00d4b141f5e6974c8f1bbda90077a0b42f
*Frame.olean SAME 07be8f33280c713459299e3942a46a5695c7c61173af4b5cc506f7f81fce0382
*Halt.olean SAME bbec64145c811dcfdf6c5f1be0683a461b4c9478cf354a31201ecda23db125b5
*Normal.olean SAME 292ec4f641ebb808ff8e37075405b7dea60e9f5ae22bf307e2a8b327de47c0a3
*Oracle.olean SAME aba34f40f7e4fc0812b4a80bc0a42d472770e255cd15ff572793f04a5f8751da
*Pad.olean SAME a893514d9d9a7b9ee198efefd4a46a9bc59129eb29f5f01884c43c5670167c6f
*Plain.olean SAME 538a20892c70be803e666d35140c75b811aca5ba27aa95032ef8ac94dc690561
*Prog.olean SAME 9f91d8f0624f08e0a079ce2712a2bd5ec7f5d67053fa115d27386cc3a7b3ff7b
*Queries.olean SAME 55dd84a847e3354d80daf7abe0563cc75fe312bd57ce7cc790c6a5dfdc58b7da
*Self.olean SAME 2a154bef41f5362745a35ac188e0624a5afe435ffd3a9df2bad3f959aa019753
*Sep.olean SAME b004c415b234932d33d7025328c104416eb924f01af127fc757bbe872dc72280
*Stage.olean SAME ddb07f381ae1823929f6b436b631bea29cd76e27762072058fbe49242581761b
*Univ.olean SAME 764ce3af55c8fd6bd56c16f1e848abff8cb19541e398c8a99c19849247480cb5
new modules:
f774511c9685aead9b9424ae052c1dd0a8b8f9e434af54200724477929d21a57 *BakerGillSolovay.olean
144ce2423f0a2a0e4eb077be46dbe5a98083e73bce81f58ca77d3b523f33ed2e *Collapse.olean
```

(The first eighteen values are those of `logs/session6-olean-after.txt`; that of `Pad` is new in
the "before" file, taken before any change of this session.)

`lake env leanchecker --fresh` was not run this session (§13.4 item 8).
