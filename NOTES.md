# NOTES — Baker-Gill-Solovay in Lean 4 + Mathlib

Working notes. `PLAN.md` holds the approved plan; this file holds the statements (rule 2), the
paper proofs, the lemma table and the check outputs.

Status legend: **stated** = written here, no Lean proof; **proved** = Lean proof compiled and
axiom-checked (output quoted in §7 or §8). Nothing is committed.

Contents: §1 setup record · §2 definitions · §3 target statements · §4 statements for sessions 1 and 2 ·
§5 paper proof of the collapse oracle · §6 literature · §7 lemma table and checks (session 1) ·
§8 lemma table and checks (session 2).

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

## 4. Statements, written before the Lean proofs (§4.1–4.4 session 1; §4.5–4.7 session 2)

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
