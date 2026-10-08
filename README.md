# Baker-Gill-Solovay in Lean 4

**Claim.** Lean's kernel accepts a proof, using no axioms beyond `propext`, `Classical.choice`
and `Quot.sound`, that there is an oracle `A` with `P^A = NP^A` and an oracle `B` with
`P^B ≠ NP^B`, where `P^X` and `NP^X` are classes of binary languages defined on Mathlib's
`FinTM2` multi-stack machines with a binary query stack, and they coincide with the
LeanMillenniumPrizeProblems `P` and `NP` when the oracle is empty.

## The statement

`Relativization/BakerGillSolovay.lean:30`:

```lean
theorem baker_gill_solovay : (∃ A : Oracle, PEqNP A) ∧ (∃ B : Oracle, ¬ PEqNP B) :=
  ⟨collapse, separation⟩
```

with, in `Relativization/Oracle.lean` and `Relativization/Classes.lean`:

```lean
abbrev Oracle := Set (List Bool)

def PEqNP (A : Oracle) : Prop :=
  ∀ L : Language (List Bool),
    InP A (fin_encoding_string Bool) L ↔ InNP A (fin_encoding_string Bool) L
```

`InP A` and `InNP A` are `Millennium.InPolynomialTime` and
`Millennium.InNondeterministicPolynomialTime` written out word for word, with an oracle machine
(`OracleFinTM2`, `OTM2ComputableInPolyTime A`) in place of Mathlib's `TM2ComputableInPolyTime`.
An oracle machine is a `FinTM2` with an extra binary query stack. At every step its program
receives one bit, whether the current query stack is in `A`. The theorem has no hypotheses.
The witnesses are `univOracle` and `sepOracle`, and `PEqNP univOracle` and
`¬ PEqNP sepOracle` are proved on their own.

[`DEFINITIONS.md`](DEFINITIONS.md) quotes every definition the statement depends on, explains
the machine model and gives a plain-language reading. It also includes a restatement that uses
only plain machine steps, with instructions for checking it.

## What this is not

* **Not the recursive-oracle statement of the paper's abstract (F1).** Baker, Gill and Solovay's
  abstract says "We construct a recursive set A such that P^A = NP^A. On the other hand, we
  construct a recursive set B such that P^B ≠ NP^B", and they remark that their `A` is decidable
  in exponential time. The Lean statement has no decidability clause. The witness oracles are
  `noncomputable`: they are built from enumerations of machine codes obtained with
  `Classical.choose`. Nothing about their recursiveness or decidability is proved. What is
  proved matches Theorems 1 and 3 of the paper as printed, which do not mention recursiveness.
* **The machine model is not proved equivalent to the paper's (F2).** The paper uses multitape
  Turing machines with a query tape and query states, defines `NP^X` with nondeterministic
  machines, and requires the time bound under every oracle. Here an oracle answer bit is seen at
  every step, `NP^X` is defined by verifiers with certificates `|y| ≤ |w|^k`, and the time bound
  is required only under the given oracle. That these choices give the same relativized classes
  is a standard argument made on paper, **not proved in Lean**. The only machine-checked link to
  a standard definition is the empty-oracle case: `InP ∅ ea L ↔ InPolynomialTime ea L`,
  `InNP ∅ ea L ↔ InNondeterministicPolynomialTime ea L` and
  `ClassEquality ∅ ↔ ClayPVersusNP`, all in `Relativization/Plain.lean`.
* **Binary languages only (F3).** `PEqNP` quantifies over languages of binary strings, as in the
  paper. The relativized Clay form over every finite alphabet with at least two symbols,
  `ClassEquality A`, is defined in `Classes.lean` but **not proved** for the collapse oracle.
  (`¬ ClassEquality sepOracle` follows by taking `alphabet := Bool`. The red-team review proved
  this in a scratch file, `logs/redteam-src-RT3_Degenerate.lean.txt`, not in the repository.)
* Not a statement about P versus NP itself, and not a formalization of the rest of the 1975
  paper. In particular, Theorem 2 (a PSPACE-complete oracle gives `P^A = NP^A`) is not
  formalized. The witnesses are variants of the paper's constructions, not copies of them (see
  Credit).

[`REDTEAM.md`](REDTEAM.md) is a review of the statement by a separate session that had not
written the code. It lists these points as findings F1–F3, together with six informational ones
(F4–F9), and found no critical or major issues.

## Verifying

Requirements: [elan](https://github.com/leanprover/elan) and Git. Pinned versions:

* Lean `leanprover/lean4:v4.31.0` (`lean-toolchain`);
* Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`);
* LeanMillenniumPrizeProblems `603053dc267cf3efe422f438eb78098c0ececd6f`, of which only
  `Problems/PVersusNP/Millennium.lean` is imported.

Both are `[[require]]` entries in `lakefile.toml`. Every transitive dependency is pinned in
`lake-manifest.json`. LeanMillenniumPrizeProblems brings in Physlib, doc-gen4 and a few other
packages, which Lake clones but this project never imports.

```
git clone https://github.com/JoshuaTan42/lean-relativization-bgs.git
cd lean-relativization-bgs
lake exe cache get
lake build
```

The dependencies are Lake packages, not Git submodules, so no `git submodule` step is needed.
Lake clones them into `.lake/packages` on first use. `lake exe cache get` downloads Mathlib's
prebuilt files; without it, Lake builds Mathlib from source, which takes hours. The `.lake`
directory needs about 7 GB.

**Build.** `lake build` should finish with no warnings and no errors. Before the run in
`logs/session9-build.txt`, this project's own build files
(`.lake/build/lib/lean/Relativization*`, `.lake/build/ir/Relativization*`) were deleted, so all
22 modules were recompiled. The Mathlib and dependency builds were kept. The last lines:

```
✔ [1339/1342] Built Relativization.Collapse (17s)
✔ [1340/1342] Built Relativization.BakerGillSolovay (12s)
✔ [1341/1342] Built Relativization (12s)
Build completed successfully (1342 jobs).

real	2m48.178s
user	0m0.015s
sys	0m0.031s
exit: 0
```

`grep -c -i -E "warning|error"` on that log prints `0`. The rebuilt `.olean` files are
byte-identical to those built before (`logs/session9-olean.txt`, 22 lines `SAME`).

**Axioms.** Create a file `Check.lean` outside `Relativization/` containing

```lean
import Relativization
#print axioms Relativization.baker_gill_solovay
#print axioms Relativization.collapse
#print axioms Relativization.separation
```

and run `lake env lean Check.lean`. Output (`logs/session9-print-axioms.txt`):

```
'Relativization.baker_gill_solovay' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Relativization.separation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same line for `baker_gill_solovay` appears in `logs/session7-print-axioms.txt`. In this
Lean version, `#print axioms` reads axiom lists that are stored in the `.olean` files.
`REDTEAM.md` §4.3 confirms the same three axioms by walking the proof terms directly.

**Kernel replay.** `leanchecker` ships with the Lean toolchain. It replays declarations
through Lean's kernel to detect environment tampering. The session-8 review ran it on every
module and from an empty environment. These runs are on the `.lean` files of this commit:
`git diff 3d2d815 -- '*.lean'` is empty. From `logs/redteam-leanchecker-modules.txt` (all
modules, then each module one at a time; 22 lines `EXIT[…]=0`, none non-zero):

```
$ lake env leanchecker --verbose Relativization
replaying Relativization
replaying Relativization.Univ
…
replaying Relativization.BakerGillSolovay
LEANCHECKER_PREFIX_EXIT=0
…
$ lake env leanchecker --verbose Relativization.BakerGillSolovay
replaying Relativization.BakerGillSolovay
EXIT[Relativization.BakerGillSolovay]=0
$ lake env leanchecker --verbose Relativization
…
EXIT[Relativization]=0
```

From `logs/redteam-leanchecker-fresh.txt`. `--fresh` replays the whole import closure,
Mathlib and LeanMillenniumPrizeProblems included, from an empty environment:

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

(`EXIT…` lines are printed by the wrapper used for the run.) To repeat:
`lake env leanchecker Relativization.<Module>` for one module, and
`lake env leanchecker --fresh Relativization` for the whole closure (about 5 minutes on the
author's machine). `leanchecker` re-runs Lean's own kernel. It is not an independent
implementation (REDTEAM F5).

The source contains no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`,
`unsafe`, `partial`, `set_option` or metaprogramming commands, according to the comment- and
string-aware scan in REDTEAM §4.1.

## Files

| File | Contents |
|---|---|
| `Relativization/Oracle.lean` | the oracle machine model, query length and locality |
| `Relativization/Classes.lean` | `InP`, `InNP`, `PEqNP`, `ClassEquality` |
| `Relativization/Plain.lean` | plain machines as oracle machines; the empty-oracle theorems |
| `Relativization/Self.lean`, `Comp.lean` | `A ∈ P^A`; composition; `P^A ⊆ NP^A` |
| `Relativization/Halt.lean`, `Countable.lean`, `Normal.lean`, `Codes.lean` | unique output, countability, normal form, decider and verifier codes and their enumerations |
| `Relativization/Prog.lean`, `Emb.lean`, `Counter.lean` | program library, stack embedding and counter view for hand-written `TM2` machines |
| `Relativization/Sep.lean`, `Count.lean`, `Queries.lean`, `Stage.lean` | the separating language, counting, the queries of a run, the stage construction of `sepOracle` and `¬ PEqNP sepOracle` |
| `Relativization/Frame.lean`, `Univ.lean`, `Pad.lean`, `Collapse.lean` | frames, the self-referential `univOracle`, the pad machine, `PEqNP univOracle` |
| `Relativization/BakerGillSolovay.lean` | `collapse`, `separation`, `baker_gill_solovay` |
| `DEFINITIONS.md` | the exact definitions and a plain-language reading |
| `REDTEAM.md` | the session-8 review |
| `NOTES.md`, `PLAN.md` | statements written before each proof, paper proofs, plan and per-session check outputs |
| `logs/` | build, axiom, scan and `leanchecker` logs, and the review's scratch sources |

Some code is ported from the author's Cook-Levin development, which uses the same Millennium
definitions: `Prog.lean`, `Emb.lean` and most of `Counter.lean`, verbatim except for the
changes listed in each file's header, with new sections added; the composition machine of `Comp.lean`, adapted
to an oracle machine; and small marked sections of `Pad.lean` and `Collapse.lean`. The source is
[millennium-cook-levin](https://github.com/JoshuaTan42/millennium-cook-levin), commit
`c271016`. Each file's header says which parts are ported. The port diffs are in
`logs/session{3,5,6,7}-port-diff.txt`.

## Credit

The theorem is due to Theodore Baker, John Gill and Robert Solovay, "Relativizations of the
P =? NP question", *SIAM J. Comput.* 4(4), 1975, pp. 431–442. The two oracles here are variants
of the oracles of their Theorem 1 and Theorem 3:

* `univOracle` is a variant of Theorem 1's self-referential oracle `A = K(A)`. It codes triples
  as frames `1^i 0 1^T 0 v` and uses a step budget `⌊(T ∸ μ)/(D + 1)⌋`, so that queries stay
  shorter than the frame for machines that write several query symbols per step.
* `sepOracle` is a variant of Theorem 3's stage construction. Its separating language is
  `{w | ∃ y, |y| ≤ |w| ∧ y.reverse ++ w.reverse ∈ B}`, with added strings `u ++ 0^n` of length
  `2n`, instead of the paper's `L(B) = {x : ∃ y ∈ B, |y| = |x|}`.

The attribution was checked by reading a scanned copy of the paper (pp. 431–437) from a course
website, not SIAM's own copy (`REDTEAM.md` §6, `logs/redteam-6-literature.txt`).

## How this was made

The Lean code and the documentation were written by Claude Code agents (Anthropic's AI coding
tool) over a series of scoped sessions directed by the author. For each session the author set
the goal and the rules: no `sorry`, `axiom`, `native_decide` or environment-modifying
metaprogramming in proved code, and every statement written down in `NOTES.md` before it was
proved. The author also reviewed the session's report. The result is checked by Lean's kernel
(`lake build`, `#print axioms`), by `leanchecker`, and by an independent reviewer session
(`REDTEAM.md`). That reviewer was also a Claude Code agent, in a separate session that had not
written the code. `NOTES.md` records the development session by session.

## License

Copyright 2026 Joshua Tan. Licensed under the Apache License, Version 2.0; see `LICENSE`.
Mathlib and LeanMillenniumPrizeProblems (and their dependencies) are separate projects under
their own licenses.
