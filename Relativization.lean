import Relativization.Oracle
import Relativization.Classes
import Relativization.Plain
import Relativization.Self
import Relativization.Comp
import Relativization.Halt
import Relativization.Countable
import Relativization.Normal
import Relativization.Codes
import Relativization.Prog
import Relativization.Emb
import Relativization.Sep
import Relativization.Count
import Relativization.Queries
import Relativization.Stage
import Relativization.Frame
import Relativization.Univ
import Relativization.Counter
import Relativization.Pad

/-!
# Baker-Gill-Solovay

Root module. Session 1 (foundations and faithfulness checks):

* `Relativization.Oracle`: the oracle machine model and query locality;
* `Relativization.Classes`: `P^A`, `NP^A`;
* `Relativization.Plain`: plain machines as oracle machines, and the empty oracle;
* `Relativization.Self`: `A ∈ P^A`;
* `Relativization.Comp`: plain-then-oracle composition, and `P^A ⊆ NP^A`.

Session 2 (normal form and unique output):

* `Relativization.Halt`: halting configurations are terminal; unique output (F4);
* `Relativization.Countable`: `TM2.Stmt` over finite data is countable (N1);
* `Relativization.Normal`: `NFMachine`, the normal form of an oracle machine and its step-for-step
  simulation (N3);
* `Relativization.Codes`: decider and verifier codes, their enumerations (N2), and the codes of
  deciders and verifiers (N4).

Session 3 (program library and the separating language):

* `Relativization.Prog`: the `TM2` program library ported from PvsNP, with the transfer of plain
  runs to oracle runs;
* `Relativization.Emb`: stack embedding of a sub-machine into a host, ported from PvsNP, with an
  oracle-host version;
* `Relativization.Sep`: the machine `(w, y) ↦ (w ++ y).reverse` (B1), the separating language
  `sepLang` and `sepLang B ∈ NP^B` (B2).

Session 4 (the stage construction):

* `Relativization.Count`: the counting lemmas (B3): fewer than `2^n` strings miss some
  `u ++ 0^n`, and every polynomial is eventually below `2^n`;
* `Relativization.Queries`: the finite set of queries asked by a run, and the instance of the
  sharp locality lemma L4 the stages use;
* `Relativization.Stage`: the stages and the oracle `sepOracle` (B4), run stability (B5), and
  `sepLang sepOracle ∉ P^sepOracle`, `¬ PEqNP sepOracle` (B6).

Session 5 (the collapse oracle):

* `Relativization.Frame`: the frames `1^i 0 1^T 0 v` and their decoding (A1);
* `Relativization.Univ`: the oracle `univOracle` by levels, with the self-referential equation
  `x ∈ A ↔ Phi A x` and its uniqueness (A2);
* `Relativization.Counter`: the counter view of `TM2` machines and the unary power loop, ported
  from PvsNP (A3).

Session 6 (the pad machine):

* `Relativization.Pad`: `padFun i c' d w = frame i ((|w| + c')^d) w.reverse` and the plain
  polynomial-time machine computing it, `Pad.padComputable` (A4), built from the copy loop, the
  counter view and the power loop embedded into the host with `Emb.runLe_embed`.

See `NOTES.md` for statements, the lemma table and check outputs; `PLAN.md` for the plan.
-/
