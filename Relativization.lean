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

See `NOTES.md` for statements, the lemma table and check outputs; `PLAN.md` for the plan.
-/
