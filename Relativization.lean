import Relativization.Oracle
import Relativization.Classes
import Relativization.Plain
import Relativization.Self
import Relativization.Comp
import Relativization.Halt
import Relativization.Countable
import Relativization.Normal
import Relativization.Codes

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

See `NOTES.md` for statements, the lemma table and check outputs; `PLAN.md` for the plan.
-/
