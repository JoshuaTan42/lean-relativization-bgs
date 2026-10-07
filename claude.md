# Relativization — project rules

Goal: a machine-checked proof of the Baker-Gill-Solovay theorem in Lean 4 + Mathlib:
there is an oracle A with P^A = NP^A and an oracle B with P^B ≠ NP^B.

Related finished project (read-only, never modify): `D:\PvsNP`.

## Rules

1. **No escape hatches in anything marked proved.** No `sorry`, `admit`, `axiom`,
   `native_decide`, `implemented_by`, `extern`, `unsafe`, `partial`, or
   environment-modifying metaprogramming. Finished results must show only
   `propext`, `Classical.choice`, `Quot.sound` under `#print axioms`.
2. **State before proving.** Every theorem is stated in `NOTES.md` before it is proved.
3. **Lakefile is frozen after initial setup.** Ask before any lakefile change;
   print the diff and stop.
4. **Nothing on C:.** Never install toolchains, clones or caches on C:.
   Check free space before any download or build over 1 GB; stop if it would
   leave less than 10 GB free.
5. **No unverified claims.** Never claim a command ran unless it ran; quote the output.
