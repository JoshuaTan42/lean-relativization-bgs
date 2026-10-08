import Relativization.Frame
import Relativization.Counter
import Relativization.Emb
import Relativization.Classes

/-!
# The pad machine (A4)

`padFun i c' d w = frame i ((|w| + c')^d) w.reverse` is the padding function of the collapse
proof (`NOTES.md` §4.12, §5.7): the reduction `L w ↔ padFun i c' d w ∈ univOracle` of A5 goes
through it. This file builds a plain `FinTM2` computing it in polynomial time:

* `Pad.padTM i c' d`: a host machine with an input stack `inp` and the stacks of the counter
  view (A3), a Bool output stack and six unit counters. The copy loop (label `rd`, hand-written
  as `Sep.revTM` was) moves the input to the output, reversing it, and counts it; the counter
  sub-machine `Pad.cprog i c' d` (a program of the counter view, run with A3's wrappers:
  `emitOut`, `emitS`, `pow_run`, `xferES`, `drainS`) computes `(|w| + c')^d` in unary and emits
  the frame around the reversed input. The sub-machine is embedded into the host with
  `Emb.runLe_embed` (route E of §4.12; PvsNP `Pre.lean` `[FULL]`/`[COMP]`/`[REAL]` is the
  template);
* `Pad.pad_run`: from `initList (padTM i c' d) w` the machine reaches
  `haltList (padTM i c' d) (padFun i c' d w)` within `padB c' d |w|` steps;
* `Pad.padComputable i c' d : TM2ComputableInPolyTime … (padFun i c' d)` (**A4**), with the
  polynomial obtained from `IsPoly (padB c' d)`.

`IsPoly` and its closure lemmas are PvsNP `Pre.lean` 717–735, verbatim.
-/

namespace Relativization

open Turing Function Computability Millennium Prog Counter Emb

/-- `padFun i c' d w = frame i ((|w| + c')^d) w.reverse = 1^i 0 1^{(|w| + c')^d} 0 w.reverse`. -/
def padFun (i c' d : ℕ) (w : List Bool) : List Bool :=
  frame i ((w.length + c') ^ d) w.reverse

/-! ## [POLY] Polynomial step bounds (PvsNP `Pre.lean` `[POLY]`, verbatim) -/

/-- `f` is (pointwise) the evaluation of a polynomial with natural coefficients. -/
def IsPoly (f : ℕ → ℕ) : Prop := ∃ p : Polynomial ℕ, ∀ n, f n = p.eval n

namespace IsPoly

theorem const (a : ℕ) : IsPoly fun _ => a := ⟨Polynomial.C a, fun _ => by simp⟩

theorem id : IsPoly fun n => n := ⟨Polynomial.X, fun _ => by simp⟩

theorem add {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n + g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p + q, fun n => by simp [hp, hq]⟩

theorem mul {f g : ℕ → ℕ} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun n => f n * g n := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg; exact ⟨p * q, fun n => by simp [hp, hq]⟩

theorem pow {f : ℕ → ℕ} (hf : IsPoly f) (j : ℕ) : IsPoly fun n => f n ^ j := by
  obtain ⟨p, hp⟩ := hf; exact ⟨p ^ j, fun n => by simp [hp]⟩

end IsPoly

namespace Pad

/-! ## [DEF] Counters, stacks, labels, programs, the machine -/

/-- The six unit counters: `b` (the base `|w| + c'`), `kc` (exponent countdown), `p` (the power),
`q`, `ad`, `t` (scratch of the power loop). -/
inductive PC | b | kc | p | q | ad | t
  deriving DecidableEq, Fintype

/-- Stacks of the pad machine: the input, and the stacks of the counter view. -/
inductive PK | inp | cv (k : SK PC)
  deriving DecidableEq, Fintype

/-- Stack alphabets: bits on the input, the counter view's alphabets elsewhere. -/
abbrev PΓ : PK → Type
  | .inp => Bool
  | .cv k => SΓ PC k

/-- Labels of the counter sub-machine. -/
inductive CL | sep1 | addc | one | exp | pw (s : PW) | emitT | sep2 | drn | fin
  deriving DecidableEq, Fintype

/-- Labels of the pad machine: the copy loop, and the sub-machine's labels. -/
inductive PL | rd | cp (l : CL)
  deriving DecidableEq, Fintype

/-- **The counter sub-machine.** From `out = v`, `b = n`, all else `0`: prepend `0`; `b += c'`;
`p = 1`; `kc = d`; `p ← p · b^kc` (the power loop of A3); prepend `1^p` and drain `p`; prepend
`1^i 0`; drain `b`; halt. -/
def cprog (i c' d : ℕ) : CL → TM2.Stmt (SΓ PC) CL Bool
  | .sep1 => emitR .out [false] .addc
  | .addc => emitR (.c .b) (List.replicate c' ()) .one
  | .one => emitR (.c .p) (List.replicate 1 ()) .exp
  | .exp => emitR (.c .kc) (List.replicate d ()) (.pw .hd)
  | .pw s => powS .b .kc .p .q .ad .t CL.pw .emitT s
  | .emitT => xferE (.c .p) .out [true] .emitT .sep2
  | .sep2 => emitR .out (List.replicate i true ++ [false]) .drn
  | .drn => xfer (.c .b) [] .drn .fin
  | .fin => .halt

/-- The counter view's stacks inside the pad machine. -/
def padEmb : SEmb (SΓ PC) PΓ where
  e := PK.cv
  inj := fun _ _ h => by cases h; rfl
  ι := fun _ => Equiv.refl _

/-- **The copy loop** (one label, one step per bit). Peek the input: if a bit is there, pop it
into the state, push it on the output and one unit on `b`, loop; if the input is empty, start
the sub-machine. -/
def rdStmt : TM2.Stmt PΓ PL Bool :=
  .peek .inp (fun _ o => o.isSome) <| .branch id
    (.pop .inp (fun _ o => o.getD false) <| .push (.cv .out) (fun v => v) <|
      .push (.cv (.c .b)) (fun _ => ()) <| .goto fun _ => .rd)
    (.goto fun _ => .cp .sep1)

/-- **The pad machine's program**: the copy loop at `rd`, the embedded sub-machine at `cp l`. -/
def pprog (i c' d : ℕ) : PL → TM2.Stmt PΓ PL Bool
  | .rd => rdStmt
  | .cp l => mapS padEmb PL.cp (cprog i c' d l)

/-- **The pad machine**: input stack `inp`, output stack `cv .out`, states `Bool`. -/
def padTM (i c' d : ℕ) : FinTM2 where
  K := PK
  k₀ := .inp
  k₁ := .cv .out
  Γ := PΓ
  Λ := PL
  main := .rd
  σ := Bool
  initialState := false
  m := pprog i c' d

/-- Step bound of the pad machine on an input of length `n` (`i` does not enter). -/
def padB (c' d n : ℕ) : ℕ := 2 * n + c' + 9 + powB d 1 (n + c') + (n + c') ^ d

/-! ## [CNT] The counter sub-machine's run -/

/-- All counters zero. -/
def F0 : PC → ℕ := fun _ => 0

/-- After the copy loop: `b = n`. -/
def F1 (n : ℕ) : PC → ℕ
  | .b => n
  | _ => 0

/-- Before the power loop: `b = n + c'`, `kc = d`, `p = 1`. -/
def F2 (c' d n : ℕ) : PC → ℕ
  | .b => n + c'
  | .kc => d
  | .p => 1
  | _ => 0

/-- After the power loop: `b = n + c'`, `p = (n + c')^d`. -/
def F3 (c' d n : ℕ) : PC → ℕ
  | .b => n + c'
  | .p => (n + c') ^ d
  | _ => 0

/-- Step budget of the sub-machine. -/
def cB (c' d n : ℕ) : ℕ := 4 + powB d 1 (n + c') + ((n + c') ^ d + 1) + 1 + (n + c' + 1)

theorem rep_singleton {α : Type} (a : α) : ∀ n, rep [a] n = List.replicate n a
  | 0 => rfl
  | n + 1 => by rw [rep_succ, rep_singleton a n]; rfl

/-- **The sub-machine's run**: from `out = o`, `b = n`, it reaches `fin` with
`out = frame i ((n + c')^d) o` and every counter `0`, within `cB c' d n` steps. -/
theorem cprog_run (i c' d n : ℕ) (v : Bool) (o : List Bool) :
    RunLe (cprog i c' d) (cB c' d n) ⟨some .sep1, v, st (F1 n) o⟩
      ⟨some .fin, false, st F0 (frame i ((n + c') ^ d) o)⟩ := by
  refine Bud.start ?_
  refine (emitOut (M := cprog i c' d) (self := .sep1) (next := .addc) rfl _ _ _).bud ?_
  refine (emitS (M := cprog i c' d) (self := .addc) (next := .one) rfl _ _ _).bud ?_
  refine (emitS (M := cprog i c' d) (self := .one) (next := .exp) rfl _ _ _).bud ?_
  refine (emitS (M := cprog i c' d) (self := .exp) (next := .pw .hd) rfl _ _ _).bud ?_
  refine bud_st (F' := F2 c' d n) (by
    funext z; cases z <;> simp [F1, F2]; omega) ?_
  refine (pow_run (M := cprog i c' d) (mk := CL.pw) (exit := .emitT) (fun _ => rfl) (by decide) d
    _ (by simp [F2]) (by simp [F2]) (by simp [F2]) (by simp [F2]) _ _).bud ?_
  refine bud_st (F' := F3 c' d n) (by
    funext z; cases z <;> simp [F2, F3]) ?_
  refine (xferES (M := cprog i c' d) (self := .emitT) (next := .sep2) rfl _ _ _).bud ?_
  refine (emitOut (M := cprog i c' d) (self := .sep2) (next := .drn) rfl _ _ _).bud ?_
  refine (drainS (M := cprog i c' d) (self := .drn) (next := .fin) rfl _ _ _).bud ?_
  refine Bud.fin ?_ ?_
  · simp [F2, F3, cB]
  · congr 2
    · funext z; cases z <;> simp [F3, F0]
    · simp [frame, rep_singleton, F3]

/-! ## [RD] The copy loop -/

/-- Stacks of the pad machine: the input `s`, the counters `F`, the output `o`. -/
def pst (s : List Bool) (F : PC → ℕ) (o : List Bool) : ∀ k, List (PΓ k)
  | .inp => s
  | .cv k => st F o k

theorem update_pst_inp (s s' : List Bool) (F : PC → ℕ) (o : List Bool) :
    update (pst s F o) .inp s' = pst s' F o := by
  funext k
  rcases k with _ | k
  · rw [update_self]; rfl
  · rw [update_of_ne (by simp)]; rfl

theorem update_pst_cv (s : List Bool) (F : PC → ℕ) (o : List Bool) (k₀ : SK PC)
    (l : List (SΓ PC k₀)) (k : SK PC) :
    update (pst s F o) (.cv k₀) l (.cv k) = update (st F o) k₀ l k := by
  by_cases h : k = k₀
  · subst h; simp
  · rw [update_of_ne (by simpa using h), update_of_ne h]; rfl

theorem update_pst_out (s : List Bool) (F : PC → ℕ) (o o' : List Bool) :
    update (pst s F o) (.cv .out) o' = pst s F o' := by
  funext k
  rcases k with _ | k
  · rw [update_of_ne (by simp)]; rfl
  · show update (pst s F o) (.cv .out) o' (.cv k) = st F o' k
    rw [update_pst_cv, update_st_out]

theorem update_pst_c (s : List Bool) (F : PC → ℕ) (o : List Bool) (x : PC) (n : ℕ) :
    update (pst s F o) (.cv (.c x)) (cnt () n : List (SΓ PC (.c x))) = pst s (update F x n) o := by
  funext k
  rcases k with _ | k
  · rw [update_of_ne (by simp)]; rfl
  · show update (pst s F o) (.cv (.c x)) (cnt () n) (.cv k) = st (update F x n) o k
    rw [update_pst_cv, update_st_c]

theorem cons_cnt {α : Type} (u : α) (n : ℕ) : u :: cnt u n = cnt u (n + 1) := rfl

/-- One step of the copy loop on a nonempty input. -/
theorem stepAux_rd_cons (v x : Bool) (s : List Bool) (F : PC → ℕ) (o : List Bool) :
    TM2.stepAux rdStmt v (pst (x :: s) F o) =
      ⟨some .rd, x, pst s (update F .b (F .b + 1)) (x :: o)⟩ := by
  simp only [rdStmt, TM2.stepAux, pst, List.head?_cons, Option.isSome_some, id, cond_true,
    List.tail_cons, Option.getD_some, update_pst_inp, st_out, update_pst_out, st_c, cons_cnt]
  rw [update_pst_c]

/-- The exit step of the copy loop. -/
theorem stepAux_rd_nil (v : Bool) (F : PC → ℕ) (o : List Bool) :
    TM2.stepAux rdStmt v (pst [] F o) = ⟨some (.cp .sep1), false, pst [] F o⟩ := by
  simp only [rdStmt, TM2.stepAux, pst, List.head?_nil, Option.isSome_none, id, cond_false]

/-- **The copy loop's run**: `|s| + 1` steps; afterwards the input is empty, the output is
`s.reverse ++ o` and `b` has grown by `|s|`. -/
theorem rd_run (i c' d : ℕ) (s : List Bool) :
    ∀ (v : Bool) (F : PC → ℕ) (o : List Bool),
      Run (pprog i c' d) (s.length + 1) ⟨some .rd, v, pst s F o⟩
        ⟨some (.cp .sep1), false, pst [] (update F .b (F .b + s.length)) (s.reverse ++ o)⟩ := by
  induction s with
  | nil =>
      intro v F o
      have h := Run.single (M := pprog i c' d) (l := .rd) (stepAux_rd_nil v F o)
      simpa using h
  | cons x s ih =>
      intro v F o
      have h := ih x (update F .b (F .b + 1)) (x :: o)
      have e1 : update (update F .b (F .b + 1)) .b (update F .b (F .b + 1) .b + s.length) =
          update F .b (F .b + (x :: s).length) := by
        rw [update_self, update_idem, List.length_cons]
        congr 1
        omega
      have e2 : s.reverse ++ x :: o = (x :: s).reverse ++ o := by simp
      rw [e1, e2] at h
      refine Run.head ?_ h
      show TM2.step (pprog i c' d) _ = _
      simp only [TM2.step, pprog, stepAux_rd_cons]

/-! ## [EMB] The sub-machine inside the host -/

theorem embeds (i c' d : ℕ) : Embeds padEmb PL.cp (cprog i c' d) (pprog i c' d) :=
  fun _ => Or.inl rfl

theorem agree (s : List Bool) (F : PC → ℕ) (o : List Bool) : Agree padEmb (st F o) (pst s F o) :=
  fun _ => (List.map_id _).symm

/-- Host stacks agreeing with `st F' o'` on the counter view and unchanged on the input are
`pst s F' o'`. -/
theorem eq_pst_of_agree {F' : PC → ℕ} {o' : List Bool} {T' : ∀ k, List (PΓ k)} (s : List Bool)
    (F : PC → ℕ) (o : List Bool) (hA : Agree padEmb (st F' o') T')
    (hF : Emb.Frame padEmb (pst s F o) T') : T' = pst s F' o' := by
  funext k
  rcases k with _ | k
  · exact hF .inp (fun k => by simp [padEmb])
  · exact (hA k).trans (List.map_id _)

/-! ## [RUN] The whole machine -/

theorem initList_pad (i c' d : ℕ) (w : List Bool) :
    initList (padTM i c' d) w = ⟨some .rd, false, pst w F0 []⟩ := by
  simp only [initList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · rcases k with _ | x <;> rfl

theorem haltList_pad (i c' d : ℕ) (l : List Bool) :
    haltList (padTM i c' d) l = ⟨none, false, pst [] F0 l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · rcases k with _ | x <;> rfl

/-- **Correctness and time.** From `initList (padTM i c' d) w` the pad machine reaches
`haltList (padTM i c' d) (padFun i c' d w)` within `padB c' d |w|` steps. -/
theorem pad_run (i c' d : ℕ) (w : List Bool) :
    RunLe (padTM i c' d).m (padB c' d w.length) (initList (padTM i c' d) w)
      (haltList (padTM i c' d) (padFun i c' d w)) := by
  rw [initList_pad, haltList_pad]
  show RunLe (pprog i c' d) _ _ _
  -- the copy loop
  have r1 := rd_run i c' d w false F0 []
  have e1 : update F0 .b (F0 .b + w.length) = F1 w.length := by
    funext z; cases z <;> simp [F0, F1]
  rw [e1, List.append_nil] at r1
  -- the embedded sub-machine
  obtain ⟨T', r2, hA, hF⟩ := runLe_embed (E := padEmb) PL.cp (embeds i c' d)
    (cprog_run i c' d w.length false w.reverse) (agree [] (F1 w.length) w.reverse)
  rw [eq_pst_of_agree [] (F1 w.length) w.reverse hA hF] at r2
  -- the halt
  have r3 : Run (pprog i c' d) 1
      ⟨some (.cp .fin), false, pst [] F0 (frame i ((w.length + c') ^ d) w.reverse)⟩
      ⟨none, false, pst [] F0 (frame i ((w.length + c') ^ d) w.reverse)⟩ :=
    Run.single (by simp [pprog, cprog, mapS, TM2.stepAux])
  have := ((r1.le le_rfl).trans r2).trans (r3.le le_rfl)
  refine this.mono ?_
  simp only [padB, cB]
  omega

/-! ## [PKG] `TM2ComputableInPolyTime` -/

theorem padB_poly (c' d : ℕ) : IsPoly (padB c' d) := by
  have hb : IsPoly fun n => n + c' := IsPoly.id.add (IsPoly.const c')
  unfold padB powB
  exact (((((IsPoly.const 2).mul IsPoly.id).add (IsPoly.const c')).add (IsPoly.const 9)).add
    (((IsPoly.const d).mul ((((IsPoly.const 1).mul ((hb.add (IsPoly.const 1)).pow d)).mul
      (((IsPoly.const 3).mul hb).add (IsPoly.const 5))).add (IsPoly.const 5))).add
      (IsPoly.const 1))).add (hb.pow d)

/-- **A4.** `padFun i c' d` is computable by a plain machine in polynomial time, on the identity
encoding of binary strings on both sides. -/
noncomputable def padComputable (i c' d : ℕ) :
    TM2ComputableInPolyTime (fin_encoding_string Bool).encode (fin_encoding_string Bool).encode
      (padFun i c' d) where
  tm := padTM i c' d
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Classical.choose (padB_poly c' d)
  outputsFun w := by
    have key : ∀ (l : List ((padTM i c' d).Γ (padTM i c' d).k₀))
        (l' : List ((padTM i c' d).Γ (padTM i c' d).k₁)) (n : ℕ),
        l = w → l' = padFun i c' d w → padB c' d w.length ≤ n →
        TM2OutputsInTime (padTM i c' d) l (some l') n := by
      rintro l l' n rfl rfl hn
      exact TM2OutputsInTime.ofRunLe ((pad_run i c' d l).mono hn)
    refine key _ _ _ ?_ ?_ ?_
    · exact List.map_id _
    · exact List.map_id _
    · exact (Classical.choose_spec (padB_poly c' d) w.length).le

end Pad

end Relativization
