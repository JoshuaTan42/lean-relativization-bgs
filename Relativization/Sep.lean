import Relativization.Prog
import Relativization.Comp
import Relativization.Self

/-!
# The separating language is in `NP^B`

* `Sep.revTM`, `Sep.revComputable` (B1): the plain one-loop machine computing
  `(w, y) ↦ (w ++ y).reverse` on the `pair_encoding` of two binary strings, in `|w#y| + 1` steps;
* `sepLang B := {w | ∃ y, |y| ≤ |w| ∧ y.reverse ++ w.reverse ∈ B}` (PLAN §4.2);
* `sepLang_inNP` (B2): `sepLang B ∈ NP^B` for every oracle `B`, with certificate alphabet `Bool`,
  exponent `1`, and the verifier `oracleComp B revComputable (T3 machine)`.
-/

namespace Relativization

open Turing StateTransition Function Computability Millennium Prog

namespace Sep

/-- Stack alphabets: the input stack `false` holds the `pair_encoding` alphabet
`Bool ⊕ Option Bool`; the output stack `true` holds bits. -/
abbrev RΓ : Bool → Type
  | false => Bool ⊕ Option Bool
  | true => Bool

/-- The state: the symbol just popped from the input (`none` at the start and at the end). -/
abbrev Rσ := Option (Bool ⊕ Option Bool)

/-- The bit carried by an input symbol; the separator `inr none` carries none. -/
def sym : Bool ⊕ Option Bool → Option Bool
  | .inl b => some b
  | .inr o => o

/-- Did the popped symbol carry a bit? -/
def hasBit (v : Rσ) : Bool := (v.bind sym).isSome

/-- The bit to push (`false` is a junk value, never pushed). -/
def bitOf (v : Rσ) : Bool := (v.bind sym).getD false

/-- The program of the single label: pop the input; if nothing was popped, halt; if the popped
symbol carries a bit, push it on the output; loop. -/
def prog : Unit → TM2.Stmt RΓ Unit Rσ := fun _ =>
  .pop false (fun _ o => o) <|
    .branch Option.isSome
      (.branch hasBit (.push true bitOf (.goto fun _ => ())) (.goto fun _ => ()))
      .halt

/-- The machine computing `(w, y) ↦ (w ++ y).reverse`. -/
def revTM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := RΓ
  Λ := Unit
  main := ()
  σ := Rσ
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Option Bool))
  m := prog

/-- Stacks of `revTM` from the input and the output. -/
def mk (i : List (Bool ⊕ Option Bool)) (o : List Bool) : ∀ k : Bool, List (RΓ k)
  | false => i
  | true => o

theorem update_mk_false (i i' : List (Bool ⊕ Option Bool)) (o : List Bool) :
    update (mk i o) false i' = mk i' o := by
  funext k; cases k <;> simp [mk]

theorem update_mk_true (i : List (Bool ⊕ Option Bool)) (o o' : List Bool) :
    update (mk i o) true o' = mk i o' := by
  funext k; cases k <;> simp [mk]

/-- The bits of an input string: `w#y ↦ w ++ y`. -/
def bits (u : List (Bool ⊕ Option Bool)) : List Bool := u.filterMap sym

theorem bits_cons (x : Bool ⊕ Option Bool) (u : List (Bool ⊕ Option Bool)) :
    bits (x :: u) = (sym x).toList ++ bits u := by
  unfold bits
  cases h : sym x
  · rw [List.filterMap_cons_none h]; rfl
  · rw [List.filterMap_cons_some h]; rfl

theorem bits_encode (w y : List Bool) :
    bits (w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b))) = w ++ y := by
  simp [bits, List.filterMap_append, List.filterMap_cons_none, List.filterMap_map, sym]

/-- One step on empty input: halt. -/
theorem step_nil (v : Rσ) (o : List Bool) :
    TM2.step prog (⟨some (), v, mk [] o⟩ : TM2.Cfg RΓ Unit Rσ) = some ⟨none, none, mk [] o⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mk, update_mk_false]

/-- One step on nonempty input: pop the symbol and push its bit, if any. -/
theorem step_cons (v : Rσ) (x : Bool ⊕ Option Bool) (i : List (Bool ⊕ Option Bool))
    (o : List Bool) :
    TM2.step prog (⟨some (), v, mk (x :: i) o⟩ : TM2.Cfg RΓ Unit Rσ) =
      some ⟨some (), some x, mk i ((sym x).toList ++ o)⟩ := by
  rcases x with b | _ | b <;>
    simp [TM2.step, prog, TM2.stepAux, mk, hasBit, bitOf, sym, update_mk_false, update_mk_true]

/-- The loop: `|u| + 1` steps from input `u` to the halting configuration with output
`(bits u).reverse` on top of `o`. -/
theorem loop_run (u : List (Bool ⊕ Option Bool)) :
    ∀ (v : Rσ) (o : List Bool),
      Run prog (u.length + 1) (⟨some (), v, mk u o⟩ : TM2.Cfg RΓ Unit Rσ)
        ⟨none, none, mk [] ((bits u).reverse ++ o)⟩ := by
  induction u with
  | nil =>
      intro v o
      exact Run.head (step_nil v o) (Run.zero _)
  | cons x u ih =>
      intro v o
      have h := ih (some x) ((sym x).toList ++ o)
      have e : (bits u).reverse ++ ((sym x).toList ++ o) = (bits (x :: u)).reverse ++ o := by
        rw [bits_cons, List.reverse_append, List.append_assoc]
        cases sym x <;> rfl
      rw [e] at h
      exact (Run.head (step_cons v x u o) h).of_eq (by simp)

theorem initList_eq (i : List (Bool ⊕ Option Bool)) :
    initList revTM i = ⟨some (), none, mk i []⟩ := by
  simp only [initList]
  congr 1
  funext k
  cases k <;> simp [revTM, mk]

theorem haltList_eq (o : List Bool) : haltList revTM o = ⟨none, none, mk [] o⟩ := by
  simp only [haltList]
  congr 1
  funext k
  cases k <;> simp [revTM, mk]

/-- `revTM` on `w#y` reaches the halting configuration with output `(w ++ y).reverse` in
`|w#y| + 1` steps. -/
theorem revTM_run (w y : List Bool) :
    Run revTM.m
      ((w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b))).length + 1)
      (initList revTM (w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b))))
      (haltList revTM (w ++ y).reverse) := by
  rw [initList_eq, haltList_eq]
  have h := loop_run (w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b))) none []
  rw [bits_encode, List.append_nil] at h
  exact h

/-- **B1.** `(w, y) ↦ (w ++ y).reverse` is computable in polynomial time (`X + 1`) on the
`pair_encoding` of two binary strings. -/
noncomputable def revComputable :
    TM2ComputableInPolyTime
      (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Bool)).encode
      (fin_encoding_string Bool).encode
      (fun p : List Bool × List Bool => (p.1 ++ p.2).reverse) where
  tm := revTM
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + Polynomial.C 1
  outputsFun p := by
    obtain ⟨w, y⟩ := p
    have key : ∀ (l : List (revTM.Γ revTM.k₀)) (l' : List (revTM.Γ revTM.k₁)) (n : ℕ),
        l = w.map Sum.inl ++ Sum.inr none :: y.map (fun b => Sum.inr (some b)) →
        l' = (w ++ y).reverse → l.length + 1 ≤ n → TM2OutputsInTime revTM l (some l') n := by
      rintro l l' n rfl rfl hn
      exact TM2OutputsInTime.ofRun (revTM_run w y) hn
    refine key _ _ _ ?_ ?_ ?_
    · exact List.map_id _
    · exact List.map_id _
    · simp [pair_encoding.length_eq]

end Sep

/-- The separating language: `w` is in it iff some certificate `y` no longer than `w` has
`y.reverse ++ w.reverse` in the oracle (PLAN §4.2). -/
def sepLang (B : Oracle) : Language (List Bool) :=
  fun w => ∃ y : List Bool, y.length ≤ w.length ∧ y.reverse ++ w.reverse ∈ B

/-- **B2.** `sepLang B ∈ NP^B` for every oracle `B`. -/
theorem sepLang_inNP (B : Oracle) : InNP B (fin_encoding_string Bool) (sepLang B) := by
  obtain ⟨g, hg, hgB⟩ := oracle_inP B
  refine ⟨Bool, inferInstance, fun w y => y.reverse ++ w.reverse ∈ B, 1,
    ⟨fun p => g ((p.1 ++ p.2).reverse), oracleComp B Sep.revComputable hg, fun p => ?_⟩,
    fun w => ?_⟩
  · show p.2.reverse ++ p.1.reverse ∈ B ↔ g ((p.1 ++ p.2).reverse) = true
    rw [List.reverse_append]
    exact hgB _
  · exact ⟨fun ⟨y, hy, h⟩ => ⟨y, by rw [pow_one]; exact hy, h⟩,
      fun ⟨y, hy, h⟩ => ⟨y, by rw [pow_one] at hy; exact hy, h⟩⟩

/-- For the separation (B6): on `0^n` the certificate is a prefix of length at most `n`. -/
theorem sepLang_replicate_iff (B : Oracle) (n : ℕ) :
    sepLang B (List.replicate n false) ↔
      ∃ u : List Bool, u.length ≤ n ∧ u ++ List.replicate n false ∈ B := by
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y.reverse, by simpa using hy, by simpa using h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u.reverse, by simpa using hu, by simpa using h⟩

end Relativization
