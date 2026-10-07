import Relativization.Codes
import Relativization.Halt
import Relativization.Sep
import Relativization.Count
import Relativization.Queries

/-!
# The stage construction: an oracle `B` with `sepLang B ∉ P^B`

Stage `i` takes the decider code `dEnum i` (machine `M i`, polynomial `p`), chooses a length
`n` above the current bound with `p.eval n < 2^n` (B3b), runs the machine on `0^n` under the
finite oracle built so far for `p.eval n` steps, picks a string `u ++ 0^n` with `|u| = n` that
the run did not query (B3a: at most `p.eval n < 2^n` queries), and adds it exactly when the run
did not output `[true]`. The next bound is `2n + p.eval n * depth`, above every query of the
run. `sepOracle` is the union of the stages (B4).

* `Stage.outputs_iff` (B5): the stage-`i` run is the run under `sepOracle` for its `p.eval n`
  steps (L4' of `Queries.lean`: the only string the two oracles may disagree on within the
  query-length bound is the one the stage chose unqueried);
* `sepLang_not_inP` (B6): `sepLang sepOracle ∉ P^sepOracle`; `sepOracle_not_pEqNP`.

`NOTES.md` §4.10 has the statements and the paper argument.
-/

namespace Relativization

open Turing Function Computability Millennium

/-- The input `0^n` as decider code `c` reads it. -/
def DCode.input (c : DCode) (n : ℕ) : List (Fin (c.N.a c.N.k₀)) :=
  (List.replicate n false).map c.inE.symm

theorem DCode.input_length (c : DCode) (n : ℕ) : (c.input n).length = n := by
  simp [DCode.input]

namespace Stage

/-- The state carried from stage to stage: the length bound and the strings added so far. -/
structure State where
  /-- every string added so far, and every query asked so far, has length at most `bound` -/
  bound : ℕ
  /-- the strings added so far -/
  F : Oracle

/-- The machine of stage `i`. -/
noncomputable abbrev M (i : ℕ) : OracleFinTM2 := (dEnum i).N.toOracleFinTM2

/-! ### One stage -/

/-- The input length of stage `i` from state `s`: above `s.bound`, with `p.eval n < 2^n`. -/
noncomputable def len (i : ℕ) (s : State) : ℕ :=
  Classical.choose (exists_len s.bound (dEnum i).time)

theorem bound_lt_len (i : ℕ) (s : State) : s.bound < len i s :=
  (Classical.choose_spec (exists_len s.bound (dEnum i).time)).1

theorem eval_len_lt (i : ℕ) (s : State) : (dEnum i).time.eval (len i s) < 2 ^ len i s :=
  (Classical.choose_spec (exists_len s.bound (dEnum i).time)).2

/-- The step budget of the stage. -/
noncomputable def tim (i : ℕ) (s : State) : ℕ :=
  (dEnum i).time.eval (len i s)

/-- The queries asked during the stage's run under the oracle so far. -/
noncomputable def Q (i : ℕ) (s : State) : Finset (List Bool) :=
  (M i).queries s.F ((dEnum i).input (len i s)) (tim i s)

/-- The counting inequality: fewer queries than strings `u ++ 0^n`. -/
theorem card_Q_lt (i : ℕ) (s : State) : (Q i s).card < 2 ^ len i s :=
  lt_of_le_of_lt ((M i).card_queries_le _ _ _) (eval_len_lt i s)

/-- A prefix `u` of length `n` with `u ++ 0^n` unqueried (B3a). -/
noncomputable def free (i : ℕ) (s : State) : List Bool :=
  Classical.choose (exists_free (len i s) (Q i s) (card_Q_lt i s))

theorem free_length (i : ℕ) (s : State) : (free i s).length = len i s :=
  (Classical.choose_spec (exists_free (len i s) (Q i s) (card_Q_lt i s))).1

/-- The string the stage may add: `u ++ 0^n`. -/
noncomputable def str (i : ℕ) (s : State) : List Bool :=
  free i s ++ List.replicate (len i s) false

theorem str_not_mem_Q (i : ℕ) (s : State) : str i s ∉ Q i s :=
  (Classical.choose_spec (exists_free (len i s) (Q i s) (card_Q_lt i s))).2

theorem str_length (i : ℕ) (s : State) : (str i s).length = 2 * len i s := by
  rw [str, List.length_append, List.length_replicate, free_length]
  omega

/-- Does the machine output `[true]` on `0^n` under the oracle so far, within the budget? -/
def acc (i : ℕ) (s : State) : Prop :=
  Nonempty (OTM2OutputsInTime s.F (M i) ((dEnum i).input (len i s))
    (some [(dEnum i).outE.symm true]) (tim i s))

/-- One stage: raise the bound above every query of the run, and add `u ++ 0^n` exactly when
the machine did not output `[true]`. -/
noncomputable def step (i : ℕ) (s : State) : State where
  bound := 2 * len i s + tim i s * (M i).depth
  F := s.F ∪ {z | ¬ acc i s ∧ z = str i s}

/-- The stage states, by primitive recursion from `(0, ∅)`. -/
noncomputable def st : ℕ → State
  | 0 => ⟨0, ∅⟩
  | i + 1 => step i (st i)

/-! ### The data of stage `i` -/

/-- The bound in force at stage `i`. -/
noncomputable def boundAt (i : ℕ) : ℕ := (st i).bound

/-- The finite oracle stage `i` runs against: everything added by stages `< i`. -/
noncomputable def oracleAt (i : ℕ) : Oracle := (st i).F

/-- The input length of stage `i`. -/
noncomputable def lenAt (i : ℕ) : ℕ := len i (st i)

/-- The step budget of stage `i`. -/
noncomputable def timeAt (i : ℕ) : ℕ := tim i (st i)

/-- The string stage `i` may add. -/
noncomputable def strAt (i : ℕ) : List Bool := str i (st i)

/-- Did stage `i` see `[true]`? -/
def accAt (i : ℕ) : Prop := acc i (st i)

/-- The input `0^n` of stage `i`, as its machine reads it. -/
noncomputable def inputAt (i : ℕ) : List (Fin ((dEnum i).N.a (dEnum i).N.k₀)) :=
  (dEnum i).input (lenAt i)

end Stage

/-- **B4.** The oracle `B` of the separation: everything some stage added. -/
def sepOracle : Oracle := {z | ∃ i, z ∈ Stage.oracleAt i}

namespace Stage

/-! ### Invariants -/

theorem st_succ (i : ℕ) : st (i + 1) = step i (st i) := rfl

theorem boundAt_succ (i : ℕ) : boundAt (i + 1) = 2 * lenAt i + timeAt i * (M i).depth := rfl

theorem oracleAt_zero : oracleAt 0 = ∅ := rfl

theorem mem_oracleAt_succ (i : ℕ) (z : List Bool) :
    z ∈ oracleAt (i + 1) ↔ z ∈ oracleAt i ∨ (¬ accAt i ∧ z = strAt i) :=
  Iff.rfl

theorem inputAt_length (i : ℕ) : (inputAt i).length = lenAt i :=
  DCode.input_length _ _

theorem boundAt_lt_lenAt (i : ℕ) : boundAt i < lenAt i :=
  bound_lt_len i (st i)

theorem timeAt_lt (i : ℕ) : timeAt i < 2 ^ lenAt i :=
  eval_len_lt i (st i)

theorem lenAt_lt_boundAt_succ (i : ℕ) : lenAt i < boundAt (i + 1) := by
  rw [boundAt_succ]
  have := boundAt_lt_lenAt i
  omega

/-- The bounds increase. -/
theorem boundAt_mono : Monotone boundAt :=
  monotone_nat_of_le_succ fun i => ((boundAt_lt_lenAt i).trans (lenAt_lt_boundAt_succ i)).le

theorem strAt_length (i : ℕ) : (strAt i).length = 2 * lenAt i :=
  str_length i (st i)

/-- The added string was unqueried. -/
theorem strAt_not_mem_Q (i : ℕ) : strAt i ∉ Q i (st i) :=
  str_not_mem_Q i (st i)

theorem mem_oracleAt (i : ℕ) (z : List Bool) :
    z ∈ oracleAt i ↔ ∃ j < i, ¬ accAt j ∧ z = strAt j := by
  induction i with
  | zero =>
      rw [oracleAt_zero]
      exact ⟨fun h => absurd h (Set.notMem_empty z),
        fun ⟨j, hj, _⟩ => (Nat.not_lt_zero j hj).elim⟩
  | succ i ih =>
      rw [mem_oracleAt_succ, ih]
      constructor
      · rintro (⟨j, hj, h⟩ | h)
        · exact ⟨j, Nat.lt_succ_of_lt hj, h⟩
        · exact ⟨i, Nat.lt_succ_self i, h⟩
      · rintro ⟨j, hj, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact Or.inl ⟨j, hj, h⟩
        · exact Or.inr h

theorem oracleAt_subset_sepOracle (i : ℕ) : oracleAt i ⊆ sepOracle :=
  fun _ hz => ⟨i, hz⟩

/-- Membership in `B`: the strings added by the stages that did not see `[true]`. -/
theorem mem_sepOracle (z : List Bool) : z ∈ sepOracle ↔ ∃ j, ¬ accAt j ∧ z = strAt j :=
  ⟨fun ⟨i, hi⟩ => let ⟨j, _, h⟩ := (mem_oracleAt i z).mp hi; ⟨j, h⟩,
    fun ⟨j, h⟩ => ⟨j + 1, (mem_oracleAt (j + 1) z).mpr ⟨j, Nat.lt_succ_self j, h⟩⟩⟩

/-- Below its bound, the finite oracle of stage `i` is final. -/
theorem mem_oracleAt_of_length_le {i : ℕ} {z : List Bool} (hz : z ∈ sepOracle)
    (hl : z.length ≤ boundAt i) : z ∈ oracleAt i := by
  obtain ⟨j, hj, rfl⟩ := (mem_sepOracle z).mp hz
  refine (mem_oracleAt i _).mpr ⟨j, ?_, hj, rfl⟩
  by_contra hij
  have h₁ : boundAt i ≤ boundAt j := boundAt_mono (not_lt.mp hij)
  have h₂ := boundAt_lt_lenAt j
  rw [strAt_length] at hl
  omega

/-! ### B5: run stability -/

/-- `F_i` and `B` agree on every query asked during the stage-`i` run under `F_i`: a string of
`B` is some `x_j`; `j < i` puts it in `F_i`; `j = i` contradicts the choice of `u_i`; `j > i`
contradicts L3 (`|x_j| = 2 n_j > bound_{i+1} ≥ n_i + t_i D_i`). -/
theorem agree_on_queries (i : ℕ) : ∀ z ∈ Q i (st i), (z ∈ oracleAt i ↔ z ∈ sepOracle) := by
  intro z hz
  refine ⟨fun h => oracleAt_subset_sepOracle i h, fun hB => ?_⟩
  obtain ⟨j, hj, rfl⟩ := (mem_sepOracle z).mp hB
  rcases lt_trichotomy j i with hji | rfl | hij
  · exact (mem_oracleAt i _).mpr ⟨j, hji, hj, rfl⟩
  · exact absurd hz (strAt_not_mem_Q j)
  · exfalso
    have h₁ : (strAt j).length ≤ (inputAt i).length + timeAt i * (M i).depth :=
      (M i).length_le_of_mem_queries hz
    rw [inputAt_length, strAt_length] at h₁
    have h₂ := boundAt_lt_lenAt j
    have h₃ : boundAt (i + 1) ≤ boundAt j := boundAt_mono hij
    rw [boundAt_succ] at h₃
    omega

/-- **B5.** The stage-`i` run on `0^{n_i}` under `F_i` is the run under `B` for `t_i` steps:
the same outputs within `t_i` steps. -/
theorem outputs_iff (i : ℕ) (o : Option (List (Fin ((dEnum i).N.a (dEnum i).N.k₁)))) :
    Nonempty (OTM2OutputsInTime (oracleAt i) (M i) (inputAt i) o (timeAt i)) ↔
      Nonempty (OTM2OutputsInTime sepOracle (M i) (inputAt i) o (timeAt i)) :=
  (M i).outputsInTime_congr_queries _ _ _ (agree_on_queries i)

/-! ### Towards B6 -/

/-- If stage `i` saw `[true]`, no string of `B` has length in `[n_i, 2 n_i]`. -/
theorem length_lt_or_lt_of_accAt {i : ℕ} (h : accAt i) {z : List Bool} (hz : z ∈ sepOracle) :
    z.length < lenAt i ∨ 2 * lenAt i < z.length := by
  obtain ⟨j, hj, rfl⟩ := (mem_sepOracle z).mp hz
  rw [strAt_length]
  rcases lt_trichotomy j i with hji | rfl | hij
  · left
    have h₁ : boundAt (j + 1) ≤ boundAt i := boundAt_mono (Nat.succ_le_of_lt hji)
    rw [boundAt_succ] at h₁
    have h₂ := boundAt_lt_lenAt i
    omega
  · exact absurd h hj
  · right
    have h₁ : boundAt (i + 1) ≤ boundAt j := boundAt_mono hij
    have h₂ := boundAt_lt_lenAt j
    have h₃ := lenAt_lt_boundAt_succ i
    omega

/-- If stage `i` did not see `[true]`, it added `u_i ++ 0^{n_i}`. -/
theorem strAt_mem_sepOracle {i : ℕ} (h : ¬ accAt i) : strAt i ∈ sepOracle :=
  (mem_sepOracle _).mpr ⟨i, h, rfl⟩

end Stage

/-! ### B6 -/

/-- **B6.** `sepLang sepOracle ∉ P^sepOracle`. A polynomial-time decider for it under
`sepOracle` is some code `dEnum i`; stage `i` made it wrong on `0^{n_i}`. -/
theorem sepLang_not_inP : ¬ InP sepOracle (fin_encoding_string Bool) (sepLang sepOracle) := by
  rintro ⟨f, h, hf⟩
  obtain ⟨c, -, hc⟩ := exists_dcode_decides h
  obtain ⟨i, rfl⟩ := dEnum_surjective c
  have hB : Nonempty (OTM2OutputsInTime sepOracle (Stage.M i) (Stage.inputAt i)
      (some [(dEnum i).outE.symm (f (List.replicate (Stage.lenAt i) false))])
      (Stage.timeAt i)) := by
    have := hc (List.replicate (Stage.lenAt i) false)
    rwa [List.length_replicate] at this
  obtain ⟨hB⟩ := hB
  have key := Stage.outputs_iff i (some [(dEnum i).outE.symm true])
  -- F4': the machine's one output under `B` is `[f 0^n]`
  have hbool : ∀ b : Bool, Nonempty (OTM2OutputsInTime sepOracle (Stage.M i) (Stage.inputAt i)
      (some [(dEnum i).outE.symm b]) (Stage.timeAt i)) ↔
        b = f (List.replicate (Stage.lenAt i) false) :=
    fun b => OTM2OutputsInTime.bool_iff (tm := Stage.M i) (dEnum i).outE hB b
  by_cases hacc : Stage.accAt i
  · -- the stage saw `[true]`, so `f 0^n = true`, so some `u ++ 0^n ∈ B` with `|u| ≤ n`
    have h₁ : Nonempty (OTM2OutputsInTime sepOracle (Stage.M i) (Stage.inputAt i)
        (some [(dEnum i).outE.symm true]) (Stage.timeAt i)) := key.mp hacc
    have h₂ : true = f (List.replicate (Stage.lenAt i) false) := (hbool true).mp h₁
    obtain ⟨u, hu, huB⟩ := (sepLang_replicate_iff _ _).mp ((hf _).mpr h₂.symm)
    have := Stage.length_lt_or_lt_of_accAt hacc huB
    rw [List.length_append, List.length_replicate] at this
    omega
  · -- the stage added `u ++ 0^n`, so `f 0^n = true`, so the machine outputs `[true]`
    have h₃ : sepLang sepOracle (List.replicate (Stage.lenAt i) false) :=
      (sepLang_replicate_iff _ _).mpr
        ⟨Stage.free i (Stage.st i), (Stage.free_length i (Stage.st i)).le,
          Stage.strAt_mem_sepOracle hacc⟩
    have h₂ : f (List.replicate (Stage.lenAt i) false) = true := (hf _).mp h₃
    rw [h₂] at hB
    exact hacc (key.mpr ⟨hB⟩)

/-- **B6**, the form T6 will use: `P^B ≠ NP^B` for `B = sepOracle`, since `sepLang B ∈ NP^B`
(B2) but not in `P^B`. -/
theorem sepOracle_not_pEqNP : ¬ PEqNP sepOracle := fun h =>
  sepLang_not_inP ((h (sepLang sepOracle)).mpr (sepLang_inNP sepOracle))

end Relativization
