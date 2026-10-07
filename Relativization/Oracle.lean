import Mathlib.Computability.TuringMachine.Computable

/-!
# Oracle two-stack Turing machines

`OracleFinTM2` is Mathlib's `Turing.FinTM2` plus a *query stack* with binary alphabet, and a
program that receives, at every step, the oracle's verdict on the current content of the query
stack (definitions D1 and D2 of `NOTES.md`).

Main results of this file:

* `OracleFinTM2.step_empty` (T0): with the empty oracle the step function is the plain one;
* `OracleFinTM2.query_length_step` (L2): one step lengthens the query by at most `tm.depth`;
* `OracleFinTM2.iter_congr` (L4), `OracleFinTM2.locality` (L5),
  `OracleFinTM2.outputsInTime_congr` (L6): a run of `t` steps depends only on the oracle's
  values on strings of length at most `input length + t * tm.depth`.
-/

namespace Relativization

open Turing StateTransition Function

/-- An oracle is a language over the binary alphabet. -/
abbrev Oracle := Set (List Bool)

/-- `Turing.FinTM2` plus a query stack with binary alphabet, and a program that may depend on
the oracle's answer about the current content of the query stack. -/
structure OracleFinTM2 where
  /-- index type of stacks -/
  {K : Type} [kDecidableEq : DecidableEq K]
  /-- finitely many stacks -/
  [kFin : Fintype K]
  /-- input resp. output stack -/
  (k₀ k₁ : K)
  /-- type of stack elements -/
  (Γ : K → Type)
  /-- type of function labels -/
  (Λ : Type)
  /-- the label executed first -/
  (main : Λ)
  /-- finitely many labels -/
  [ΛFin : Fintype Λ]
  /-- type of internal states -/
  (σ : Type)
  /-- the initial state -/
  (initialState : σ)
  /-- finitely many states -/
  [σFin : Fintype σ]
  /-- the input alphabet is finite -/
  [Γk₀Fin : Fintype (Γ k₀)]
  /-- the query stack -/
  (kq : K)
  /-- the query alphabet is binary -/
  (queryAlphabet : Γ kq ≃ Bool)
  /-- the program: one statement per label and oracle answer -/
  (m : Λ → Bool → Turing.TM2.Stmt Γ Λ σ)

namespace OracleFinTM2

variable (tm : OracleFinTM2)

instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq

/-- Fixing the oracle's answer gives a plain `FinTM2` on the same types. -/
def toFinTM2 (b : Bool) : FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := tm.Γ
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := tm.Γk₀Fin
  m := fun l => tm.m l b

/-- Configurations of an oracle machine: those of the underlying TM2. -/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

/-- The query string: the query stack, top first, read as bits. -/
def query (c : tm.Cfg) : List Bool :=
  (c.stk tm.kq).map tm.queryAlphabet

open Classical in
/-- One step with oracle `A`: the program sees whether the current query string is in `A`. -/
noncomputable def step (A : Oracle) (c : tm.Cfg) : Option tm.Cfg :=
  Turing.TM2.step (fun l => tm.m l (decide (tm.query c ∈ A))) c

/-- The initial configuration on an input list. -/
def initList (s : List (tm.Γ tm.k₀)) : tm.Cfg :=
  Turing.initList (tm.toFinTM2 false) s

/-- The halting configuration with a given output list. -/
def haltList (s : List (tm.Γ tm.k₁)) : tm.Cfg :=
  Turing.haltList (tm.toFinTM2 false) s

end OracleFinTM2

/-- A proof that `tm` with oracle `A` outputs `l'` on input `l` in at most `m` steps. -/
def OTM2OutputsInTime (A : Oracle) (tm : OracleFinTM2) (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) (m : ℕ) :=
  EvalsToInTime (tm.step A) (tm.initList l) (Option.map tm.haltList l') m

/-- An oracle machine, a polynomial, and a proof that with oracle `A` the machine outputs `f` in
at most `time (input length)` steps. -/
structure OTM2ComputableInPolyTime (A : Oracle) {α β αΓ βΓ : Type} (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) where
  /-- the machine -/
  tm : OracleFinTM2
  /-- the input alphabet is equivalent to `αΓ` -/
  inputAlphabet : tm.Γ tm.k₀ ≃ αΓ
  /-- the output alphabet is equivalent to `βΓ` -/
  outputAlphabet : tm.Γ tm.k₁ ≃ βΓ
  /-- the time bound -/
  time : Polynomial ℕ
  /-- the machine outputs `f` within the time bound -/
  outputsFun : ∀ a, OTM2OutputsInTime A tm ((ea a).map inputAlphabet.invFun)
    (some ((eb (f a)).map outputAlphabet.invFun)) (time.eval (ea a).length)

/-! ### Generic iteration lemmas -/

section iter

variable {α β : Type}

theorem iter_none (f : α → Option α) (n : ℕ) : (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply]; exact ih

theorem iter_step {f : α → Option α} {c c' : α} (h : f c = some c') (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some c') := by
  rw [iterate_succ_apply]
  change (flip bind f)^[n] (f c) = _
  rw [h]

/-- An embedding of configurations that commutes with one step commutes with every run. -/
theorem iter_map {f : α → Option α} {g : β → Option β} (e : α → β)
    (H : ∀ c, g (e c) = (f c).map e) (n : ℕ) (x : Option α) :
    (flip bind g)^[n] (x.map e) = ((flip bind f)^[n] x).map e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply', ih]
      cases (flip bind f)^[n] x with
      | none => rfl
      | some d => exact H d

/-- A step-respecting embedding transports runs that end in a configuration. (Halted
configurations are absorbing, so every intermediate configuration of such a run is live.) -/
theorem iter_sim {f : α → Option α} {g : β → Option β} (e : α → β)
    (H : ∀ c c', f c = some c' → g (e c) = some (e c')) :
    ∀ (n : ℕ) (c d : α), (flip bind f)^[n] (some c) = some d →
      (flip bind g)^[n] (some (e c)) = some (e d) := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h ⊢
      rw [h]
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind f)^[n] (f c) = some d at h
      cases hc : f c with
      | none => rw [hc, iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          rw [iter_step (H c c' hc)]
          exact ih c' d h

/-- A measure that grows by at most `D` per step grows by at most `n * D` in `n` steps. -/
theorem iter_le {f : α → Option α} (μ : α → ℕ) (D : ℕ)
    (H : ∀ c c', f c = some c' → μ c' ≤ μ c + D) :
    ∀ (n : ℕ) (c d : α), (flip bind f)^[n] (some c) = some d → μ d ≤ μ c + n * D := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h
      subst h; simp
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind f)^[n] (f c) = some d at h
      cases hc : f c with
      | none => rw [hc, iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          have h₁ := ih c' d h
          have h₂ := H c c' hc
          rw [Nat.succ_mul]
          omega

end iter

/-! ### Pushes per step -/

section depth

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Maximum number of pushes onto stack `k` along one root-to-leaf path of a statement. -/
def pushDepth (k : K) : TM2.Stmt Γ Λ σ → ℕ
  | .push k' _ q => (if k' = k then 1 else 0) + pushDepth k q
  | .peek _ _ q => pushDepth k q
  | .pop _ _ q => pushDepth k q
  | .load _ q => pushDepth k q
  | .branch _ q₁ q₂ => max (pushDepth k q₁) (pushDepth k q₂)
  | .goto _ => 0
  | .halt => 0

/-- Executing a statement lengthens stack `k` by at most `pushDepth k`. -/
theorem length_stepAux (k : K) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushDepth k q := by
  induction q generalizing v S with
  | push k' f q ih =>
      simp only [TM2.stepAux, pushDepth]
      refine (ih _ _).trans ?_
      by_cases h : k' = k
      · subst h; simp; omega
      · simp [update_of_ne (Ne.symm h), h]
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
      simp only [TM2.stepAux, pushDepth]
      refine (ih _ _).trans ?_
      by_cases h : k' = k
      · subst h; simp
      · simp [update_of_ne (Ne.symm h)]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, pushDepth]
      cases f v
      · exact (ih₂ v S).trans (by omega)
      · exact (ih₁ v S).trans (by omega)
  | goto f => simp [TM2.stepAux, pushDepth]
  | halt => simp [TM2.stepAux, pushDepth]

/-- One step of a TM2 program lengthens stack `k` by at most any bound on its `pushDepth`. -/
theorem length_step_le {M : Λ → TM2.Stmt Γ Λ σ} (k : K) (D : ℕ)
    (hD : ∀ l, pushDepth k (M l) ≤ D) {c c' : TM2.Cfg Γ Λ σ} (h : TM2.step M c = some c') :
    (c'.stk k).length ≤ (c.stk k).length + D := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact (length_stepAux k _ v S).trans (Nat.add_le_add_left (hD l) _)

end depth

namespace OracleFinTM2

variable (tm : OracleFinTM2)

attribute [local instance] OracleFinTM2.ΛFin

/-- `depth M`: the largest number of symbols one step can push onto the query stack. -/
def depth : ℕ :=
  Finset.univ.sup fun p : tm.Λ × Bool => pushDepth tm.kq (tm.m p.1 p.2)

theorem pushDepth_le_depth (l : tm.Λ) (b : Bool) : pushDepth tm.kq (tm.m l b) ≤ tm.depth :=
  Finset.le_sup (f := fun p : tm.Λ × Bool => pushDepth tm.kq (tm.m p.1 p.2))
    (Finset.mem_univ (l, b))

/-! ### The empty oracle -/

/-- **T0.** With the empty oracle, the step function is that of the plain machine obtained by
fixing the answer `false`. -/
theorem step_empty (c : tm.Cfg) : tm.step ∅ c = (tm.toFinTM2 false).step c := by
  unfold step
  rw [@decide_eq_false _ (Classical.propDecidable _) (Set.notMem_empty (tm.query c))]
  rfl

/-! ### Locality -/

/-- **L1.** A step depends on the oracle only through the answer to the current query. -/
theorem step_congr {A A' : Oracle} (c : tm.Cfg) (h : tm.query c ∈ A ↔ tm.query c ∈ A') :
    tm.step A c = tm.step A' c := by
  unfold step
  rw [decide_eq_decide.mpr h]

theorem query_length (c : tm.Cfg) : (tm.query c).length = (c.stk tm.kq).length := by
  simp [query]

/-- **L2 (growth).** One step lengthens the query string by at most `tm.depth`. -/
theorem query_length_step (A : Oracle) {c c' : tm.Cfg} (h : tm.step A c = some c') :
    (tm.query c').length ≤ (tm.query c).length + tm.depth := by
  rw [query_length, query_length]
  exact length_step_le tm.kq tm.depth (fun l => tm.pushDepth_le_depth l _) h

/-- **L3.** After `n` steps the query string is at most `n * tm.depth` longer. -/
theorem query_length_iter (A : Oracle) (n : ℕ) (c d : tm.Cfg)
    (h : (flip bind (tm.step A))^[n] (some c) = some d) :
    (tm.query d).length ≤ (tm.query c).length + n * tm.depth :=
  iter_le (fun c => (tm.query c).length) tm.depth (fun _ _ => tm.query_length_step A) n c d h

/-- **L4 (sharp locality).** Two oracles that agree on every query asked during the first `n`
steps of a run give the same run for `n` steps. -/
theorem iter_congr {A A' : Oracle} (n : ℕ) (c : tm.Cfg)
    (h : ∀ j < n, ∀ d, (flip bind (tm.step A))^[j] (some c) = some d →
      (tm.query d ∈ A ↔ tm.query d ∈ A')) :
    (flip bind (tm.step A))^[n] (some c) = (flip bind (tm.step A'))^[n] (some c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have ih' := ih fun j hj d hd => h j (Nat.lt_succ_of_lt hj) d hd
      rw [iterate_succ_apply', iterate_succ_apply', ← ih']
      cases hd : (flip bind (tm.step A))^[n] (some c) with
      | none => rfl
      | some d => exact tm.step_congr d (h n (Nat.lt_succ_self n) d hd)

/-- Locality from an arbitrary configuration, by query length. -/
theorem iter_congr_of_length {A A' : Oracle} (c : tm.Cfg) (t : ℕ)
    (h : ∀ z : List Bool, z.length ≤ (tm.query c).length + t * tm.depth → (z ∈ A ↔ z ∈ A'))
    {n : ℕ} (hn : n ≤ t) :
    (flip bind (tm.step A))^[n] (some c) = (flip bind (tm.step A'))^[n] (some c) := by
  refine tm.iter_congr n c fun j hj d hd => h _ ?_
  have h₁ := tm.query_length_iter A j c d hd
  have h₂ : j * tm.depth ≤ t * tm.depth := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The query string of an initial configuration is no longer than the input. -/
theorem query_initList_length_le (l : List (tm.Γ tm.k₀)) :
    (tm.query (tm.initList l)).length ≤ l.length := by
  rw [query_length]
  by_cases h : tm.kq = tm.k₀
  · rw [h]; simp [initList, Turing.initList, toFinTM2]
  · simp [initList, Turing.initList, toFinTM2, h]

/-- **L5 (query locality).** A run of at most `t` steps on input `l` depends only on the
oracle's values on strings of length at most `l.length + t * tm.depth`. -/
theorem locality {A A' : Oracle} (l : List (tm.Γ tm.k₀)) (t : ℕ)
    (h : ∀ z : List Bool, z.length ≤ l.length + t * tm.depth → (z ∈ A ↔ z ∈ A'))
    {n : ℕ} (hn : n ≤ t) :
    (flip bind (tm.step A))^[n] (some (tm.initList l)) =
      (flip bind (tm.step A'))^[n] (some (tm.initList l)) := by
  refine tm.iter_congr_of_length _ t (fun z hz => h z ?_) hn
  have := tm.query_initList_length_le l
  omega

/-- Transport of a time-bounded output along oracles that agree on short strings. -/
def OutputsInTime.congr {A A' : Oracle} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {t : ℕ}
    (h : ∀ z : List Bool, z.length ≤ l.length + t * tm.depth → (z ∈ A ↔ z ∈ A'))
    (o : OTM2OutputsInTime A tm l l' t) : OTM2OutputsInTime A' tm l l' t where
  steps := o.steps
  evals_in_steps := (tm.locality l t h o.steps_le_m).symm.trans o.evals_in_steps
  steps_le_m := o.steps_le_m

/-- **L6.** Whether the machine outputs `l'` on `l` within `t` steps depends only on the oracle's
values on strings of length at most `l.length + t * tm.depth`. -/
theorem outputsInTime_congr {A A' : Oracle} (l : List (tm.Γ tm.k₀))
    (l' : Option (List (tm.Γ tm.k₁))) (t : ℕ)
    (h : ∀ z : List Bool, z.length ≤ l.length + t * tm.depth → (z ∈ A ↔ z ∈ A')) :
    Nonempty (OTM2OutputsInTime A tm l l' t) ↔ Nonempty (OTM2OutputsInTime A' tm l l' t) :=
  ⟨fun ⟨o⟩ => ⟨OutputsInTime.congr tm h o⟩,
    fun ⟨o⟩ => ⟨OutputsInTime.congr tm (fun z hz => (h z hz).symm) o⟩⟩

end OracleFinTM2

end Relativization
