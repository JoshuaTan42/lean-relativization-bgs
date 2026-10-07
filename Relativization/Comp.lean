import Relativization.Classes

/-!
# A plain polynomial-time function followed by an oracle machine

`oracleComp` (F7): if `f` is computed by a plain polynomial-time `FinTM2` and `g` by a
polynomial-time oracle machine with oracle `A`, then `g ∘ f` is computed by a polynomial-time
oracle machine with oracle `A`.

The composite machine has stacks `K₁ ⊕ K₂ ⊕ Unit`. It runs `M₁`, moves `M₁`'s output onto a
scratch stack and back onto `M₂`'s input stack (two reversals preserve the order), then runs
`M₂`. Its query stack is `M₂`'s. Only the statements of `M₂` look at the oracle's answer, and
while `M₂` runs the composite query string is `M₂`'s query string.

`inP_subset_inNP` (T4): `P^A ⊆ NP^A`, from `oracleComp` and the left-projection machine of
`Millennium`.

Ported from `Comp.lean` of the PvsNP project (commit `c271016`), where both machines are plain.
-/

namespace Relativization

open Turing StateTransition Function Computability Millennium

namespace Comp

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin
  OracleFinTM2.kFin OracleFinTM2.ΛFin OracleFinTM2.σFin OracleFinTM2.Γk₀Fin

variable (M₁ : FinTM2) (M₂ : OracleFinTM2)

/-- Stack indices of the composite machine: `M₁`'s stacks, `M₂`'s stacks, one scratch stack. -/
abbrev CK := M₁.K ⊕ M₂.K ⊕ Unit

/-- `M₂`'s input alphabet, used for the scratch stack and for symbols held in the control. -/
abbrev X := M₂.Γ M₂.k₀

/-- Stack alphabets of the composite machine. -/
@[reducible] def CΓ : CK M₁ M₂ → Type
  | .inl k => M₁.Γ k
  | .inr (.inl k) => M₂.Γ k
  | .inr (.inr _) => X M₂

/-- Labels: `M₁`'s, `M₂`'s, and the two copy loops (`none` = pop, `some x` = push `x`). -/
abbrev CΛ := M₁.Λ ⊕ M₂.Λ ⊕ (Option (X M₂) ⊕ Option (X M₂))

/-- States: `M₁`'s state, `M₂`'s state, and the symbol just popped by a copy loop. -/
abbrev Cσ := M₁.σ × M₂.σ × Option (X M₂)

/-- Label: pop from `M₁`'s output stack. -/
abbrev pop1 : CΛ M₁ M₂ := .inr (.inr (.inl none))
/-- Label: push `x` on the scratch stack. -/
abbrev push1 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inl (some x)))
/-- Label: pop from the scratch stack. -/
abbrev pop2 : CΛ M₁ M₂ := .inr (.inr (.inr none))
/-- Label: push `x` on `M₂`'s input stack. -/
abbrev push2 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inr (some x)))

/-- The scratch stack index. -/
abbrev tmp : CK M₁ M₂ := .inr (.inr ())

/-- Lift a statement of `M₁`; halting jumps to the first copy loop instead. -/
def lift₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inl k) (fun s => f s.1) (lift₁ q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .load a q => .load (fun s => (a s.1, s.2)) (lift₁ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (lift₁ q₁) (lift₁ q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => pop1 M₁ M₂)

/-- Lift a statement of `M₂`; halting halts. -/
def lift₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inr (.inl k)) (fun s => f s.2.1) (lift₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (lift₂ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (lift₂ q₁) (lift₂ q₂)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (φ : M₁.Γ M₁.k₁ → X M₂)

/-- The composite program. `φ` translates `M₁`'s output symbols into `M₂`'s input symbols. Only
the statements of `M₂` use the oracle's answer. -/
def prog : CΛ M₁ M₂ → Bool → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .inl l, _ => lift₁ M₁ M₂ (M₁.m l)
  | .inr (.inl l), b => lift₂ M₁ M₂ (M₂.m l b)
  | .inr (.inr (.inl none)), _ =>
      .pop (.inl M₁.k₁) (fun s o => (s.1, s.2.1, o.map φ))
        (.goto fun s => match s.2.2 with
          | some x => push1 M₁ M₂ x
          | none => pop2 M₁ M₂)
  | .inr (.inr (.inl (some x))), _ =>
      .push (tmp M₁ M₂) (fun _ => x) (.goto fun _ => pop1 M₁ M₂)
  | .inr (.inr (.inr none)), _ =>
      .pop (tmp M₁ M₂) (fun s o => (s.1, s.2.1, o))
        (.goto fun s => match s.2.2 with
          | some x => push2 M₁ M₂ x
          | none => .inr (.inl M₂.main))
  | .inr (.inr (.inr (some x))), _ =>
      .push (.inr (.inl M₂.k₀)) (fun _ => x) (.goto fun _ => pop2 M₁ M₂)

/-- The composite machine. Its query stack is `M₂`'s. -/
def compTM : OracleFinTM2 where
  K := CK M₁ M₂
  k₀ := .inl M₁.k₀
  k₁ := .inr (.inl M₂.k₁)
  Γ := CΓ M₁ M₂
  Λ := CΛ M₁ M₂
  main := .inl M₁.main
  σ := Cσ M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  kq := .inr (.inl M₂.kq)
  queryAlphabet := M₂.queryAlphabet
  m := prog M₁ M₂ φ

/-! ### Stacks of the composite machine -/

/-- Assemble composite stacks from `M₁`'s stacks, `M₂`'s stacks and the scratch stack. -/
def mkStk (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    ∀ k : CK M₁ M₂, List (CΓ M₁ M₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => t

variable {M₁ M₂}

theorem update_mkStk_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₁.K) (x : List (M₁.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inl k) x = mkStk M₁ M₂ (update S₁ k x) S₂ t := by
  funext k'
  rcases k' with k' | k' | u
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_inr (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₂.K) (x : List (M₂.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inr (.inl k)) x = mkStk M₁ M₂ S₁ (update S₂ k x) t := by
  funext k'
  rcases k' with k' | k' | u
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_tmp (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (x : List (X M₂)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (tmp M₁ M₂) x = mkStk M₁ M₂ S₁ S₂ x := by
  funext k'
  rcases k' with k' | k' | ⟨⟩
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl
  · simp [mkStk]

/-! ### Simulating one statement of `M₁` or `M₂` -/

/-- Composite label of a (possibly halted) `M₁` label: halting becomes the first copy loop. -/
def lab₁ : Option M₁.Λ → CΛ M₁ M₂
  | some l => .inl l
  | none => pop1 M₁ M₂

theorem stepAux_lift₁ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k))
    (v₂ : M₂.σ) (o : Option (X M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₁ M₁ M₂ q) (v, v₂, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨some (lab₁ (TM2.stepAux q v S₁).l), ((TM2.stepAux q v S₁).var, v₂, o),
        mkStk M₁ M₂ (TM2.stepAux q v S₁).stk S₂ t⟩ := by
  induction q generalizing v S₁ with
  | push k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | peek k f q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | load a q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₁, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₁, TM2.stepAux, lab₁]
  | halt => simp [lift₁, TM2.stepAux, lab₁]

theorem stepAux_lift₂ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k))
    (v₁ : M₁.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₂ M₁ M₂ q) (v₁, v, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨(TM2.stepAux q v S₂).l.map (fun l => .inr (.inl l)), (v₁, (TM2.stepAux q v S₂).var, o),
        mkStk M₁ M₂ S₁ (TM2.stepAux q v S₂).stk t⟩ := by
  induction q generalizing v S₂ with
  | push k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | peek k f q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | load a q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₂, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₂, TM2.stepAux]
  | halt => simp [lift₂, TM2.stepAux]

/-! ### Phase embeddings and one-step simulation -/

/-- Configurations of the composite machine, on its raw types. -/
abbrev CCfg (M₁ : FinTM2) (M₂ : OracleFinTM2) : Type :=
  TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)

/-- The step function of the composite machine, on its raw types. -/
noncomputable def cstep (A : Oracle) (c : CCfg M₁ M₂) : Option (CCfg M₁ M₂) :=
  (compTM M₁ M₂ φ).step A c

/-- Composite configuration while running `M₁` (all other stacks empty). -/
def emb₁ (c : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : CCfg M₁ M₂ :=
  ⟨some (lab₁ c.l), (c.var, M₂.initialState, none), mkStk M₁ M₂ c.stk (fun _ => []) []⟩

/-- Composite configuration while running `M₂` (all other stacks empty). -/
def emb₂ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : CCfg M₁ M₂ :=
  ⟨c.l.map (fun l => .inr (.inl l)), (M₁.initialState, c.var, none),
    mkStk M₁ M₂ (fun _ => []) c.stk []⟩

/-- While `M₂` runs, the composite machine asks `M₂`'s query. -/
theorem query_emb₂ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) :
    (compTM M₁ M₂ φ).query (emb₂ (M₁ := M₁) c) = M₂.query c :=
  rfl

/-- A step of `M₁` is a step of the composite machine, whatever the oracle. -/
theorem step_emb₁ (A : Oracle) {c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ} (h : M₁.step c = some c') :
    cstep φ A (emb₁ (M₂ := M₂) c) = some (emb₁ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · obtain rfl := Option.some.inj h
    show some (TM2.stepAux (lift₁ M₁ M₂ (M₁.m l)) (v, M₂.initialState, none)
      (mkStk M₁ M₂ S (fun _ => []) [])) = _
    rw [stepAux_lift₁]
    rfl

open Classical in
/-- A step of `M₂` with oracle `A` is a step of the composite machine with oracle `A`. -/
theorem step_emb₂ (A : Oracle) {c c' : TM2.Cfg M₂.Γ M₂.Λ M₂.σ} (h : M₂.step A c = some c') :
    cstep φ A (emb₂ (M₁ := M₁) c) = some (emb₂ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [OracleFinTM2.step, TM2.step] at h
  · have h' : some (TM2.stepAux (M₂.m l (decide (M₂.query ⟨some l, v, S⟩ ∈ A))) v S) =
        some c' := h
    obtain rfl := Option.some.inj h'
    show some (TM2.stepAux (lift₂ M₁ M₂ (M₂.m l (decide (M₂.query ⟨some l, v, S⟩ ∈ A))))
      (M₁.initialState, v, none) (mkStk M₁ M₂ (fun _ => []) S [])) = _
    rw [stepAux_lift₂]
    rfl

/-! ### The copy loops -/

section copy

variable (A : Oracle) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k))
  (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))

theorem step_pop1_cons (y : M₁.Γ M₁.k₁) (ys : List (M₁.Γ M₁.k₁)) (hy : S₁ M₁.k₁ = y :: ys) :
    cstep φ A ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (push1 M₁ M₂ (φ y)), (v₁, v₂, some (φ y)),
        mkStk M₁ M₂ (update S₁ M₁.k₁ ys) S₂ t⟩ := by
  simp [cstep, OracleFinTM2.step, compTM, TM2.step, prog, TM2.stepAux, mkStk, hy]
  exact update_mkStk_inl _ _ _ _ _

theorem step_pop1_nil (hy : S₁ M₁.k₁ = []) :
    cstep φ A ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none), mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ t⟩ := by
  simp [cstep, OracleFinTM2.step, compTM, TM2.step, prog, TM2.stepAux, mkStk, hy]
  exact update_mkStk_inl _ _ _ _ _

theorem step_push1 (x : X M₂) (s : Cσ M₁ M₂) :
    cstep φ A ⟨some (push1 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop1 M₁ M₂), s, mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ := by
  simp [cstep, OracleFinTM2.step, compTM, TM2.step, prog, TM2.stepAux, mkStk]
  exact update_mkStk_tmp _ _ _ _

theorem step_pop2_cons (x : X M₂) :
    cstep φ A ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ =
      some ⟨some (push2 M₁ M₂ x), (v₁, v₂, some x), mkStk M₁ M₂ S₁ S₂ t⟩ := by
  simp [cstep, OracleFinTM2.step, compTM, TM2.step, prog, TM2.stepAux, mkStk]
  exact update_mkStk_tmp _ _ _ _

theorem step_pop2_nil :
    cstep φ A ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ []⟩ =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none), mkStk M₁ M₂ S₁ S₂ []⟩ := by
  simp [cstep, OracleFinTM2.step, compTM, TM2.step, prog, TM2.stepAux, mkStk]

theorem step_push2 (x : X M₂) (s : Cσ M₁ M₂) :
    cstep φ A ⟨some (push2 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), s, mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (x :: S₂ M₂.k₀)) t⟩ := by
  simp [cstep, OracleFinTM2.step, compTM, TM2.step, prog, TM2.stepAux, mkStk]
  exact update_mkStk_inr _ _ _ _ _

end copy

/-- First copy loop: move `M₁`'s output onto the scratch stack (reversing it). -/
theorem copy₁ (A : Oracle) (ys : List (M₁.Γ M₁.k₁)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (hy : S₁ M₁.k₁ = ys) :
    (flip bind (cstep φ A))^[2 * ys.length + 1]
        (some ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none),
        mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ ((ys.map φ).reverse ++ t)⟩ := by
  induction ys generalizing o S₁ t with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop1_nil φ A v₁ v₂ o S₁ S₂ t hy)]
      simp
  | cons y ys ih =>
      rw [show 2 * (y :: ys).length + 1 = (2 * ys.length + 1) + 1 + 1 by simp; ring,
        iter_step (step_pop1_cons φ A v₁ v₂ o S₁ S₂ t y ys hy),
        iter_step (step_push1 φ A _ _ _ _ _), ih _ _ _ (update_self _ _ _)]
      simp [update_idem]

/-- Second copy loop: move the scratch stack onto `M₂`'s input stack (reversing it back). -/
theorem copy₂ (A : Oracle) (t : List (X M₂)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) :
    (flip bind (cstep φ A))^[2 * t.length + 1]
        (some ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none),
        mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (t.reverse ++ S₂ M₂.k₀)) []⟩ := by
  induction t generalizing o S₂ with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop2_nil φ A v₁ v₂ o S₁ S₂)]
      simp
  | cons x t ih =>
      rw [show 2 * (x :: t).length + 1 = (2 * t.length + 1) + 1 + 1 by simp; ring,
        iter_step (step_pop2_cons φ A v₁ v₂ o S₁ S₂ t x), iter_step (step_push2 φ A _ _ _ _ _),
        ih]
      simp [update_idem]

/-! ### Output length of a plain machine -/

/-- The most symbols one step of a plain machine can push onto its output stack. -/
def outDepth (M : FinTM2) : ℕ :=
  Finset.univ.sup fun l : M.Λ => pushDepth M.k₁ (M.m l)

/-- After `n` steps the output stack is at most `n * outDepth M` longer. -/
theorem length_iter (M : FinTM2) (n : ℕ) (c d : M.Cfg)
    (h : (flip bind M.step)^[n] (some c) = some d) :
    (d.stk M.k₁).length ≤ (c.stk M.k₁).length + n * outDepth M :=
  iter_le (fun c : M.Cfg => (c.stk M.k₁).length) (outDepth M)
    (fun _ _ hc => length_step_le M.k₁ (outDepth M)
      (fun l => Finset.le_sup (f := fun l : M.Λ => pushDepth M.k₁ (M.m l)) (Finset.mem_univ l))
      hc) n c d h

/-- Evaluation of a polynomial with natural coefficients is monotone. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-! ### Initial and halting configurations -/

theorem initList_stk_length_le (M : FinTM2) (l : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M l).stk k).length ≤ l.length := by
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_stk_self (M : FinTM2) (l : List (M.Γ M.k₁)) : (haltList M l).stk M.k₁ = l := by
  simp [haltList]

theorem update_haltList_stk (M : FinTM2) (l : List (M.Γ M.k₁)) :
    update (haltList M l).stk M.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [haltList, h]

theorem update_nil_eq_initList (M : OracleFinTM2) (l : List (M.Γ M.k₀)) :
    update (fun _ => []) M.k₀ l = (M.initList l).stk := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [OracleFinTM2.initList, initList, OracleFinTM2.toFinTM2]
  · simp [OracleFinTM2.initList, initList, OracleFinTM2.toFinTM2, h]

theorem initList_compTM (l : List (M₁.Γ M₁.k₀)) :
    (compTM M₁ M₂ φ).initList l = emb₁ (initList M₁ l) := by
  simp only [OracleFinTM2.initList, initList, emb₁, lab₁]
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases h : k = M₁.k₀
    · subst h; simp [mkStk, compTM, OracleFinTM2.toFinTM2]
    · simp [mkStk, compTM, OracleFinTM2.toFinTM2, h]
  · simp [mkStk, compTM, OracleFinTM2.toFinTM2]
  · simp [mkStk, compTM, OracleFinTM2.toFinTM2]

theorem haltList_compTM (l : List (M₂.Γ M₂.k₁)) :
    (compTM M₁ M₂ φ).haltList l = emb₂ (M₂.haltList l) := by
  simp only [OracleFinTM2.haltList, haltList, emb₂]
  congr 1
  funext k
  rcases k with k | k | u
  · simp [mkStk, compTM, OracleFinTM2.toFinTM2]
  · by_cases h : k = M₂.k₁
    · subst h; simp [mkStk, compTM, OracleFinTM2.toFinTM2]
    · simp [mkStk, compTM, OracleFinTM2.toFinTM2, h]
  · simp [mkStk, compTM, OracleFinTM2.toFinTM2]

/-! ### The composition theorem -/

section main

variable {A : Oracle} {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ}
  {eγ : γ → List γΓ} {f : α → β} {g : β → γ}

/-- Symbol translation from `M₁`'s output alphabet to `M₂`'s input alphabet. -/
def glue (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : OTM2ComputableInPolyTime A eβ eγ g) :
    h₁.tm.Γ h₁.tm.k₁ → X h₂.tm :=
  fun y => h₂.inputAlphabet.symm (h₁.outputAlphabet y)

/-- `n + d·p₁(n)`: a bound on the length of the intermediate string. -/
noncomputable def midPoly (h₁ : TM2ComputableInPolyTime eα eβ f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (outDepth h₁.tm) * h₁.time

/-- Time bound of the composite machine: `p₁ + 4·(X + d·p₁) + 2 + p₂ ∘ (X + d·p₁)`
(two copy loops of `2m + 1` steps each, with `m ≤ n + d·p₁(n)`). -/
noncomputable def compTime (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : OTM2ComputableInPolyTime A eβ eγ g) : Polynomial ℕ :=
  h₁.time + Polynomial.C 4 * midPoly h₁ + Polynomial.C 2 + h₂.time.comp (midPoly h₁)

/-- The composite machine with oracle `A` computes `g ∘ f` within `compTime`. -/
noncomputable def compOutputs (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : OTM2ComputableInPolyTime A eβ eγ g) (a : α) :
    OTM2OutputsInTime A (compTM h₁.tm h₂.tm (glue h₁ h₂))
      (List.map h₁.inputAlphabet.invFun (eα a))
      (some (List.map h₂.outputAlphabet.invFun (eγ (g (f a)))))
      ((compTime h₁ h₂).eval (eα a).length) := by
  let φ := glue h₁ h₂
  let inp := List.map h₁.inputAlphabet.invFun (eα a)
  let L := List.map h₁.outputAlphabet.invFun (eβ (f a))
  let inp₂ := List.map h₂.inputAlphabet.invFun (eβ (f a))
  let out := List.map h₂.outputAlphabet.invFun (eγ (g (f a)))
  obtain ⟨⟨s₁, e₁⟩, hs₁⟩ := h₁.outputsFun a
  obtain ⟨⟨s₂, e₂⟩, hs₂⟩ := h₂.outputsFun (f a)
  change (flip bind h₁.tm.step)^[s₁] (some (initList h₁.tm inp)) =
      some (haltList h₁.tm L) at e₁
  change (flip bind (h₂.tm.step A))^[s₂] (some (h₂.tm.initList inp₂)) =
      some (h₂.tm.haltList out) at e₂
  -- Phase 1: run `M₁`.
  have P₁ : (flip bind (cstep φ A))^[s₁]
      (some (emb₁ (M₂ := h₂.tm) (initList h₁.tm inp))) = some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L)) :=
    iter_sim (emb₁ (M₂ := h₂.tm)) (fun _ _ h => step_emb₁ φ A h) _ _ _ e₁
  -- Copy loop 1.
  have P₂ : (flip bind (cstep φ A))^[2 * L.length + 1]
      (some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L))) =
      some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩ :=
    copy₁ φ A L _ _ _ _ _ _ (haltList_stk_self _ _)
  -- Copy loop 2, ending in `M₂`'s initial configuration.
  have hT : ((L.map φ).reverse ++ []).reverse ++ [] = inp₂ := by
    simp [L, inp₂, φ, glue, List.map_map, Function.comp_def]
  have P₃ : (flip bind (cstep φ A))^[
        2 * ((L.map φ).reverse ++ []).length + 1]
      (some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩) =
      some (emb₂ (M₁ := h₁.tm) (h₂.tm.initList inp₂)) := by
    rw [copy₂, update_haltList_stk]
    rw [hT, update_nil_eq_initList]
    rfl
  -- Phase 2: run `M₂` with the oracle.
  have P₄ : (flip bind (cstep φ A))^[s₂]
      (some (emb₂ (M₁ := h₁.tm) (h₂.tm.initList inp₂))) = some (emb₂ (M₁ := h₁.tm) (h₂.tm.haltList out)) :=
    iter_sim (emb₂ (M₁ := h₁.tm)) (fun _ _ h => step_emb₂ φ A h) _ _ _ e₂
  refine ⟨⟨s₂ + (2 * ((L.map φ).reverse ++ []).length + 1) + (2 * L.length + 1) +
    s₁, ?_⟩, ?_⟩
  · show (flip bind ((compTM h₁.tm h₂.tm φ).step A))^[_]
        (some ((compTM h₁.tm h₂.tm φ).initList inp)) =
      Option.map (compTM h₁.tm h₂.tm φ).haltList (some out)
    rw [initList_compTM, Option.map_some, haltList_compTM]
    change (flip bind (cstep φ A))^[_] _ = _
    rw [iterate_add_apply, iterate_add_apply, iterate_add_apply]
    erw [P₁, P₂, P₃, P₄]
    rfl
  · -- Time bound.
    change s₁ ≤ h₁.time.eval (eα a).length at hs₁
    change s₂ ≤ h₂.time.eval (eβ (f a)).length at hs₂
    have hlen := length_iter h₁.tm _ _ _ e₁
    rw [haltList_stk_self] at hlen
    have hinit := initList_stk_length_le h₁.tm inp h₁.tm.k₁
    have hL : L.length = (eβ (f a)).length := by simp [L]
    have hinp : inp.length = (eα a).length := by simp [inp]
    have hm : (eβ (f a)).length ≤
        (eα a).length + outDepth h₁.tm * h₁.time.eval (eα a).length := by
      have := Nat.mul_le_mul_left (outDepth h₁.tm) hs₁
      rw [Nat.mul_comm] at hlen
      omega
    have hp₂ := eval_mono h₂.time hm
    have hmid : (midPoly h₁).eval (eα a).length =
        (eα a).length + outDepth h₁.tm * h₁.time.eval (eα a).length := by
      simp [midPoly]
    simp only [compTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, hmid]
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
      Nat.add_zero, hL]
    omega

end main

end Comp

/-- **F7.** A plain polynomial-time function followed by a polynomial-time oracle machine is a
polynomial-time oracle machine, for the same oracle. -/
noncomputable def oracleComp (A : Oracle) {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : OTM2ComputableInPolyTime A eβ eγ g) :
    OTM2ComputableInPolyTime A eα eγ (g ∘ f) where
  tm := Comp.compTM h₁.tm h₂.tm (Comp.glue h₁ h₂)
  inputAlphabet := h₁.inputAlphabet
  outputAlphabet := h₂.outputAlphabet
  time := Comp.compTime h₁ h₂
  outputsFun := Comp.compOutputs h₁ h₂

/-- **T4 (`P^A ⊆ NP^A`).** A decider is a verifier that ignores its certificate: project the pair
`w#y` to `w` with the plain left-projection machine of `Millennium`, then run the decider. -/
theorem inP_subset_inNP (A : Oracle) (alphabet : Type) [Fintype alphabet] [Nontrivial alphabet]
    (L : Language (List alphabet)) :
    InP A (fin_encoding_string alphabet) L → InNP A (fin_encoding_string alphabet) L := by
  rintro ⟨d, hd, hL⟩
  obtain ⟨hproj⟩ := LeftProjection.polynomial_time_computable.of_linear_time
    LeftProjection.linear_time_correctness alphabet
  refine ⟨alphabet, inferInstance, fun a _ => L a, 0,
    ⟨fun p => d p.1, oracleComp A hproj hd, fun p => hL p.1⟩, fun a => ⟨fun h => ?_, ?_⟩⟩
  · exact ⟨[], by simp, h⟩
  · rintro ⟨_, _, h⟩
    exact h

end Relativization
