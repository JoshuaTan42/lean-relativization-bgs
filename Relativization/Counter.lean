import Mathlib.Tactic.Linarith
import Relativization.Prog

/-!
# The counter view and the power loop (A3)

Ported from `D:\PvsNP` (commit `c271016`): the section `[LIB]` of `D3OneHot.lean` (the generic
counter-machine view: stacks `SK C` with a Bool output and unit counters, the stack builder
`st f o`, and each `Prog` primitive restated in that view with an exact step count, plus the
runtime `for` loop `stLoop`) and the section `[LIB]` of `Pre.lean` (decrement, multi-target
transfer and the power loop `pow_run`: `p ← p · b^j` within `powB j p b` steps), both verbatim
except for the module header and the namespace; the stage type `MS` of `D3Fam.lean`; and
`outputsOfRunLe` of `Pkg.lean` as `TM2OutputsInTime.ofRunLe`. `NOTES.md` §4.11.

The padding machine of the collapse half (A4) will compute `(|w| + c')^d` in unary with
`pow_run` and emit the frame with `xferES` and `emitOut`.
-/

namespace Relativization.Counter

open Relativization.Prog Turing Function

/-- Stages of a `mul_run` site. -/
inductive MS | head | body | l2 | rest
  deriving DecidableEq, Fintype

/-! ## [LIB] A generic counter-machine view -/

/-- Stacks of a counter machine: a Bool output and unit counters indexed by `C`. -/
inductive SK (C : Type)
  | out
  | c (x : C)
  deriving DecidableEq, Fintype

abbrev SΓ (C : Type) : SK C → Type
  | .out => Bool
  | .c _ => Unit

section View

variable {C : Type} [DecidableEq C]

/-- Stacks from counter values `f` and output `o`. -/
def st (f : C → ℕ) (o : List Bool) : ∀ k, List (SΓ C k)
  | .out => o
  | .c x => cnt () (f x)

omit [DecidableEq C] in
@[simp] theorem st_c (f : C → ℕ) (o : List Bool) (x : C) : st f o (.c x) = cnt () (f x) := rfl
omit [DecidableEq C] in
@[simp] theorem st_out (f : C → ℕ) (o : List Bool) : st f o .out = o := rfl

theorem update_st_c (f : C → ℕ) (o : List Bool) (x : C) (n : ℕ) :
    update (st f o) (.c x) (cnt () n) = st (update f x n) o := by
  funext k
  rcases k with _ | y
  · rfl
  · by_cases h : y = x
    · subst h; simp
    · rw [update_of_ne (by simpa using h)]; simp [update_of_ne h]

theorem update_st_nil (f : C → ℕ) (o : List Bool) (x : C) :
    update (st f o) (.c x) [] = st (update f x 0) o := update_st_c f o x 0

theorem update_st_out (f : C → ℕ) (o l : List Bool) : update (st f o) .out l = st f l := by
  funext k
  rcases k with _ | y
  · simp
  · rw [update_of_ne (by simp)]; rfl

theorem addU_nil {K : Type} [DecidableEq K] {Γ : K → Type} (n : ℕ) (S : ∀ k, List (Γ k)) :
    addU [] n S = S := rfl

variable {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem emitS {self next : Λ} {x : C} {n : ℕ}
    (hp : M self = emitR (.c x) (List.replicate n ()) next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (n + F x)) o⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_c, show List.replicate n () = cnt () n from rfl, cnt_add, update_st_c] at this
  exact this

theorem emitOut {self next : Λ} {ys : List Bool} (hp : M self = emitR .out ys next)
    (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st F (ys ++ o)⟩ := by
  have := emitR_run hp v (st F o)
  rw [st_out, update_st_out] at this
  exact this

theorem incS {self next : Λ} {x : C} (hp : M self = incr (.c x) () next) (F : C → ℕ) (v : Bool)
    (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some next, v, st (update F x (F x + 1)) o⟩ := by
  have := incr_run_cnt hp v (S := st F o) (n := F x) rfl
  rw [update_st_c] at this
  exact this

theorem drainS {self next : Λ} {x : C} (hp : M self = xfer (.c x) [] self next) (F : C → ℕ)
    (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (update F x 0) o⟩ := by
  have := xfer_run hp (by simp [List.NodupKeys]) (by simp) () (F x) v (st F o) rfl
  rw [addU_nil, update_st_nil] at this
  exact this

theorem xferES {self next : Λ} {x : C} {ys : List Bool}
    (hp : M self = xferE (.c x) .out ys self next) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩
      ⟨some next, false, st (update F x 0) (rep ys (F x) ++ o)⟩ := by
  have := xferE_run hp (by simp) () (F x) v (st F o) rfl
  rw [update_st_nil, update_st_out, st_out] at this
  exact this

theorem copyS {l₁ l₂ next : Λ} {a c t : C}
    (h₁ : M l₁ = xfer (.c a) [⟨.c c, ()⟩, ⟨.c t, ()⟩] l₁ l₂)
    (h₂ : M l₂ = xfer (.c t) [⟨.c a, ()⟩] l₂ next)
    (hac : a ≠ c) (hat : a ≠ t) (hct : c ≠ t) (F : C → ℕ) (ht : F t = 0) (v : Bool)
    (o : List Bool) :
    Run M (2 * F a + 2) ⟨some l₁, v, st F o⟩
      ⟨some next, false, st (update F c (F a + F c)) o⟩ := by
  have := copy_run h₁ h₂ (by simpa using hac) (by simpa using hat) (by simpa using hct) (F a)
    (F c) v (st F o) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

/-- A `mul_run` site `c += a · b` (index stack `ad`, scratch `t`), for any counter machine. -/
def mulS (a ad b c t : C) (mk : MS → Λ) (next : Λ) : MS → TM2.Stmt (SΓ C) Λ Bool
  | .head => forHead (.c a) (.c ad) () (mk .body) (mk .rest)
  | .body => xfer (.c b) [⟨.c c, ()⟩, ⟨.c t, ()⟩] (mk .body) (mk .l2)
  | .l2 => xfer (.c t) [⟨.c b, ()⟩] (mk .l2) (mk .head)
  | .rest => xfer (.c ad) [⟨.c a, ()⟩] (mk .rest) next

theorem mulS_run {a ad b c t : C} {mk : MS → Λ} {next : Λ}
    (hp : ∀ s, M (mk s) = mulS a ad b c t mk next s)
    (hnd : ([.c a, .c ad, .c b, .c c, .c t] : List (SK C)).Nodup)
    (F : C → ℕ) (had : F ad = 0) (ht : F t = 0) (v : Bool) (o : List Bool) :
    Run M (F a * (2 * F b + 3) + F a + 2) ⟨some (mk .head), v, st F o⟩
      ⟨some next, false, st (update F c (F a * F b + F c)) o⟩ := by
  have := mul_run (hp .head) (hp .body) (hp .l2) (hp .rest) hnd (F a) (F b) (F c) v (st F o) rfl
    (by simp [had]) rfl rfl (by simp [ht])
  rw [update_st_c] at this
  exact this

/-- Gap emission (`emitDiff_run`) in the counter view. -/
theorem gapS {P Q T1 T2 : C} {ys : List Bool} {dec cmpL emitL ifZero next : Λ}
    {r rB out : Ordering → Λ}
    (hdec : M dec = decr (.c P) ifZero cmpL)
    (hcmp : M cmpL = cmpStep (.c P) (.c Q) (.c T1) (.c T2) () () cmpL (r .lt) (r .eq) (r .gt))
    (hr : ∀ o, M (r o) = xfer (.c T1) [⟨.c P, ()⟩] (r o) (rB o))
    (hrB : ∀ o, M (rB o) = xfer (.c T2) [⟨.c Q, ()⟩] (rB o) (out o))
    (hout : ∀ o, out o = if o = .eq then next else emitL)
    (hemit : M emitL = emitR .out ys dec)
    (hnd : ([.c P, .c Q, .c T1, .c T2, .out] : List (SK C)).Nodup) (q gap : ℕ) (F : C → ℕ)
    (hP : F P = q + gap + 1) (hQ : F Q = q) (h1 : F T1 = 0) (h2 : F T2 = 0) (v : Bool)
    (o : List Bool) :
    Run M (gap * (3 * q + 6) + 3 * q + 4) ⟨some dec, v, st F o⟩
      ⟨some next, false, st (update F P q) (rep ys gap ++ o)⟩ := by
  have := emitDiff_run hdec hcmp hr hrB hout hemit hnd q gap v (st F o) (by simp [hP])
    (by simp [hQ]) (by simp [h1]) (by simp [h2])
  rw [update_st_c, update_st_out, st_out] at this
  exact this

/-- Transport a budgeted run along an equality of counter functions. -/
theorem bud_st {K X : ℕ} {F F' : C → ℕ} {l : Option Λ} {v : Bool} {o : List Bool}
    {d : TM2.Cfg (SΓ C) Λ Bool} (h : F = F') (h' : Bud M K X ⟨l, v, st F' o⟩ d) :
    Bud M K X ⟨l, v, st F o⟩ d := h ▸ h'

omit [DecidableEq C] in
theorem st_eta (S : ∀ k, List (SΓ C k)) : S = st (fun x => (S (.c x)).length) (S .out) := by
  funext k
  rcases k with _ | x
  · rfl
  · exact List.eq_replicate_iff.2 ⟨rfl, fun _ _ => rfl⟩

/-- **A runtime `for` loop in the counter view.** The body runs with the loop counter `c` holding
the index value `t` (descending, `n-1, …, 0`) and must restore every counter; it prepends
`blk t`. The loop prepends the blocks in ascending order. -/
theorem stLoop {c cd : C} {head body rest next : Λ}
    (hHead : M head = forHead (.c c) (.c cd) () body rest)
    (hRest : M rest = xfer (.c cd) [⟨.c c, ()⟩] rest next) (hc : c ≠ cd) (n B : ℕ)
    (blk : ℕ → List Bool) (f : C → ℕ) (hfc : f c = n) (hfcd : f cd = 0)
    (hbody : ∀ t < n, ∀ o, ∃ v', RunLe M B
      ⟨some body, true, st (update (update f c t) cd (n - t)) o⟩
      ⟨some head, v', st (update (update f c t) cd (n - t)) (blk t ++ o)⟩)
    (v : Bool) (o : List Bool) :
    RunLe M (n * (B + 1) + n + 2) ⟨some head, v, st f o⟩
      ⟨some next, false, st f ((List.range n).flatMap blk ++ o)⟩ := by
  obtain ⟨S', hrun, h'c, h'cd, h'o, h'x⟩ := forLoop_le (M := M) (c := .c c) (cd := .c cd)
    (uc := ()) (ucd := ()) hHead
    hRest (by simpa using hc) n B
    (fun i S => S .out = (List.range' (n - i) i).flatMap blk ++ o ∧
      ∀ x, x ≠ c → x ≠ cd → (S (.c x)).length = f x)
    (fun i S S' h ⟨h1, h2⟩ => ⟨by rw [h .out (by simp) (by simp), h1],
      fun x hx1 hx2 => by rw [h (.c x) (by simpa using hx1) (by simpa using hx2), h2 x hx1 hx2]⟩)
    (fun i hi S hS1 hS2 ⟨h1, h2⟩ => by
      have hS : S = st (update (update f c (n - 1 - i)) cd (n - (n - 1 - i))) (S .out) := by
        funext k
        rcases k with _ | x
        · rfl
        · by_cases hx1 : x = c
          · subst hx1; rw [hS1]; simp [hc]
          · by_cases hx2 : x = cd
            · subst hx2; rw [hS2]; simp only [st_c, update_self]; congr 1; omega
            · simp only [st_c, update_of_ne hx2, update_of_ne hx1]
              exact List.eq_replicate_iff.2 ⟨h2 x hx1 hx2, fun _ _ => rfl⟩
      obtain ⟨v', r⟩ := hbody (n - 1 - i) (by omega) (S .out)
      rw [← hS] at r
      refine ⟨v', _, r, ?_, ?_, ?_, fun x hx1 hx2 => ?_⟩
      · rw [hS1]; simp [hc]
      · rw [hS2]; simp only [st_c, update_self]; congr 1; omega
      · simp only [st_out, h1]
        rw [show n - (i + 1) = n - 1 - i by omega, List.range'_succ,
          show n - 1 - i + 1 = n - i by omega, List.flatMap_cons, List.append_assoc]
      · simp [update_of_ne hx1, update_of_ne hx2])
    v (st f o) (by simp [hfc]) (by simp [hfcd]) ⟨by simp, fun x _ _ => by simp⟩
  have hS' : S' = st f ((List.range n).flatMap blk ++ o) := by
    funext k
    rcases k with _ | x
    · rw [h'o, Nat.sub_self, ← List.range_eq_range']; rfl
    · by_cases hx1 : x = c
      · subst hx1; rw [h'c]; simp [hfc]
      · by_cases hx2 : x = cd
        · subst hx2; rw [h'cd]; simp [hfcd]
        · exact List.eq_replicate_iff.2 ⟨h'x x hx1 hx2, fun _ _ => rfl⟩
  rw [hS'] at hrun
  exact hrun

end View

/-! ## [LIB] Counter-view additions: decrement, multi-target transfer, the power loop -/

section CLib

variable {C : Type} [DecidableEq C] {Λ : Type} {M : Λ → TM2.Stmt (SΓ C) Λ Bool}

theorem decS_pos {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) {j : ℕ} (hx : F x = j + 1) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifPos, true, st (update F x j) o⟩ := by
  have := decr_run_cnt hp v (S := st F o) (u := ()) (n := j) (by simp [hx])
  rw [update_st_c] at this
  exact this

theorem decS_zero {self ifZero ifPos : Λ} {x : C} (hp : M self = decr (.c x) ifZero ifPos)
    (F : C → ℕ) (hx : F x = 0) (v : Bool) (o : List Bool) :
    Run M 1 ⟨some self, v, st F o⟩ ⟨some ifZero, false, st F o⟩ :=
  decr_run_zero hp v (by simp [hx])

/-- Unit targets of a multi-target transfer. -/
def tg (ys : List C) : List (Σ k, SΓ C k) := ys.map fun y => ⟨.c y, ()⟩

omit [DecidableEq C] in
theorem tg_keys (ys : List C) : (tg ys).keys = ys.map SK.c := by
  simp [tg, List.keys]

omit [DecidableEq C] in
theorem tg_nodupKeys {ys : List C} (h : ys.Nodup) : (tg ys).NodupKeys := by
  unfold List.NodupKeys
  rw [tg_keys]
  exact h.map (fun _ _ h => by cases h; rfl)

theorem dlookup_tg (ys : List C) (z : C) :
    List.dlookup (SK.c z) (tg ys) = if z ∈ ys then some () else none := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : z = y
      · subst h; simp [tg, List.dlookup_cons_eq]
      · rw [tg, List.map_cons, List.dlookup_cons_ne _ _ (by simpa using h)]
        rw [← tg, ih]; simp [h]

theorem dlookup_tg_out (ys : List C) : List.dlookup (SK.out) (tg ys) = none := by
  rw [List.dlookup_eq_none, tg_keys]; simp

/-- Counter function after `xfer x → ys`. -/
def xf (F : C → ℕ) (x : C) (ys : List C) : C → ℕ :=
  fun z => if z = x then 0 else if z ∈ ys then F z + F x else F z

/-- **Multi-target transfer** in the counter view: drain `x`, adding its value to every `y ∈ ys`. -/
theorem xferS {self next : Λ} {x : C} {ys : List C} (hp : M self = xfer (.c x) (tg ys) self next)
    (hnd : ys.Nodup) (hx : x ∉ ys) (F : C → ℕ) (v : Bool) (o : List Bool) :
    Run M (F x + 1) ⟨some self, v, st F o⟩ ⟨some next, false, st (xf F x ys) o⟩ := by
  have := xfer_run hp (tg_nodupKeys hnd) (by rw [tg_keys]; simpa using hx) () (F x) v (st F o) rfl
  have e : addU (tg ys) (F x) (update (st F o) (SK.c x) []) = st (xf F x ys) o := by
    funext k
    rcases k with _ | z
    · simp [addU, dlookup_tg_out]
    · simp only [addU, dlookup_tg]
      by_cases hz : z = x
      · subst hz; simp [xf, hx]
      · rw [update_of_ne (by simpa using hz)]
        by_cases hy : z ∈ ys
        · simp [xf, hz, hy, add_comm]
        · simp [xf, hz, hy]
  rw [e] at this
  exact this

/-- Power-loop stages. -/
inductive PW
  | hd
  | mul (s : MS)
  | drn
  | mv
  deriving DecidableEq, Fintype

/-- `p ← p · b^kc`: decrement `kc`; `q += p·b`; drain `p`; move `q` to `p`; repeat. -/
def powS (b kc p q ad t : C) (mk : PW → Λ) (exit : Λ) : PW → TM2.Stmt (SΓ C) Λ Bool
  | .hd => decr (.c kc) exit (mk (.mul .head))
  | .mul s => mulS p ad b q t (fun s => mk (.mul s)) (mk .drn) s
  | .drn => xfer (.c p) [] (mk .drn) (mk .mv)
  | .mv => xfer (.c q) (tg [p]) (mk .mv) (mk .hd)

/-- Step budget of the power loop (`j` rounds, start value `p`, base `b`). -/
def powB (j p b : ℕ) : ℕ := j * (p * (b + 1) ^ j * (3 * b + 5) + 5) + 1

/-- **The power loop.** From `kc = j`, `q = ad = t = 0`: ends with `p ← p · b^j`, `kc = 0`. -/
theorem pow_run {b kc p q ad t : C} {mk : PW → Λ} {exit : Λ}
    (hp : ∀ s, M (mk s) = powS b kc p q ad t mk exit s)
    (hnd : [b, kc, p, q, ad, t].Nodup) :
    ∀ (j : ℕ) (F : C → ℕ), F kc = j → F q = 0 → F ad = 0 → F t = 0 → ∀ (v : Bool) (o : List Bool),
      RunLe M (powB j (F p) (F b)) ⟨some (mk .hd), v, st F o⟩
        ⟨some exit, false, st (update (update F p (F p * F b ^ j)) kc 0) o⟩ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨hbk, hbp, hbq, hbad, hbt⟩, ⟨hkp, hkq, hkad, hkt⟩, ⟨hpq, hpad, hpt⟩, ⟨hqad, hqt⟩,
    hadt, -⟩ := hnd
  intro j
  induction j with
  | zero =>
      intro F hk hq had ht v o
      have r := decS_zero (hp .hd) F hk v o
      have hF : update (update F p (F p * F b ^ 0)) kc 0 = F := by
        funext z; by_cases h1 : z = kc
        · subst h1; simp [hk]
        · by_cases h2 : z = p
          · subst h2; simp [h1]
          · simp [h1]
      rw [hF]; exact r.le (by simp [powB])
  | succ j ih =>
      intro F hk hq had ht v o
      -- decrement
      have r1 := decS_pos (hp .hd) F hk v o
      set F1 := update F kc j with hF1
      -- q += p * b
      have r2 := mulS_run (a := p) (ad := ad) (b := b) (c := q) (t := t)
        (mk := fun s => mk (.mul s)) (next := mk .drn) (M := M) (fun s => hp (.mul s))
        (by simp [hpad, (Ne.symm hbp), hpq, hpt, (Ne.symm hbad), (Ne.symm hqad), hadt, hbq, hbt, hqt])
        F1 (by simp [hF1, (Ne.symm hkad), had]) (by simp [hF1, (Ne.symm hkt), ht]) true o
      set F2 := update F1 q (F1 p * F1 b + F1 q) with hF2
      -- drain p
      have r3 := drainS (hp .drn) F2 false o
      set F3 := update F2 p 0 with hF3
      -- move q to p
      have r4 := xferS (hp .mv) (by simp) (by simpa using (Ne.symm hpq)) F3 false o
      set F4 := xf F3 q [p] with hF4
      have hF1p : F1 p = F p := by rw [hF1, update_of_ne (Ne.symm hkp)]
      have hF1b : F1 b = F b := by rw [hF1, update_of_ne hbk]
      have hF1q : F1 q = 0 := by rw [hF1, update_of_ne (Ne.symm hkq), hq]
      have hF2p : F2 p = F p := by rw [hF2, update_of_ne hpq, hF1p]
      have hF3q : F3 q = F p * F b := by
        rw [hF3, update_of_ne (Ne.symm hpq), hF2, update_self, hF1p, hF1b, hF1q, add_zero]
      have hrest : ∀ z, z ≠ q → z ≠ p → z ≠ kc → F4 z = F z := by
        intro z h1 h2 h3
        simp only [hF4, xf, if_neg h1, List.mem_singleton, if_neg h2, hF3, hF2, hF1,
          update_of_ne h1, update_of_ne h2, update_of_ne h3]
      have h4p : F4 p = F p * F b := by
        simp only [hF4, xf, if_neg hpq, List.mem_singleton, if_true, hF3, update_self, zero_add]
        exact hF3q
      have h4k : F4 kc = j := by
        simp only [hF4, xf, if_neg hkq, List.mem_singleton, if_neg hkp, hF3, hF2, hF1,
          update_of_ne hkp, update_of_ne hkq, update_self]
      have h4b : F4 b = F b := hrest b hbq hbp hbk
      have r5 := ih F4 h4k (by simp [hF4, xf])
        (by rw [hrest ad (Ne.symm hqad) (Ne.symm hpad) (Ne.symm hkad), had])
        (by rw [hrest t (Ne.symm hqt) (Ne.symm hpt) (Ne.symm hkt), ht]) false o
      have hend : update (update F4 p (F4 p * F4 b ^ j)) kc 0 =
          update (update F p (F p * F b ^ (j + 1))) kc 0 := by
        funext z
        by_cases h1 : z = kc
        · subst h1; simp
        rw [update_of_ne h1, update_of_ne h1]
        by_cases h2 : z = p
        · subst h2; rw [update_self, update_self, h4p, h4b, pow_succ]; ring
        rw [update_of_ne h2, update_of_ne h2]
        by_cases h3 : z = q
        · subst h3; simp [hF4, xf, hq]
        exact hrest z h3 h2 h1
      rw [hend, h4p, h4b] at r5
      rw [hF2p] at r3
      rw [hF3q] at r4
      rw [hF1p, hF1b] at r2
      have := ((((r1.le le_rfl).trans (r2.le le_rfl)).trans (r3.le le_rfl)).trans
        (r4.le le_rfl)).trans r5
      refine this.mono ?_
      unfold powB
      have hpw : F p * F b * (F b + 1) ^ j ≤ F p * (F b + 1) ^ (j + 1) := by
        rw [pow_succ, mul_assoc, mul_comm (F b)]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_succ _))
      have hp1 : F p ≤ F p * (F b + 1) ^ (j + 1) :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos (Nat.succ_pos _))
      have h1 := Nat.mul_le_mul_right (3 * F b + 5) hp1
      have h2 := Nat.mul_le_mul_left j (Nat.add_le_add_right
        (Nat.mul_le_mul_right (3 * F b + 5) hpw) 5)
      nlinarith [h1, h2]

end CLib

/-! ## Packaging a bounded run (PvsNP `Pkg.outputsOfRunLe`) -/

/-- A bounded run from `initList` to `haltList` is a `TM2OutputsInTime` certificate. -/
noncomputable def _root_.Turing.TM2OutputsInTime.ofRunLe {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : List (tm.Γ tm.k₁)} {B : ℕ} (h : RunLe tm.m B (initList tm l) (haltList tm l')) :
    TM2OutputsInTime tm l (some l') B where
  steps := Classical.choose h
  evals_in_steps := (Classical.choose_spec h).2
  steps_le_m := (Classical.choose_spec h).1

end Relativization.Counter
