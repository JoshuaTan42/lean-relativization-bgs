import Relativization.Frame
import Relativization.Codes
import Relativization.Queries

/-!
# The collapse oracle `A` (A2)

Decision D6 (`NOTES.md` §5.4): a frame `x = frame i T v` is in `A` iff verifier code `i`, run
with oracle `A` on `v.reverse # y` for some certificate `y` with `|y| ≤ |v|^{k_i}`, outputs
`[true]` within the step budget `⌊(T ∸ μ_i(|v|)) / (D_i + 1)⌋`, where `μ_i(n) = n + 1 + n^{k_i}`
and `D_i` is the depth of the coded machine.

`A` is built by levels (`Univ.level`, a primitive recursion on the length: level `m + 1` adds
the strings of length `m` accepted with oracle level `m`), so it exists outright. The content
is that it satisfies the untruncated self-referential equation

* `Univ.mem_univOracle` (†): `x ∈ A ↔ Phi A x`,

because every query asked within the budget is strictly shorter than the frame
(`Univ.length_lt_of_mem_queries`, Proposition 5 of §5.5), so by the sharp locality lemma L6'
the run cannot see the truncation (`Univ.Phi_congr`). `A` is the only oracle satisfying (†)
(`Univ.eq_univOracle_of_fixpoint`). `NOTES.md` §4.11 has the statements and the argument.
-/

namespace Relativization

open Turing Function Computability Millennium

namespace Univ

/-- The machine of verifier code `i`. -/
noncomputable abbrev M (i : ℕ) : OracleFinTM2 := (vEnum i).N.toOracleFinTM2

/-- `μ_i(n) = n + 1 + n^{k_i}`: the longest verifier input `w#y` with `|w| = n` and
`|y| ≤ n^{k_i}`. -/
noncomputable def mu (i n : ℕ) : ℕ := n + 1 + n ^ (vEnum i).k

/-- **D6.** The step budget `⌊(T ∸ μ_i(n)) / (D_i + 1)⌋`. -/
noncomputable def budget (i T n : ℕ) : ℕ := (T - mu i n) / ((M i).depth + 1)

/-- `w#y` as the machine of code `i` reads it. -/
noncomputable def input (i : ℕ) (w : List Bool) (y : List (Fin (vEnum i).g)) :
    List (Fin ((vEnum i).N.a (vEnum i).N.k₀)) :=
  ((pair_encoding (fin_encoding_string Bool) (fin_encoding_string (Fin (vEnum i).g))).encode
    (w, y)).map (vEnum i).inE.symm

theorem input_length (i : ℕ) (w : List Bool) (y : List (Fin (vEnum i).g)) :
    (input i w y).length = w.length + 1 + y.length :=
  (List.length_map _).trans (pair_encoding.length_eq _ _ _)

/-- `Acc O i T v`: some certificate `y ∈ [g_i]*` with `|y| ≤ |v|^{k_i}` makes `M_i^O` output
`[true]` on `v.reverse # y` within the budget. -/
def Acc (O : Oracle) (i T : ℕ) (v : List Bool) : Prop :=
  ∃ y : List (Fin (vEnum i).g), y.length ≤ v.length ^ (vEnum i).k ∧
    Nonempty (OTM2OutputsInTime O (M i) (input i v.reverse y)
      (some [(vEnum i).outE.symm true]) (budget i T v.length))

/-- The membership condition `Φ(O, x)` (§5.4): `x` is a frame `frame i T v` and `Acc O i T v`. -/
def Phi (O : Oracle) (x : List Bool) : Prop :=
  ∃ i T v, decode x = some (i, T, v) ∧ Acc O i T v

theorem Phi_frame (O : Oracle) (i T : ℕ) (v : List Bool) :
    Phi O (frame i T v) ↔ Acc O i T v := by
  constructor
  · rintro ⟨i', T', v', h, ha⟩
    rw [decode_frame] at h
    obtain ⟨rfl, rfl, rfl⟩ : i = i' ∧ T = T' ∧ v = v' := by simpa using h
    exact ha
  · exact fun ha => ⟨i, T, v, decode_frame i T v, ha⟩

/-- The levels `A_0 = ∅`, `A_{m+1} = A_m ∪ {x | |x| = m ∧ Φ(A_m, x)}`. -/
def level : ℕ → Oracle
  | 0 => ∅
  | m + 1 => level m ∪ {x | x.length = m ∧ Phi (level m) x}

end Univ

/-- **D6.** The oracle `A = ⋃_m A_m`. -/
def univOracle : Oracle := {x | ∃ m, x ∈ Univ.level m}

namespace Univ

/-! ### The levels -/

theorem mem_level_succ (m : ℕ) (x : List Bool) :
    x ∈ level (m + 1) ↔ x ∈ level m ∨ (x.length = m ∧ Phi (level m) x) :=
  Iff.rfl

theorem length_lt_of_mem_level {m : ℕ} {x : List Bool} (h : x ∈ level m) : x.length < m := by
  induction m with
  | zero => exact absurd h (Set.notMem_empty x)
  | succ m ih =>
      rcases (mem_level_succ m x).mp h with h | ⟨h, _⟩
      · exact (ih h).trans (Nat.lt_succ_self m)
      · omega

theorem level_mono : Monotone level :=
  monotone_nat_of_le_succ fun _ => Set.subset_union_left

theorem mem_level_iff_of_lt {m m' : ℕ} {x : List Bool} (hx : x.length < m) (h : m ≤ m') :
    x ∈ level m' ↔ x ∈ level m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Iff.rfl
  | succ d ih =>
      rw [← Nat.add_assoc, mem_level_succ, ih]
      constructor
      · rintro (h' | ⟨h', _⟩)
        · exact h'
        · omega
      · exact Or.inl

theorem mem_univOracle_iff_level (x : List Bool) :
    x ∈ univOracle ↔ x ∈ level (x.length + 1) :=
  ⟨fun ⟨_, hm⟩ => (mem_level_iff_of_lt (Nat.lt_succ_self _) (length_lt_of_mem_level hm)).mp hm,
    fun h => ⟨_, h⟩⟩

theorem univOracle_inter_eq_level (m : ℕ) : univOracle ∩ {z | z.length < m} = level m := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hl⟩
    exact (mem_level_iff_of_lt (Nat.lt_succ_self _) hl).mpr ((mem_univOracle_iff_level x).mp hx)
  · exact fun h => ⟨⟨m, h⟩, length_lt_of_mem_level h⟩

/-- **(★)**, the plan's form: `x ∈ A ↔ Φ(A ∩ {z | |z| < |x|}, x)`. -/
theorem mem_univOracle_iff_trunc (x : List Bool) :
    x ∈ univOracle ↔ Phi (univOracle ∩ {z | z.length < x.length}) x := by
  rw [mem_univOracle_iff_level, mem_level_succ, univOracle_inter_eq_level]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact absurd (length_lt_of_mem_level h) (lt_irrefl _)
    · exact h
  · exact fun h => Or.inr ⟨rfl, h⟩

/-! ### Proposition 5: every query within the budget is shorter than the frame -/

/-- **Proposition 5** (§5.5). Every query asked within the budget, on every admissible
certificate, under every oracle, is strictly shorter than the frame. -/
theorem length_lt_of_mem_queries {O : Oracle} {i T : ℕ} {v : List Bool}
    {y : List (Fin (vEnum i).g)} (hy : y.length ≤ v.length ^ (vEnum i).k) {z : List Bool}
    (hz : z ∈ (M i).queries O (input i v.reverse y) (budget i T v.length)) :
    z.length < (frame i T v).length := by
  rw [frame_length]
  have h₁ : z.length ≤ (input i v.reverse y).length + budget i T v.length * (M i).depth :=
    (M i).length_le_of_mem_queries hz
  rw [input_length, List.length_reverse] at h₁
  have h₂ : budget i T v.length * ((M i).depth + 1) ≤ T - mu i v.length :=
    Nat.div_mul_le_self _ _
  rw [Nat.mul_succ] at h₂
  have h₃ : 0 < budget i T v.length := by
    rcases Nat.eq_zero_or_pos (budget i T v.length) with h0 | h0
    · rw [h0] at hz
      simp [OracleFinTM2.queries] at hz
    · exact h0
  unfold mu at h₂
  omega

/-! ### Truncation is invisible, and the self-referential equation -/

/-- `Acc O i T v` depends on `O` only on strings shorter than the frame (L6' and
Proposition 5). -/
theorem Acc_congr {O O' : Oracle} (i T : ℕ) (v : List Bool)
    (h : ∀ z : List Bool, z.length < (frame i T v).length → (z ∈ O ↔ z ∈ O')) :
    Acc O i T v ↔ Acc O' i T v :=
  exists_congr fun _ => and_congr_right fun hy =>
    (M i).outputsInTime_congr_queries _ _ _ fun z hz => h z (length_lt_of_mem_queries hy hz)

/-- `Phi O x` depends on `O` only on strings shorter than `x`. -/
theorem Phi_congr {O O' : Oracle} (x : List Bool)
    (h : ∀ z : List Bool, z.length < x.length → (z ∈ O ↔ z ∈ O')) : Phi O x ↔ Phi O' x :=
  exists₃_congr fun i T v => and_congr_right fun hd =>
    Acc_congr i T v (by rw [← eq_frame_of_decode hd]; exact h)

/-- **(†)**, Theorem 6 of §5.6: `A` satisfies the self-referential equation `x ∈ A ↔ Φ(A, x)`. -/
theorem mem_univOracle (x : List Bool) : x ∈ univOracle ↔ Phi univOracle x :=
  (mem_univOracle_iff_trunc x).trans (Phi_congr x fun z hz => by simp [hz])

/-- **Uniqueness** (Theorem 6, second half): `A` is the only oracle satisfying (†). -/
theorem eq_univOracle_of_fixpoint {B : Oracle} (hB : ∀ x, x ∈ B ↔ Phi B x) : B = univOracle := by
  have key : ∀ m (x : List Bool), x.length < m → (x ∈ B ↔ x ∈ level m) := by
    intro m
    induction m with
    | zero => exact fun x hx => absurd hx (Nat.not_lt_zero _)
    | succ m ih =>
        intro x hx
        rw [mem_level_succ]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
        · rw [ih x hx]
          exact ⟨Or.inl, fun h => h.elim id fun ⟨h, _⟩ => absurd h (by omega)⟩
        · rw [hB x, Phi_congr x fun z hz => ih z (by omega)]
          constructor
          · exact fun h => Or.inr ⟨hx, h⟩
          · rintro (h | ⟨_, h⟩)
            · exact absurd (length_lt_of_mem_level h) (by omega)
            · exact h
  ext x
  rw [mem_univOracle_iff_level]
  exact key _ x (Nat.lt_succ_self _)

end Univ

end Relativization
