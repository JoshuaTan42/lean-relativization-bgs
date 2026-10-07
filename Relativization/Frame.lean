import Mathlib.Data.List.Basic

/-!
# Frames (A1)

`frame i T v = 1^i 0 1^T 0 v` codes a triple (verifier code `i`, time parameter `T`, reversed
input `v`) as a binary string, and `decode` reads it back: `decode x = some (i, T, v)` iff
`x = frame i T v` (`decode_eq_some_iff`). `NOTES.md` §4.11, §5.4.
-/

namespace Relativization

/-- `frame i T v = 1^i 0 1^T 0 v`. -/
def frame (i T : ℕ) (v : List Bool) : List Bool :=
  List.replicate i true ++ false :: (List.replicate T true ++ false :: v)

theorem frame_length (i T : ℕ) (v : List Bool) : (frame i T v).length = i + T + v.length + 2 := by
  simp only [frame, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The number of leading `true`s. -/
def ones : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: l => ones l + 1

/-- The list after its leading `true`s. -/
def dropOnes : List Bool → List Bool
  | [] => []
  | false :: l => false :: l
  | true :: l => dropOnes l

theorem ones_replicate (i : ℕ) (l : List Bool) :
    ones (List.replicate i true ++ false :: l) = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [List.replicate_succ, List.cons_append]
      show ones (List.replicate i true ++ false :: l) + 1 = i + 1
      rw [ih]

theorem dropOnes_replicate (i : ℕ) (l : List Bool) :
    dropOnes (List.replicate i true ++ false :: l) = false :: l := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [List.replicate_succ, List.cons_append]
      exact ih

theorem replicate_ones_append_dropOnes :
    ∀ x : List Bool, List.replicate (ones x) true ++ dropOnes x = x
  | [] => rfl
  | false :: _ => rfl
  | true :: l => by
      show List.replicate (ones l + 1) true ++ dropOnes l = true :: l
      rw [List.replicate_succ, List.cons_append, replicate_ones_append_dropOnes l]

/-- Decoding: the leading ones, a zero, the following ones, a zero, the rest. -/
def decode (x : List Bool) : Option (ℕ × ℕ × List Bool) :=
  match dropOnes x with
  | false :: r =>
    match dropOnes r with
    | false :: v => some (ones x, ones r, v)
    | _ => none
  | _ => none

/-- **A1.** `decode (frame i T v) = some (i, T, v)`. -/
theorem decode_frame (i T : ℕ) (v : List Bool) : decode (frame i T v) = some (i, T, v) := by
  simp only [decode, frame, dropOnes_replicate, ones_replicate]

/-- **A1**, the converse: a string that decodes is the frame of its decoding. -/
theorem eq_frame_of_decode {x : List Bool} {i T : ℕ} {v : List Bool}
    (h : decode x = some (i, T, v)) : x = frame i T v := by
  have hx := replicate_ones_append_dropOnes x
  unfold decode at h
  split at h
  next r hr =>
    have hr' := replicate_ones_append_dropOnes r
    split at h
    next v' hv =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      calc x = List.replicate (ones x) true ++ dropOnes x := hx.symm
        _ = frame (ones x) (ones r) v' := by rw [hr, frame, ← hv, hr']
    next => cases h
  next => cases h

theorem decode_eq_some_iff {x : List Bool} {i T : ℕ} {v : List Bool} :
    decode x = some (i, T, v) ↔ x = frame i T v :=
  ⟨eq_frame_of_decode, fun h => h ▸ decode_frame i T v⟩

theorem frame_inj {i T i' T' : ℕ} {v v' : List Bool} (h : frame i T v = frame i' T' v') :
    i = i' ∧ T = T' ∧ v = v' := by
  have := congrArg decode h
  rw [decode_frame, decode_frame] at this
  simpa using this

theorem length_of_decode {x : List Bool} {i T : ℕ} {v : List Bool}
    (h : decode x = some (i, T, v)) : x.length = i + T + v.length + 2 := by
  rw [eq_frame_of_decode h, frame_length]

end Relativization
