/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.ContinuedFractions.Translations
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `Mathlib/Algebra/ContinuedFractions/Computation/Basic.lean`.
The file consists of three sections:
1. Recurrences and inversion lemmas for `IntFractPair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`IntFractPair.stream`, `IntFractPair.seq1`, and `GenContFract.of`) are connected,
   i.e. how the values are moved along the structures and the termination of one sequence implies
   the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `get?_of_eq_some_of_succ_get?_intFractPair_stream` and
  `get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/

public section

assert_not_exists Finset

namespace GenContFract

open GenContFract (of)

-- Fix a discrete linear ordered division ring with `floor` function and a value `v`.
variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K}

namespace IntFractPair



/--
theorem `stream_zero` / 定理 `stream_zero`

English:
theorem stream_zero
  given: (v : K)
  statement: IntFractPair.stream v 0 = some (IntFractPair.of v)
  proof: rfl

中文:
定理 stream_zero
  条件: (v : K)
  结论: 整数FractPair.stream v 0 = some (整数FractPair.of v)
  证明: rfl
-/
theorem stream_zero (v : K) : IntFractPair.stream v 0 = some (IntFractPair.of v) :=
  rfl

variable {n : Nat}

/--
theorem `stream_eq_none_of_fr_eq_zero` / 定理 `stream_eq_none_of_fr_eq_zero`

English:
theorem stream_eq_none_of_fr_eq_zero
  statement: {ifp_n : IntFractPair K}
  proof: by
  grind [IntFractPair.stream]

中文:
定理 stream_eq_none_of_fr_eq_zero
  结论: {ifp_n : 整数FractPair K}
  证明: by
  grind [IntFractPair.stream]

Depends on / 依赖: IntFractPair, IntFractPair.stream, stream
-/
theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none := by
  grind [IntFractPair.stream]

/--
theorem `succ_nth_stream_eq_none_iff` / 定理 `succ_nth_stream_eq_none_iff`

English:
theorem succ_nth_stream_eq_none_iff
  proof: by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]

中文:
定理 succ_nth_stream_eq_none_iff
  证明: by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]

Depends on / 依赖: IntFractPair, IntFractPair.stream, imp_false, stream
-/
theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ exists ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]

/--
theorem `succ_nth_stream_eq_some_iff` / 定理 `succ_nth_stream_eq_some_iff`

English:
theorem succ_nth_stream_eq_some_iff
  given: {ifp_succ_n : IntFractPair K}
  proof: by
  simp [IntFractPair.stream, ite_eq_iff, Option.bind_eq_some_iff]

中文:
定理 succ_nth_stream_eq_some_iff
  条件: {ifp_succ_n : 整数FractPair K}
  证明: by
  simp [IntFractPair.stream, ite_eq_iff, Option.bind_eq_some_iff]

Depends on / 依赖: IntFractPair, IntFractPair.stream, Option.bind_eq_some_iff, bind_eq_some_iff, ite_eq_iff, stream
-/
theorem succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} :
    IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      exists ifp_n : IntFractPair K,
        IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr != 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simp [IntFractPair.stream, ite_eq_iff, Option.bind_eq_some_iff]

/--
theorem `stream_succ_of_some` / 定理 `stream_succ_of_some`

English:
theorem stream_succ_of_some
  statement: {p : IntFractPair K} (h : IntFractPair.stream v n = some p)
  proof: succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

中文:
定理 stream_succ_of_some
  结论: {p : 整数FractPair K} (h : 整数FractPair.stream v n = some p)
  证明: succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

Depends on / 依赖: succ_nth_stream_eq_some_iff, succ_nth_stream_eq_some_iff.mpr
-/
theorem stream_succ_of_some {p : IntFractPair K} (h : IntFractPair.stream v n = some p)
    (h' : p.fr != 0) : IntFractPair.stream v (n + 1) = some (IntFractPair.of p.fr⁻¹) :=
  succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

/--
theorem `stream_succ_of_int` / 定理 `stream_succ_of_int`

English:
theorem stream_succ_of_int
  given: [IsStrictOrderedRing K] (a : Int) (n : Nat)
  proof: by
  induction n with
  | zero =>
    refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)

中文:
定理 stream_succ_of_int
  条件: [IsStrictOrderedRing K] (a : 整数) (n : 自然数)
  证明: by
  induction n with
  | zero =>
    refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)

Depends on / 依赖: Int.fract_intCast, IntFractPair, IntFractPair.of, IntFractPair.stream_eq_none_of_fr_eq_zero, IntFractPair.stream_zero, IntFractPair.succ_nth_stream_eq_none_iff.mpr, Or.inl, fract_intCast, stream_eq_none_of_fr_eq_zero, stream_zero, succ_nth_stream_eq_none_iff
-/
theorem stream_succ_of_int [IsStrictOrderedRing K] (a : Int) (n : Nat) :
    IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
    refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)

/--
theorem `exists_succ_nth_stream_of_fr_zero` / 定理 `exists_succ_nth_stream_of_fr_zero`

English:
theorem exists_succ_nth_stream_of_fr_zero
  statement: {ifp_succ_n : IntFractPair K}
  proof: by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] usin

中文:
定理 exists_succ_nth_stream_of_fr_zero
  结论: {ifp_succ_n : 整数FractPair K}
  证明: by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] usin
-/
theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    exists ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero

/--
theorem `stream_succ` / 定理 `stream_succ`

English:
theorem stream_succ
  given: (h : Int.fract v != 0) (n : Nat)
  proof: by
  induction n with
  | zero =>
    have H : (IntFractPair.of v).fr = Int.fract v := by simp [IntFractPair.of]
    rw [stream_zero]; rw [stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h)]; rw [H]
  | succ n ih =>
    rcases eq_or_ne (IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | 

中文:
定理 stream_succ
  条件: (h : 整数.fract v != 0) (n : 自然数)
  证明: by
  induction n with
  | zero =>
    have H : (IntFractPair.of v).fr = Int.fract v := by simp [IntFractPair.of]
    rw [stream_zero]; rw [stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h)]; rw [H]
  | succ n ih =>
    rcases eq_or_ne (IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | 

Depends on / 依赖: Int.fract, IntFractPair, IntFractPair.of, IntFractPair.stream, Option.ne_none_iff_exists, Or.inl, eq_or_ne, ne_none_iff_exists, ne_of_eq_of_ne, p.fr, stream, stream_succ_of_some, stream_zero, succ_nth_stream_eq_none_iff, succ_nth_stream_eq_none_iff.mpr
-/
theorem stream_succ (h : Int.fract v != 0) (n : Nat) :
    IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻¹ n := by
  induction n with
  | zero =>
    have H : (IntFractPair.of v).fr = Int.fract v := by simp [IntFractPair.of]
    rw [stream_zero]; rw [stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h)]; rw [H]
  | succ n ih =>
    rcases eq_or_ne (IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | hsome
    · rw [hnone] at ih
      rw [succ_nth_stream_eq_none_iff.mpr (Or.inl hnone)]; rw [succ_nth_stream_eq_none_iff.mpr (Or.inl ih)]
    · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hsome
      rw [hp] at ih
      rcases eq_or_ne p.fr 0 with hz | hnz
      · rw [stream_eq_none_of_fr_eq_zero hp hz, stream_eq_none_of_fr_eq_zero ih hz]
      · rw [stream_succ_of_some hp hnz, stream_succ_of_some ih hnz]

end IntFractPair

section Head

/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/


/-- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp]
/--
theorem `IntFractPair.seq1_fst_eq_of` / 定理 `IntFractPair.seq1_fst_eq_of`

English:
theorem IntFractPair.seq1_fst_eq_of
  statement: (IntFractPair.seq1 v).fst = IntFractPair.of v
  proof: rfl

中文:
定理 IntFractPair.seq1_fst_eq_of
  结论: (整数FractPair.seq1 v).fst = 整数FractPair.of v
  证明: rfl
-/
theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v :=
  rfl

/--
theorem `of_h_eq_intFractPair_seq1_fst_b` / 定理 `of_h_eq_intFractPair_seq1_fst_b`

English:
theorem of_h_eq_intFractPair_seq1_fst_b
  statement: (of v).h = (IntFractPair.seq1 v).fst.b
  proof: rfl

中文:
定理 of_h_eq_intFractPair_seq1_fst_b
  结论: (of v).h = (整数FractPair.seq1 v).fst.b
  证明: rfl
-/
theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b :=
  rfl

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
/--
theorem `of_h_eq_floor` / 定理 `of_h_eq_floor`

English:
theorem of_h_eq_floor
  statement: (of v).h = ⌊v⌋
  proof: rfl

中文:
定理 of_h_eq_floor
  结论: (of v).h = ⌊v⌋
  证明: rfl
-/
theorem of_h_eq_floor : (of v).h = ⌊v⌋ :=
  rfl

end Head

section sequence

/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`IntFractPair.stream`, `IntFractPair.seq1`, and `GenContFract.of`) are connected, i.e. how the
values are moved along the structures and how the termination of one sequence implies the
termination of another sequence.
-/


variable {n : Nat}

/--
theorem `IntFractPair.get?_seq1_eq_succ_get?_stream` / 定理 `IntFractPair.get?_seq1_eq_succ_get?_stream`

English:
theorem IntFractPair.get?_seq1_eq_succ_get?_stream
  proof: rfl

中文:
定理 IntFractPair.get?_seq1_eq_succ_get?_stream
  证明: rfl
-/
theorem IntFractPair.get?_seq1_eq_succ_get?_stream :
    (IntFractPair.seq1 v).snd.get? n = (IntFractPair.stream v) (n + 1) :=
  rfl

section Termination



/--
theorem `of_terminatedAt_iff_intFractPair_seq1_terminatedAt` / 定理 `of_terminatedAt_iff_intFractPair_seq1_terminatedAt`

English:
theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt
  proof: Option.map_eq_none_iff

中文:
定理 of_terminatedAt_iff_intFractPair_seq1_terminatedAt
  证明: Option.map_eq_none_iff

Depends on / 依赖: Option.map_eq_none_iff, map_eq_none_iff
-/
theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt :
    (of v).TerminatedAt n ↔ (IntFractPair.seq1 v).snd.TerminatedAt n :=
  Option.map_eq_none_iff

/--
theorem `of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none` / 定理 `of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none`

English:
theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none
  proof: by
  rw [of_terminatedAt_iff_intFractPair_seq1_terminatedAt]; rw [Stream'.Seq.TerminatedAt]; rw [IntFractPair.get?_seq1_eq_succ_get?_stream]

中文:
定理 of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none
  证明: by
  rw [of_terminatedAt_iff_intFractPair_seq1_terminatedAt]; rw [Stream'.Seq.TerminatedAt]; rw [IntFractPair.get?_seq1_eq_succ_get?_stream]

Depends on / 依赖: IntFractPair, IntFractPair.get, Seq.TerminatedAt, Stream, TerminatedAt, _seq1_eq_succ_get, _stream, of_terminatedAt_iff_intFractPair_seq1_terminatedAt
-/
theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [of_terminatedAt_iff_intFractPair_seq1_terminatedAt]; rw [Stream'.Seq.TerminatedAt]; rw [IntFractPair.get?_seq1_eq_succ_get?_stream]

end Termination

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/


set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some` / 定理 `IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some`

English:
theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some
  statement: {gp_n : Pair K}
  proof: by
  obtain ⟨ifp, stream_succ_nth_eq, rfl⟩ :
      exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa using s_nth_eq
  simp_all only [Option.some.injEq, exists_eq_left']

中文:
定理 IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some
  结论: {gp_n : Pair K}
  证明: by
  obtain ⟨ifp, stream_succ_nth_eq, rfl⟩ :
      exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa using s_nth_eq
  simp_all only [Option.some.injEq, exists_eq_left']

Depends on / 依赖: IntFractPair, IntFractPair.seq1, IntFractPair.stream, Option.some.injEq, Pair.mk, exists_eq_left, gp_n, ifp.b, s_nth_eq, stream, stream_succ_nth_eq
-/
theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.get? n = some gp_n) :
    exists ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b := by
  obtain ⟨ifp, stream_succ_nth_eq, rfl⟩ :
      exists ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa using s_nth_eq
  simp_all only [Option.some.injEq, exists_eq_left']

set_option backward.isDefEq.respectTransparency false in
/--
theorem `get?_of_eq_some_of_succ_get?_intFractPair_stream` / 定理 `get?_of_eq_some_of_succ_get?_intFractPair_stream`

English:
theorem get?_of_eq_some_of_succ_get?_intFractPair_stream
  statement: {ifp_succ_n : IntFractPair K}
  proof: by
  unfold of IntFractPair.seq1
  simp [stream_succ_nth_eq]

中文:
定理 get?_of_eq_some_of_succ_get?_intFractPair_stream
  结论: {ifp_succ_n : 整数FractPair K}
  证明: by
  unfold of IntFractPair.seq1
  simp [stream_succ_nth_eq]

Depends on / 依赖: IntFractPair, IntFractPair.seq1, stream_succ_nth_eq
-/
theorem get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.get? n = some ⟨1, ifp_succ_n.b⟩ := by
  unfold of IntFractPair.seq1
  simp [stream_succ_nth_eq]

/--
theorem `get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero` / 定理 `get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero`

English:
theorem get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero
  statement: {ifp_n : IntFractPair K}
  proof: get?_of_eq_some_of_succ_get?_intFractPair_stream
    IntFractPair.stream_succ_of_some stream_nth_eq nth_fr_ne_zero

中文:
定理 get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero
  结论: {ifp_n : 整数FractPair K}
  证明: get?_of_eq_some_of_succ_get?_intFractPair_stream
    IntFractPair.stream_succ_of_some stream_nth_eq nth_fr_ne_zero
-/
theorem get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr != 0) :
    (of v).s.get? n = some ⟨1, (IntFractPair.of ifp_n.fr⁻¹).b⟩ :=
get?_of_eq_some_of_succ_get?_intFractPair_stream
    IntFractPair.stream_succ_of_some stream_nth_eq nth_fr_ne_zero

open Int IntFractPair

/--
theorem `of_s_head_aux` / 定理 `of_s_head_aux`

English:
theorem of_s_head_aux
  given: (v : K)
  statement: (of v).s.get? 0 = (IntFractPair.stream v 1).bind (some ∘ fun p =>
  proof: by
  rw [of]; rw [IntFractPair.seq1]
  simp only [Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ]; rw [Stream'.get]; rw [Option.map.eq_def]
  split <;> simp_all only [Option.bind_some, Option.bind_none, Function.comp_apply]

中文:
定理 of_s_head_aux
  条件: (v : K)
  结论: (of v).s.get? 0 = (整数FractPair.stream v 1).bind (some ∘ fun p =>
  证明: by
  rw [of]; rw [IntFractPair.seq1]
  simp only [Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ]; rw [Stream'.get]; rw [Option.map.eq_def]
  split <;> simp_all only [Option.bind_some, Option.bind_none, Function.comp_apply]
-/
theorem of_s_head_aux (v : K) : (of v).s.get? 0 = (IntFractPair.stream v 1).bind (some ∘ fun p =>
    { a := 1
      b := p.b }) := by
  rw [of]; rw [IntFractPair.seq1]
  simp only [Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ]; rw [Stream'.get]; rw [Option.map.eq_def]
  split <;> simp_all only [Option.bind_some, Option.bind_none, Function.comp_apply]

/--
theorem `of_s_head` / 定理 `of_s_head`

English:
theorem of_s_head
  given: (h : fract v != 0)
  statement: (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩
  proof: by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux]; rw [stream_succ_of_some (stream_zero v) h]; rw [Option.bind]
  rfl

中文:
定理 of_s_head
  条件: (h : fract v != 0)
  结论: (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩
  证明: by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux]; rw [stream_succ_of_some (stream_zero v) h]; rw [Option.bind]
  rfl

Depends on / 依赖: Option.bind, of_s_head_aux, s.get, stream_succ_of_some, stream_zero
-/
theorem of_s_head (h : fract v != 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩ := by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux]; rw [stream_succ_of_some (stream_zero v) h]; rw [Option.bind]
  rfl

variable (K)
variable [IsStrictOrderedRing K]

/--
theorem `of_s_of_int` / 定理 `of_s_of_int`

English:
theorem of_s_of_int
  given: (a : Int)
  statement: (of (a : K)).s = Stream'.Seq.nil
  proof: haveI h : forall n, (of (a : K)).s.get? n = none := by
    intro n
    induction n with
    | zero => rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    | succ n ih => exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm

中文:
定理 of_s_of_int
  条件: (a : 整数)
  结论: (of (a : K)).s = Stream'.Seq.nil
  证明: haveI h : forall n, (of (a : K)).s.get? n = none := by
    intro n
    induction n with
    | zero => rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    | succ n ih => exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm

Depends on / 依赖: Option.bind, Seq.ext, Seq.get, Stream, _nil, of_s_head_aux, s.get, s.prop, stream_succ_of_int
-/
theorem of_s_of_int (a : Int) : (of (a : K)).s = Stream'.Seq.nil :=
  haveI h : forall n, (of (a : K)).s.get? n = none := by
    intro n
    induction n with
    | zero => rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    | succ n ih => exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm

variable {K} (v)

/--
theorem `of_s_succ` / 定理 `of_s_succ`

English:
theorem of_s_succ
  given: (n : Nat)
  statement: (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n
  proof: by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : exists a : Int, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast]; rw [inv_zero]; rw [of_s_of_int]; rw [← cast_zero]; rw [of_s_of_int]; rw [Stream'.Seq.get?_nil]; rw [Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).

中文:
定理 of_s_succ
  条件: (n : 自然数)
  结论: (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n
  证明: by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : exists a : Int, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast]; rw [inv_zero]; rw [of_s_of_int]; rw [← cast_zero]; rw [of_s_of_int]; rw [Stream'.Seq.get?_nil]; rw [Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).

Depends on / 依赖: Seq.get, Stream, _nil, cast_zero, eq_of_sub_eq_zero, eq_or_ne, fract_intCast, inv_zero, of_s_of_int, of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, s.get, stream_succ, termina, terminatedAt_iff_s_none
-/
theorem of_s_succ (n : Nat) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : exists a : Int, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast]; rw [inv_zero]; rw [of_s_of_int]; rw [← cast_zero]; rw [of_s_of_int]; rw [Stream'.Seq.get?_nil]; rw [Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).s.get? n) none with h₁ | h₁
  · rwa [h₁, ← terminatedAt_iff_s_none,
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, stream_succ h, ←
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, terminatedAt_iff_s_none]
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h₁
    obtain ⟨p', hp'₁, _⟩ := exists_succ_get?_stream_of_gcf_of_get?_eq_some hp
    have Hp := get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁
    rw [← stream_succ h] at hp'₁
    rw [Hp]; rw [get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁]

/--
theorem `of_s_tail` / 定理 `of_s_tail`

English:
theorem of_s_tail
  statement: (of v).s.tail = (of (fract v)⁻¹).s
  proof: Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ of_s_succ v n

中文:
定理 of_s_tail
  结论: (of v).s.tail = (of (fract v)⁻¹).s
  证明: Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ of_s_succ v n

Depends on / 依赖: Seq.ext, Seq.get, Stream, _tail, of_s_succ
-/
theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s :=
  Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ of_s_succ v n

variable (K) (n)

/--
theorem `convs'_of_int` / 定理 `convs'_of_int`

English:
theorem convs'_of_int
  given: (a : Int)
  statement: (of (a : K)).convs' n = a
  proof: by
  induction n with
  | zero => simp only [zeroth_conv'_eq_h, of_h_eq_floor, floor_intCast]
  | succ =>
    rw [convs']; rw [of_h_eq_floor]; rw [floor_intCast]; rw [add_eq_left]
    exact convs'Aux_succ_none ((of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _

中文:
定理 convs'_of_int
  条件: (a : 整数)
  结论: (of (a : K)).convs' n = a
  证明: by
  induction n with
  | zero => simp only [zeroth_conv'_eq_h, of_h_eq_floor, floor_intCast]
  | succ =>
    rw [convs']; rw [of_h_eq_floor]; rw [floor_intCast]; rw [add_eq_left]
    exact convs'Aux_succ_none ((of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _
-/
theorem convs'_of_int (a : Int) : (of (a : K)).convs' n = a := by
  induction n with
  | zero => simp only [zeroth_conv'_eq_h, of_h_eq_floor, floor_intCast]
  | succ =>
    rw [convs']; rw [of_h_eq_floor]; rw [floor_intCast]; rw [add_eq_left]
    exact convs'Aux_succ_none ((of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _

variable {K}

/--
theorem `convs'_succ` / 定理 `convs'_succ`

English:
theorem convs'_succ
  proof: by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : exists a : Int, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convs'_of_int]; rw [fract_intCast]; rw [inv_zero]; rw [← cast_zero]; rw [convs'_of_int]; rw [cast_zero]; rw [div_zero]; rw [add_zero]; rw [floor_intCast]
  · rw [convs', of_h

中文:
定理 convs'_succ
  证明: by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : exists a : Int, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convs'_of_int]; rw [fract_intCast]; rw [inv_zero]; rw [← cast_zero]; rw [convs'_of_int]; rw [cast_zero]; rw [div_zero]; rw [add_zero]; rw [floor_intCast]
  · rw [convs', of_h
-/
theorem convs'_succ :
    (of v).convs' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convs' n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : exists a : Int, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convs'_of_int]; rw [fract_intCast]; rw [inv_zero]; rw [← cast_zero]; rw [convs'_of_int]; rw [cast_zero]; rw [div_zero]; rw [add_zero]; rw [floor_intCast]
  · rw [convs', of_h_eq_floor, add_right_inj, convs'Aux_succ_some (of_s_head h)]
    exact congr_arg (1 / ·) (by rw [convs', of_h_eq_floor, add_right_inj, of_s_tail])

end Values

end sequence

end GenContFract
