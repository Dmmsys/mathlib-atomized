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

/-!
### Recurrences and Inversion Lemmas for `IntFractPair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/


/-
**GenContFract.IntFractPair.stream_zero** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract.
IntFractPair`。
形式化陈述：stream_zero (v : K) : IntFractPair.stream v 0 = some (IntFractPair.of v)
参数：v : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Recurrences and Inversion Lemmas for `IntFractPair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the c
omputation of the
stream of integer and fractional parts of a value.
-/
theorem stream_zero (v : K) : IntFractPair.stream v 0 = some (IntFractPair.of v) :=
  rfl

variable {n : ℕ}
/-
**GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `GenContFract.IntFractPair`。
形式化陈述：stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K} (stream_nth_eq : Int
FractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) : IntFractPai
r.stream v (n + 1) = none
参数：stream_nth_eq : IntFractPair.stream v n = some ifp_n；nth_fr_eq_zero : ifp_n.f
r = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none := by
  grind [IntFractPair.stream]

/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
/-
**GenContFract.IntFractPair.succ_nth_stream_eq_none_iff** 是 Mathlib 中的一个定理，位于命名空
间 `GenContFract.IntFractPair`。
形式化陈述：succ_nth_stream_eq_none_iff : IntFractPair.stream v (n + 1) = none ↔ IntFr
actPair.stream v n = none ∨ exists ifp, IntFractPair.stream v n = some ifp ∧ ifp
.fr = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.IntFractPair.stream.eq_2`：∀ {K : Type u_1} [inst : Division
Ring K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] (v : K) (n : ℕ),   GenCo
ntFract.IntFractPair.stream…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p

--- 原说明 ---
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and
 fractional
parts of a value in case of termination.
-/
theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 := by
  rw [IntFractPair.stream]
  cases IntFractPair.stream v n <;> simp [imp_false]

/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
/-
**GenContFract.IntFractPair.succ_nth_stream_eq_some_iff** 是 Mathlib 中的一个定理，位于命名空
间 `GenContFract.IntFractPair`。
形式化陈述：succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.s
tream v (n + 1) = some ifp_succ_n ↔ exists ifp_n : IntFractPair K, IntFractPair.
stream v n = some ifp_n ∧ ifp_n.fr != 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_
n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and
 fractional
parts of a value in case of non-termination.
-/
theorem succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} :
    IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : IntFractPair K,
        IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n := by
  simp [IntFractPair.stream, ite_eq_iff, Option.bind_eq_some_iff]

/-- An easier to use version of one direction of
`GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`. -/
/-
**GenContFract.IntFractPair.stream_succ_of_some** 是 Mathlib 中的一个定理，位于命名空间 `GenCo
ntFract.IntFractPair`。
形式化陈述：stream_succ_of_some {p : IntFractPair K} (h : IntFractPair.stream v n = so
me p) (h' : p.fr != 0) : IntFractPair.stream v (n + 1) = some (IntFractPair.of p
.fr⁻¹)
参数：h : IntFractPair.stream v n = some p；h' : p.fr != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…

--- 原说明 ---
An easier to use version of one direction of
`GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`.
-/
theorem stream_succ_of_some {p : IntFractPair K} (h : IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : IntFractPair.stream v (n + 1) = some (IntFractPair.of p.fr⁻¹) :=
  succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

/-- The stream of `IntFractPair`s of an integer stops after the first term.
-/
/-
**GenContFract.IntFractPair.stream_succ_of_int** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract.IntFractPair`。
形式化陈述：stream_succ_of_int [IsStrictOrderedRing K] (a : Int) (n : Nat) : IntFractP
air.stream (a : K) (n + 1) = none
参数：a : Int；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero`：stream_eq_none_o
f_fr_eq_zero {ifp_n : IntFractPair K} (stream_nth_eq : IntFractPair.stream v n =
 some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0)…
· 使用定理 `GenContFract.IntFractPair.stream_zero`：stream_zero (v : K) : IntFractPai
r.stream v 0 = some (IntFractPair.of v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract_intCast`：fract_intCast (z : Int) : fract (z : R) = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_none_iff`：succ_nth_stream_e
q_none_iff : IntFractPair.stream v (n + 1) = none ↔ IntFractPair.stream v n = no
ne ∨ exists ifp, IntFractPair.stream v n = …

--- 原说明 ---
The stream of `IntFractPair`s of an integer stops after the first term.
-/
theorem stream_succ_of_int [IsStrictOrderedRing K] (a : ℤ) (n : ℕ) :
    IntFractPair.stream (a : K) (n + 1) = none := by
  induction n with
  | zero =>
    refine IntFractPair.stream_eq_none_of_fr_eq_zero (IntFractPair.stream_zero (a : K)) ?_
    simp only [IntFractPair.of, Int.fract_intCast]
  | succ n ih => exact IntFractPair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)
/-
**GenContFract.IntFractPair.exists_succ_nth_stream_of_fr_zero** 是 Mathlib 中的一个定理
，位于命名空间 `GenContFract.IntFractPair`。
形式化陈述：exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K} (stream_su
cc_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) (succ_nth_fr_eq_zer
o : ifp_succ_n.fr = 0) : exists ifp_n : IntFractPair K, IntFractPair.stream v n 
= some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋
参数：stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n；succ_nth
_fr_eq_zero : ifp_succ_n.fr = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_some_iff`：succ_nth_stream_e
q_some_iff {ifp_succ_n : IntFractPair K} : IntFractPair.stream v (n + 1) = some 
ifp_succ_n ↔ exists ifp_n : IntFractPair K,…
-/
theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ := by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, _, rfl⟩
  refine ⟨ifp_n, seq_nth_eq, ?_⟩
  simpa only [IntFractPair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero

/-- A recurrence relation that expresses the `(n+1)`th term of the stream of `IntFractPair`s
of `v` for non-integer `v` in terms of the `n`th term of the stream associated to
the inverse of the fractional part of `v`.
-/
/-
**GenContFract.IntFractPair.stream_succ** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract.
IntFractPair`。
形式化陈述：stream_succ (h : Int.fract v != 0) (n : Nat) : IntFractPair.stream v (n + 
1) = IntFractPair.stream (Int.fract v)⁻¹ n
参数：h : Int.fract v != 0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.IntFractPair.stream_zero`：stream_zero (v : K) : IntFractPai
r.stream v 0 = some (IntFractPair.of v)
· 使用定理 `GenContFract.IntFractPair.stream_succ_of_some`：stream_succ_of_some {p : 
IntFractPair K} (h : IntFractPair.stream v n = some p) (h' : p.fr != 0) : IntFra
ctPair.stream v (n + 1) = some (Int…
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `GenContFract.IntFractPair.succ_nth_stream_eq_none_iff`：succ_nth_stream_e
q_none_iff : IntFractPair.stream v (n + 1) = none ↔ IntFractPair.stream v n = no
ne ∨ exists ifp, IntFractPair.stream v n = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero`：stream_eq_none_o
f_fr_eq_zero {ifp_n : IntFractPair K} (stream_nth_eq : IntFractPair.stream v n =
 some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0)…

--- 原说明 ---
A recurrence relation that expresses the `(n+1)`th term of the stream of `IntFra
ctPair`s
of `v` for non-integer `v` in terms of the `n`th term of the stream associated t
o
the inverse of the fractional part of `v`.
-/
theorem stream_succ (h : Int.fract v ≠ 0) (n : ℕ) :
    IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻¹ n := by
  induction n with
  | zero =>
    have H : (IntFractPair.of v).fr = Int.fract v := by simp [IntFractPair.of]
    rw [stream_zero, stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h), H]
  | succ n ih =>
    rcases eq_or_ne (IntFractPair.stream (Int.fract v)⁻¹ n) none with hnone | hsome
    · rw [hnone] at ih
      rw [succ_nth_stream_eq_none_iff.mpr (Or.inl hnone),
        succ_nth_stream_eq_none_iff.mpr (Or.inl ih)]
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
/-
**GenContFract.IntFractPair.seq1_fst_eq_of** 是 Mathlib 中的一个定理，位于命名空间 `GenContFra
ct.IntFractPair`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 
: FloorRing K] {v : K},   (GenContFract.IntFractPair.seq1 v).1 = GenContFract.In
tFractPair.of v
参数：GenContFract.IntFractPair.seq1 v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head term of the sequence with head of `v` is just the integer part of `v`.
-/
theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v :=
  rfl
/-
**GenContFract.of_h_eq_intFractPair_seq1_fst_b** 是 Mathlib 中的一个定理，位于命名空间 `GenCon
tFract`。
形式化陈述：of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b :=
  rfl

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
/-
**GenContFract.of_h_eq_floor** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_h_eq_floor : (of v).h = ⌊v⌋
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head term of the gcf of `v` is `⌊v⌋`.
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


variable {n : ℕ}

/-
**GenContFract.IntFractPair.get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IntFractPair.get?_seq1_eq_succ_get?_stream :
    (IntFractPair.seq1 v).snd.get? n = (IntFractPair.stream v) (n + 1) :=
  rfl

section Termination

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/


/-
**GenContFract.of_terminatedAt_iff_intFractPair_seq1_terminatedAt** 是 Mathlib 中的
一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_terminatedAt_iff_intFractPair_seq1_terminatedAt : (of v).TerminatedAt n
 ↔ (IntFractPair.seq1 v).snd.TerminatedAt n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_eq_none_iff`：∀ {α : Type u_1} {x : Option α} {α_1 : Type u_2}
 {f : α → α_1}, Option.map f x = none ↔ x = none
· 使用定理 `GenContFract.IntFractPair.stream_isSeq`：stream_isSeq (v : K) : (IntFract
Pair.stream v).IsSeq

--- 原说明 ---
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of 
another sequence.
-/
theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt :
    (of v).TerminatedAt n ↔ (IntFractPair.seq1 v).snd.TerminatedAt n :=
  Option.map_eq_none_iff
/-
**GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none** 是 Ma
thlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none : (of v).Termin
atedAt n ↔ IntFractPair.stream v (n + 1) = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.of_terminatedAt_iff_intFractPair_seq1_terminatedAt`：of_term
inatedAt_iff_intFractPair_seq1_terminatedAt : (of v).TerminatedAt n ↔ (IntFractP
air.seq1 v).snd.TerminatedAt n
· 使用定理 `Stream'.Seq.TerminatedAt.eq_1`：∀ {α : Type u} (s : Stream'.Seq α) (n : ℕ
), s.TerminatedAt n = (s.get? n = none)
· 使用定理 `GenContFract.IntFractPair.get?_seq1_eq_succ_get?_stream`：∀ {K : Type u_1
} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] {v : K
} {n : ℕ},   (GenContFract.IntFractPair.seq1 …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [of_terminatedAt_iff_intFractPair_seq1_terminatedAt, Stream'.Seq.TerminatedAt,
    IntFractPair.get?_seq1_eq_succ_get?_stream]

end Termination

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/


set_option backward.isDefEq.respectTransparency.types false in
/-
**GenContFract.IntFractPair.exists_succ_get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFr
act`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/
theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.get? n = some gp_n) :
    ∃ ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b := by
  obtain ⟨ifp, stream_succ_nth_eq, rfl⟩ :
      ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ Pair.mk 1 (ifp.b : K) = gp_n := by
    unfold of IntFractPair.seq1 at s_nth_eq
    simpa using s_nth_eq
  simp_all only [Option.some.injEq, exists_eq_left']

set_option backward.isDefEq.respectTransparency false in
/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
/-
**GenContFract.get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPai
r K} (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) : (o
f v).s.get? n = some ⟨1, ifp_succ_n.b⟩
参数：stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shows how the entries of the sequence of the computed continued fraction can be 
obtained by the
integer parts of the stream of integer and fractional parts.
-/
theorem get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.get? n = some ⟨1, ifp_succ_n.b⟩ := by
  unfold of IntFractPair.seq1
  simp [stream_succ_nth_eq]

/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
/-
**GenContFract.get** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPai
r K} (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) : (o
f v).s.get? n = some ⟨1, ifp_succ_n.b⟩
参数：stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shows how the entries of the sequence of the computed continued fraction can be 
obtained by the
fractional parts of the stream of integer and fractional parts.
-/
theorem get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
    (of v).s.get? n = some ⟨1, (IntFractPair.of ifp_n.fr⁻¹).b⟩ :=
  get?_of_eq_some_of_succ_get?_intFractPair_stream <|
    IntFractPair.stream_succ_of_some stream_nth_eq nth_fr_ne_zero

open Int IntFractPair
/-
**GenContFract.of_s_head_aux** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_s_head_aux (v : K) : (of v).s.get? 0 = (IntFractPair.stream v 1).bind (
some ∘ fun p => { a
参数：v : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.of.eq_1`：∀ {K : Type u_1} [inst : DivisionRing K] [inst_1 :
 LinearOrder K] [inst_2 : FloorRing K] (v : K),   GenContFract.of v =     match 
GenContFra…
· 使用定理 `GenContFract.IntFractPair.stream_isSeq`：stream_isSeq (v : K) : (IntFract
Pair.stream v).IsSeq
· 使用定理 `GenContFract.IntFractPair.seq1.eq_1`：∀ {K : Type u_1} [inst : DivisionRi
ng K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] (v : K),   GenContFract.In
tFractPair.seq1 v =     (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.get_succ`：get_succ (n : Nat) (s : Stream' α) : get s (succ n) = 
get (tail s) n
· 使用定理 `Stream'.get.eq_1`：∀ {α : Type u} (s : Stream' α) (n : ℕ), s.get n = s n
· 使用定理 `Option.map.eq_def`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (x : Opti
on α),   Option.map f x =     match x with     | some x => some (f x)     | none
 => non…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_s_head_aux (v : K) : (of v).s.get? 0 = (IntFractPair.stream v 1).bind (some ∘ fun p =>
    { a := 1
      b := p.b }) := by
  rw [of, IntFractPair.seq1]
  simp only [Stream'.Seq.map, Stream'.Seq.tail, Stream'.Seq.get?, Stream'.map]
  rw [← Stream'.get_succ, Stream'.get, Option.map.eq_def]
  split <;> simp_all only [Option.bind_some, Option.bind_none, Function.comp_apply]

/-- This gives the first pair of coefficients of the continued fraction of a non-integer `v`.
-/
/-
**GenContFract.of_s_head** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_s_head (h : fract v != 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩
参数：h : fract v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.of_s_head_aux`：of_s_head_aux (v : K) : (of v).s.get? 0 = (I
ntFractPair.stream v 1).bind (some ∘ fun p => { a
· 使用定理 `GenContFract.IntFractPair.stream_succ_of_some`：stream_succ_of_some {p : 
IntFractPair K} (h : IntFractPair.stream v n = some p) (h' : p.fr != 0) : IntFra
ctPair.stream v (n + 1) = some (Int…
· 使用定理 `GenContFract.IntFractPair.stream_zero`：stream_zero (v : K) : IntFractPai
r.stream v 0 = some (IntFractPair.of v)
· 使用定理 `Option.bind.eq_2`：∀ {α : Type u_1} {β : Type u_2} (x : α → Option β) (a 
: α), (some a).bind x = x a

--- 原说明 ---
This gives the first pair of coefficients of the continued fraction of a non-int
eger `v`.
-/
theorem of_s_head (h : fract v ≠ 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩ := by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux, stream_succ_of_some (stream_zero v) h, Option.bind]
  rfl

variable (K)
variable [IsStrictOrderedRing K]

/-- If `a` is an integer, then the coefficient sequence of its continued fraction is empty.
-/
/-
**GenContFract.of_s_of_int** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_s_of_int (a : Int) : (of (a : K)).s = Stream'.Seq.nil
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.ext`：∀ {α : Type u} {s t : Stream'.Seq α}, (∀ (n : ℕ), s.get
? n = t.get? n) → s = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.of_s_head_aux`：of_s_head_aux (v : K) : (of v).s.get? 0 = (I
ntFractPair.stream v 1).bind (some ∘ fun p => { a
· 使用定理 `GenContFract.IntFractPair.stream_succ_of_int`：stream_succ_of_int [IsStri
ctOrderedRing K] (a : Int) (n : Nat) : IntFractPair.stream (a : K) (n + 1) = non
e
· 使用定理 `Option.bind.eq_1`：∀ {α : Type u_1} {β : Type u_2} (x : α → Option β), no
ne.bind x = none
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Stream'.Seq.get?_nil`：∀ {α : Type u} (n : ℕ), Stream'.Seq.nil.get? n = n
one

--- 原说明 ---
If `a` is an integer, then the coefficient sequence of its continued fraction is
 empty.
-/
theorem of_s_of_int (a : ℤ) : (of (a : K)).s = Stream'.Seq.nil :=
  haveI h : ∀ n, (of (a : K)).s.get? n = none := by
    intro n
    induction n with
    | zero => rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    | succ n ih => exact (of (a : K)).s.prop ih
  Stream'.Seq.ext fun n => (h n).trans (Stream'.Seq.get?_nil n).symm

variable {K} (v)

/-- Recurrence for the `GenContFract.of` an element `v` of `K` in terms of that of the inverse of
the fractional part of `v`.
-/
/-
**GenContFract.of_s_succ** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_s_succ (n : Nat) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract_intCast`：fract_intCast (z : Int) : fract (z : R) = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `GenContFract.of_s_of_int`：of_s_of_int (a : Int) : (of (a : K)).s = Strea
m'.Seq.nil
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Stream'.Seq.get?_nil`：∀ {α : Type u} (n : ℕ), Stream'.Seq.nil.get? n = n
one
· 使用定理 `GenContFract.terminatedAt_iff_s_none`：terminatedAt_iff_s_none : g.Termin
atedAt n ↔ g.s.get? n = none
· 使用定理 `GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none`
：of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none : (of v).TerminatedA
t n ↔ IntFractPair.stream v (n + 1) = none
· 使用定理 `GenContFract.IntFractPair.stream_succ`：stream_succ (h : Int.fract v != 0
) (n : Nat) : IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻
¹ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.ne_none_iff_exists'`：∀ {α : Type u_1} {o : Option α}, o ≠ none ↔ 
∃ x, o = some x
· 使用定理 `GenContFract.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some
`：∀ {K : Type u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : Fl
oorRing K] {v : K} {n : ℕ}   {gp_n : GenContFract.Pair K},   (…
· 使用定理 `GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream`：∀ {K : Ty
pe u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : FloorRing K] 
{v : K} {n : ℕ}   {ifp_succ_n : GenContFract.IntFra…

--- 原说明 ---
Recurrence for the `GenContFract.of` an element `v` of `K` in terms of that of t
he inverse of
the fractional part of `v`.
-/
theorem of_s_succ (n : ℕ) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_intCast, inv_zero, of_s_of_int, ← cast_zero, of_s_of_int,
      Stream'.Seq.get?_nil, Stream'.Seq.get?_nil]
  rcases eq_or_ne ((of (fract v)⁻¹).s.get? n) none with h₁ | h₁
  · rwa [h₁, ← terminatedAt_iff_s_none,
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, stream_succ h, ←
      of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none, terminatedAt_iff_s_none]
  · obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h₁
    obtain ⟨p', hp'₁, _⟩ := exists_succ_get?_stream_of_gcf_of_get?_eq_some hp
    have Hp := get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁
    rw [← stream_succ h] at hp'₁
    rw [Hp, get?_of_eq_some_of_succ_get?_intFractPair_stream hp'₁]

/-- This expresses the tail of the coefficient sequence of the `GenContFract.of` an element `v` of
`K` as the coefficient sequence of that of the inverse of the fractional part of `v`.
-/
/-
**GenContFract.of_s_tail** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Stream'.Seq.ext`：∀ {α : Type u} {s t : Stream'.Seq α}, (∀ (n : ℕ), s.get
? n = t.get? n) → s = t
· 使用定理 `GenContFract.of_s_succ`：of_s_succ (n : Nat) : (of v).s.get? (n + 1) = (o
f (fract v)⁻¹).s.get? n
· 使用定理 `Stream'.Seq.get?_tail`：∀ {α : Type u} (s : Stream'.Seq α) (n : ℕ), s.tai
l.get? n = s.get? (n + 1)

--- 原说明 ---
This expresses the tail of the coefficient sequence of the `GenContFract.of` an 
element `v` of
`K` as the coefficient sequence of that of the inverse of the fractional part of
 `v`.
-/
theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s :=
  Stream'.Seq.ext fun n => Stream'.Seq.get?_tail (of v).s n ▸ of_s_succ v n

variable (K) (n)

/-- If `a` is an integer, then the `convs'` of its continued fraction expansion
are all equal to `a`.
-/
/-
**GenContFract.convs'_of_int** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ (K : Type u_1) [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 
: FloorRing K] (n : ℕ) [IsStrictOrderedRing K]   (a : ℤ), (GenContFract.of ↑a).c
onvs' n = ↑a
参数：K : Type u_1；n : ℕ；a : ℤ；GenContFract.of ↑a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.zeroth_conv'_eq_h`：∀ {K : Type u_1} {g : GenContFract K} [i
nst : DivisionRing K], g.convs' 0 = g.h
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `GenContFract.convs'.eq_1`：∀ {K : Type u_2} [inst : DivisionRing K] (g : 
GenContFract K) (n : ℕ), g.convs' n = g.h + GenContFract.convs'Aux g.s n
· 使用定理 `GenContFract.of_h_eq_floor`：of_h_eq_floor : (of v).h = ⌊v⌋
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `GenContFract.convs'Aux_succ_none`：∀ {K : Type u_1} [inst : DivisionRing 
K] {s : Stream'.Seq (GenContFract.Pair K)},   s.head = none → ∀ (n : ℕ), GenCont
Fract.convs'Aux s (n +…
· 使用定理 `Stream'.Seq.get?_nil`：∀ {α : Type u} (n : ℕ), Stream'.Seq.nil.get? n = n
one
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenContFract.of_s_of_int`：of_s_of_int (a : Int) : (of (a : K)).s = Strea
m'.Seq.nil

--- 原说明 ---
If `a` is an integer, then the `convs'` of its continued fraction expansion
are all equal to `a`.
-/
theorem convs'_of_int (a : ℤ) : (of (a : K)).convs' n = a := by
  induction n with
  | zero => simp only [zeroth_conv'_eq_h, of_h_eq_floor, floor_intCast]
  | succ =>
    rw [convs', of_h_eq_floor, floor_intCast, add_eq_left]
    exact convs'Aux_succ_none ((of_s_of_int K a).symm ▸ Stream'.Seq.get?_nil 0) _

variable {K}

/-- The recurrence relation for the `convs'` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
/-
**GenContFract.convs'_succ** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 
: FloorRing K] (v : K) (n : ℕ)   [IsStrictOrderedRing K], (GenContFract.of v).co
nvs' (n + 1) = ↑⌊v⌋ + 1 / (GenContFract.of (Int.fract v)⁻¹).convs' n
参数：v : K；n : ℕ；GenContFract.of v；n + 1；GenContFract.of (Int.fract v)⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenContFract.convs'_of_int`：∀ (K : Type u_1) [inst : DivisionRing K] [in
st_1 : LinearOrder K] [inst_2 : FloorRing K] (n : ℕ) [IsStrictOrderedRing K]   (
a : ℤ), (GenCont…
· 使用定理 `Int.fract_intCast`：fract_intCast (z : Int) : fract (z : R) = 0
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `GenContFract.convs'.eq_1`：∀ {K : Type u_2} [inst : DivisionRing K] (g : 
GenContFract K) (n : ℕ), g.convs' n = g.h + GenContFract.convs'Aux g.s n
· 使用定理 `GenContFract.of_h_eq_floor`：of_h_eq_floor : (of v).h = ⌊v⌋
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `GenContFract.convs'Aux_succ_some`：∀ {K : Type u_1} [inst : DivisionRing 
K] {s : Stream'.Seq (GenContFract.Pair K)} {p : GenContFract.Pair K},   s.head =
 some p → ∀ (n : ℕ), G…
· 使用定理 `GenContFract.of_s_head`：of_s_head (h : fract v != 0) : (of v).s.head = s
ome ⟨1, ⌊(fract v)⁻¹⌋⟩
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `GenContFract.of_s_tail`：of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s

--- 原说明 ---
The recurrence relation for the `convs'` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fract
ional part.
-/
theorem convs'_succ :
    (of v).convs' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convs' n := by
  rcases eq_or_ne (fract v) 0 with h | h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convs'_of_int, fract_intCast, inv_zero, ← cast_zero, convs'_of_int, cast_zero,
      div_zero, add_zero, floor_intCast]
  · rw [convs', of_h_eq_floor, add_right_inj, convs'Aux_succ_some (of_s_head h)]
    exact congr_arg (1 / ·) (by rw [convs', of_h_eq_floor, add_right_inj, of_s_tail])

end Values

end sequence

end GenContFract

