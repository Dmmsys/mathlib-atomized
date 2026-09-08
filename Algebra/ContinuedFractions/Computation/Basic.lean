/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Basic
public import Mathlib.Algebra.Order.Floor.Defs

/-!
# Computable Continued Fractions

## Summary

We formalise the standard computation of (regular) continued fractions for linear ordered floor
fields. The algorithm is rather simple. Here is an outline of the procedure adapted from Wikipedia:

Take a value `v`. We call `⌊v⌋` the *integer part* of `v` and `v - ⌊v⌋` the *fractional part* of
`v`.  A continued fraction representation of `v` can then be given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v - ⌊v⌋)`.  This
process stops when the fractional part hits 0.

In other words: to calculate a continued fraction representation of a number `v`, write down the
integer part (i.e. the floor) of `v`. Subtract this integer part from `v`. If the difference is 0,
stop; otherwise find the reciprocal of the difference and repeat. The procedure will terminate if
and only if `v` is rational.

For an example, refer to `IntFractPair.stream`.

## Main definitions

- `GenContFract.IntFractPair.stream`: computes the stream of integer and fractional parts of a given
  value as described in the summary.
- `GenContFract.of`: computes the generalised continued fraction of a value `v`.
  In fact, it computes a regular continued fraction that terminates if and only if `v` is rational.

## Implementation Notes

There is an intermediate definition `GenContFract.IntFractPair.seq1` between
`GenContFract.IntFractPair.stream` and `GenContFract.of` to wire up things. Users should not
(need to) directly interact with it.

The computation of the integer and fractional pairs of a value can elegantly be
captured by a recursive computation of a stream of option pairs. This is done in
`IntFractPair.stream`. However, the type then does not guarantee the first pair to always be
`some` value, as expected by a continued fraction.

To separate concerns, we first compute a single head term that always exists in
`GenContFract.IntFractPair.seq1` followed by the remaining stream of option pairs. This sequence
with a head term (`seq1`) is then transformed to a generalized continued fraction in
`GenContFract.of` by extracting the wanted integer parts of the head term and the stream.

## References

- https://en.wikipedia.org/wiki/Continued_fraction

## Tags

numerics, number theory, approximations, fractions
-/

@[expose] public section

assert_not_exists Finset

namespace GenContFract

-- Fix a carrier `K`.
variable (K : Type*)

/-- We collect an integer part `b = ⌊v⌋` and fractional part `fr = v - ⌊v⌋` of a value `v` in a pair
`⟨b, fr⟩`.
-/
/-
**GenContFract.IntFractPair** 是 Mathlib 中的一个归纳类型，位于命名空间 `GenContFract`。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We collect an integer part `b = ⌊v⌋` and fractional part `fr = v - ⌊v⌋` of a val
ue `v` in a pair
`⟨b, fr⟩`.
-/
structure IntFractPair where
  b : ℤ
  fr : K

variable {K}

/-! Interlude: define some expected coercions and instances. -/


namespace IntFractPair

/-- Make an `IntFractPair` printable. -/
/-
**GenContFract.IntFractPair.** 是 Mathlib 中的一个实例，位于命名空间 `GenContFract.IntFractPai
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make an `IntFractPair` printable.
-/
instance [Repr K] : Repr (IntFractPair K) :=
  ⟨fun p _ => "(b : " ++ repr p.b ++ ", fract : " ++ repr p.fr ++ ")"⟩
/-
**GenContFract.IntFractPair.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `GenContFract.In
tFractPair`。
形式化陈述：inhabited [Inhabited K] : Inhabited (IntFractPair K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited [Inhabited K] : Inhabited (IntFractPair K) :=
  ⟨⟨0, default⟩⟩

/-- Maps a function `f` on the fractional components of a given pair.
-/
/-
**GenContFract.IntFractPair.mapFr** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract.IntFra
ctPair`。
形式化陈述：mapFr {β : Type*} (f : K -> β) (gp : IntFractPair K) : IntFractPair β
参数：f : K -> β；gp : IntFractPair K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps a function `f` on the fractional components of a given pair.
-/
def mapFr {β : Type*} (f : K → β) (gp : IntFractPair K) : IntFractPair β :=
  ⟨gp.b, f gp.fr⟩

section coe

/-! Interlude: define some expected coercions. -/


-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe K β]

/-- The coercion between integer-fraction pairs happens componentwise. -/
@[coe]
/-
**GenContFract.IntFractPair.coeFn** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract.IntFra
ctPair`。
形式化陈述：coeFn : IntFractPair K -> IntFractPair β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion between integer-fraction pairs happens componentwise.
-/
def coeFn : IntFractPair K → IntFractPair β := mapFr (↑)

/-- Coerce a pair by coercing the fractional component. -/
/-
**GenContFract.IntFractPair.coe** 是 Mathlib 中的一个实例，位于命名空间 `GenContFract.IntFract
Pair`。
形式化陈述：coe : Coe (IntFractPair K) (IntFractPair β) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coerce a pair by coercing the fractional component.
-/
instance coe : Coe (IntFractPair K) (IntFractPair β) where
  coe := coeFn

@[simp, norm_cast]
/-
**GenContFract.IntFractPair.coe_to_intFractPair** 是 Mathlib 中的一个定理，位于命名空间 `GenCo
ntFract.IntFractPair`。
形式化陈述：coe_to_intFractPair {b : Int} {fr : K} : (↑(IntFractPair.mk b fr) : IntFra
ctPair β) = IntFractPair.mk b (↑fr : β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_to_intFractPair {b : ℤ} {fr : K} :
    (↑(IntFractPair.mk b fr) : IntFractPair β) = IntFractPair.mk b (↑fr : β) :=
  rfl

end coe

-- Fix a discrete linear ordered division ring with `floor` function.
variable [DivisionRing K] [LinearOrder K] [FloorRing K]

/-- Creates the integer and fractional part of a value `v`, i.e. `⟨⌊v⌋, v - ⌊v⌋⟩`. -/
/-
**GenContFract.IntFractPair.of** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract.IntFractP
air`。
形式化陈述：{K : Type u_1} → [inst : DivisionRing K] → [inst_1 : LinearOrder K] → [Flo
orRing K] → K → GenContFract.IntFractPair K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creates the integer and fractional part of a value `v`, i.e. `⟨⌊v⌋, v - ⌊v⌋⟩`.
-/
protected def of (v : K) : IntFractPair K :=
  ⟨⌊v⌋, Int.fract v⟩

/-- Creates the stream of integer and fractional parts of a value `v` needed to obtain the continued
fraction representation of `v` in `GenContFract.of`. More precisely, given a value `v : K`, it
recursively computes a stream of option `ℤ × K` pairs as follows:
- `stream v 0 = some ⟨⌊v⌋, v - ⌊v⌋⟩`
- `stream v (n + 1) = some ⟨⌊frₙ⁻¹⌋, frₙ⁻¹ - ⌊frₙ⁻¹⌋⟩`,
  if `stream v n = some ⟨_, frₙ⟩` and `frₙ ≠ 0`
- `stream v (n + 1) = none`, otherwise

For example, let `(v : ℚ) := 3.4`. The process goes as follows:
- `stream v 0 = some ⟨⌊v⌋, v - ⌊v⌋⟩ = some ⟨3, 0.4⟩`
- `stream v 1 = some ⟨⌊0.4⁻¹⌋, 0.4⁻¹ - ⌊0.4⁻¹⌋⟩ = some ⟨⌊2.5⌋, 2.5 - ⌊2.5⌋⟩ = some ⟨2, 0.5⟩`
- `stream v 2 = some ⟨⌊0.5⁻¹⌋, 0.5⁻¹ - ⌊0.5⁻¹⌋⟩ = some ⟨⌊2⌋, 2 - ⌊2⌋⟩ = some ⟨2, 0⟩`
- `stream v n = none`, for `n ≥ 3`
-/
/-
**GenContFract.IntFractPair.stream** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract.IntFr
actPair`。
形式化陈述：{K : Type u_1} →   [inst : DivisionRing K] →     [inst_1 : LinearOrder K] 
→ [FloorRing K] → K → Stream' (Option (GenContFract.IntFractPair K))
参数：Option (GenContFract.IntFractPair K)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Creates the stream of integer and fractional parts of a value `v` needed to obta
in the continued
fraction representation of `v` in `GenContFract.of`. More precisely, given a val
ue `v : K`, it
recursively computes a stream of option `ℤ × K` pairs as follows:
- `stream v 0 = some ⟨⌊v⌋, v - ⌊v⌋⟩`
- `stream v (n + 1) = some ⟨⌊frₙ⁻¹⌋, frₙ⁻¹ - ⌊frₙ⁻¹⌋⟩`,
  if `stream v n = some ⟨_, frₙ⟩` and `frₙ ≠ 0`
- `stream v (n + 1) = none`, otherwise

For example, let `(v : ℚ) := 3.4`. The process goes as follows:
- `stream v 0 = some ⟨⌊v⌋, v - ⌊v⌋⟩ = some ⟨3, 0.4⟩`
- `stream v 1 = some ⟨⌊0.4⁻¹⌋, 0.4⁻¹ - ⌊0.4⁻¹⌋⟩ = some ⟨⌊2.5⌋, 2.5 - ⌊2.5⌋⟩ = so
me ⟨2, 0.5⟩`
- `stream v 2 = some ⟨⌊0.5⁻¹⌋, 0.5⁻¹ - ⌊0.5⁻¹⌋⟩ = some ⟨⌊2⌋, 2 - ⌊2⌋⟩ = some ⟨2,
 0⟩`
- `stream v n = none`, for `n ≥ 3`
-/
protected def stream (v : K) : Stream' <| Option (IntFractPair K)
  | 0 => some (IntFractPair.of v)
  | n + 1 =>
    (IntFractPair.stream v n).bind fun ap_n =>
      if ap_n.fr = 0 then none else some (IntFractPair.of ap_n.fr⁻¹)

/-- Shows that `IntFractPair.stream` has the sequence property, that is once we return `none` at
position `n`, we also return `none` at `n + 1`.
-/
/-
**GenContFract.IntFractPair.stream_isSeq** 是 Mathlib 中的一个定理，位于命名空间 `GenContFract
.IntFractPair`。
形式化陈述：stream_isSeq (v : K) : (IntFractPair.stream v).IsSeq
参数：v : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Shows that `IntFractPair.stream` has the sequence property, that is once we retu
rn `none` at
position `n`, we also return `none` at `n + 1`.
-/
theorem stream_isSeq (v : K) : (IntFractPair.stream v).IsSeq := by
  intro _ hyp
  simp [IntFractPair.stream, hyp]

/--
Uses `IntFractPair.stream` to create a sequence with head (i.e. `seq1`) of integer and fractional
parts of a value `v`. The first value of `IntFractPair.stream` is never `none`, so we can safely
extract it and put the tail of the stream in the sequence part.

This is just an intermediate representation and users should not (need to) directly interact with
it. The setup of rewriting/simplification lemmas that make the definitions easy to use is done in
`Mathlib/Algebra/ContinuedFractions/Computation/Translations.lean`.
-/
/-
**GenContFract.IntFractPair.seq1** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract.IntFrac
tPair`。
形式化陈述：{K : Type u_1} →   [inst : DivisionRing K] → [inst_1 : LinearOrder K] → [F
loorRing K] → K → Stream'.Seq1 (GenContFract.IntFractPair K)
参数：GenContFract.IntFractPair K。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GenContFract.IntFractPair.stream_isSeq`：stream_isSeq (v : K) : (IntFract
Pair.stream v).IsSeq

--- 原说明 ---
Uses `IntFractPair.stream` to create a sequence with head (i.e. `seq1`) of integ
er and fractional
parts of a value `v`. The first value of `IntFractPair.stream` is never `none`, 
so we can safely
extract it and put the tail of the stream in the sequence part.

This is just an intermediate representation and users should not (need to) direc
tly interact with
it. The setup of rewriting/simplification lemmas that make the definitions easy 
to use is done in
`Mathlib/Algebra/ContinuedFractions/Computation/Translations.lean`.
-/
protected def seq1 (v : K) : Stream'.Seq1 <| IntFractPair K :=
  ⟨IntFractPair.of v, -- the head
    -- take the tail of `IntFractPair.stream` since the first element is already in the head
    Stream'.Seq.tail
      -- create a sequence from `IntFractPair.stream`
      ⟨IntFractPair.stream v, -- the underlying stream
        stream_isSeq v⟩⟩ -- the proof that the stream is a sequence

end IntFractPair

/-- Returns the `GenContFract` of a value. In fact, the returned gcf is also a `ContFract` that
terminates if and only if `v` is rational
(see `Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean`).

The continued fraction representation of `v` is given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v - ⌊v⌋)`. This
process stops when the fractional part `v - ⌊v⌋` hits 0 at some step.

The implementation uses `IntFractPair.stream` to obtain the partial denominators of the continued
fraction. Refer to said function for more details about the computation process.
-/
/-
**GenContFract.of** 是 Mathlib 中的一个定义，位于命名空间 `GenContFract`。
形式化陈述：{K : Type u_1} → [inst : DivisionRing K] → [inst_1 : LinearOrder K] → [Flo
orRing K] → K → GenContFract K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the `GenContFract` of a value. In fact, the returned gcf is also a `Cont
Fract` that
terminates if and only if `v` is rational
(see `Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean`).

The continued fraction representation of `v` is given by `[⌊v⌋; b₀, b₁, b₂,...]`
, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / 
(v - ⌊v⌋)`. This
process stops when the fractional part `v - ⌊v⌋` hits 0 at some step.

The implementation uses `IntFractPair.stream` to obtain the partial denominators
 of the continued
fraction. Refer to said function for more details about the computation process.
-/
protected def of [DivisionRing K] [LinearOrder K] [FloorRing K] (v : K) : GenContFract K :=
  let ⟨h, s⟩ := IntFractPair.seq1 v -- get the sequence of integer and fractional parts.
  ⟨h.b, -- the head is just the first integer part
    s.map fun p => ⟨1, p.b⟩⟩ -- the sequence consists of the remaining integer parts as the partial
                            -- denominators; all partial numerators are simply 1

end GenContFract

