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
`v`. A continued fraction representation of `v` can then be given by `[⌊v⌋; b₀, b₁, b₂,...]`, where
`[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v - ⌊v⌋)`. This
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

/--
Definition of `IntFractPair` / `IntFractPair` 的定义

English:
structure IntFractPair
  parameters: where
  axioms and operations (2):
    - b : Int
    - fr : K

中文:
结构 IntFractPair
  参数: where
  公理与运算 (2 个):
    - b : 整数
    - fr : K
-/
structure IntFractPair where
  b : Int
  fr : K

variable {K}

/-! Interlude: define some expected coercions and instances. -/


namespace IntFractPair

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Repr
  signature: K] : Repr (IntFractPair K)
  body: ⟨fun p _ => "(b : " ++ repr p.b ++ ", fract : " ++ repr p.fr ++ ")"⟩

中文:
实例 [Repr
  签名: K] : Repr (整数FractPair K)
  定义体: ⟨fun p _ => "(b : " ++ repr p.b ++ ", fract : " ++ repr p.fr ++ ")"⟩

Depends on / 依赖: p.fr
-/
instance [Repr K] : Repr (IntFractPair K) :=
  ⟨fun p _ => "(b : " ++ repr p.b ++ ", fract : " ++ repr p.fr ++ ")"⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: [Inhabited K]
  body: ⟨⟨0, default⟩⟩

中文:
实例 inhabited
  签名: [Inhabited K]
  定义体: ⟨⟨0, default⟩⟩
-/
instance inhabited [Inhabited K] : Inhabited (IntFractPair K) :=
  ⟨⟨0, default⟩⟩

/--
Definition of `mapFr` / `mapFr` 的定义

English:
definition mapFr
  signature: {β : Type*} (f : K -> β) (gp : IntFractPair K)
  body: ⟨gp.b, f gp.fr⟩

中文:
定义 mapFr
  签名: {β : 类型} (f : K -> β) (gp : 整数FractPair K)
  定义体: ⟨gp.b, f gp.fr⟩

Depends on / 依赖: gp.b, gp.fr
-/
def mapFr {β : Type*} (f : K -> β) (gp : IntFractPair K) : IntFractPair β :=
  ⟨gp.b, f gp.fr⟩

section coe

/-! Interlude: define some expected coercions. -/


-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe K β]

/-- The coercion between integer-fraction pairs happens componentwise. -/
@[coe]
/--
Definition of `coeFn` / `coeFn` 的定义

English:
definition coeFn
  signature: : IntFractPair K -> IntFractPair β
  body: mapFr (↑)

中文:
定义 coeFn
  签名: : 整数FractPair K -> 整数FractPair β
  定义体: mapFr (↑)
-/
def coeFn : IntFractPair K -> IntFractPair β := mapFr (↑)

/--
Instance `coe` / 实例 `coe`

English:
instance coe
  signature: : Coe (IntFractPair K) (IntFractPair β) where
  body: coeFn

@[simp, norm_cast]

中文:
实例 coe
  签名: : Coe (整数FractPair K) (整数FractPair β) where
  定义体: coeFn

@[simp, norm_cast]
-/
instance coe : Coe (IntFractPair K) (IntFractPair β) where
  coe := coeFn

@[simp, norm_cast]
/--
theorem `coe_to_intFractPair` / 定理 `coe_to_intFractPair`

English:
theorem coe_to_intFractPair
  given: {b : Int} {fr : K}
  proof: rfl

中文:
定理 coe_to_intFractPair
  条件: {b : 整数} {fr : K}
  证明: rfl
-/
theorem coe_to_intFractPair {b : Int} {fr : K} :
    (↑(IntFractPair.mk b fr) : IntFractPair β) = IntFractPair.mk b (↑fr : β) :=
  rfl

end coe

-- Fix a discrete linear ordered division ring with `floor` function.
variable [DivisionRing K] [LinearOrder K] [FloorRing K]

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (v : K)
  body: ⟨⌊v⌋, Int.fract v⟩

中文:
定义 of
  签名: (v : K)
  定义体: ⟨⌊v⌋, Int.fract v⟩
-/
protected def of (v : K) : IntFractPair K :=
  ⟨⌊v⌋, Int.fract v⟩

/--
Definition of `stream` / `stream` 的定义

English:
definition stream
  signature: (v : K)

中文:
定义 stream
  签名: (v : K)
-/
protected def stream (v : K) : Stream' Option (IntFractPair K)
  | 0 => some (IntFractPair.of v)
  | n + 1 =>
    (IntFractPair.stream v n).bind fun ap_n =>
      if ap_n.fr = 0 then none else some (IntFractPair.of ap_n.fr⁻¹)

/--
theorem `stream_isSeq` / 定理 `stream_isSeq`

English:
theorem stream_isSeq
  given: (v : K)
  statement: (IntFractPair.stream v).IsSeq
  proof: by
  intro _ hyp
  simp [IntFractPair.stream, hyp]

中文:
定理 stream_isSeq
  条件: (v : K)
  结论: (整数FractPair.stream v).IsSeq
  证明: by
  intro _ hyp
  simp [IntFractPair.stream, hyp]

Depends on / 依赖: IntFractPair, IntFractPair.stream, stream
-/
theorem stream_isSeq (v : K) : (IntFractPair.stream v).IsSeq := by
  intro _ hyp
  simp [IntFractPair.stream, hyp]

/--
Definition of `seq1` / `seq1` 的定义

English:
definition seq1
  signature: (v : K)
  body: ⟨IntFractPair.of v, -- the head
    -- take the tail of `IntFractPair.stream` since the first element is already in the head
    Stream'.Seq.tail
      -- create a sequence from `IntFractPair.stream`
      ⟨IntFractPair.stream v, -- the underlying stream
        stream_isSeq v⟩⟩ -- the proof that th

中文:
定义 seq1
  签名: (v : K)
  定义体: ⟨IntFractPair.of v, -- the head
    -- take the tail of `IntFractPair.stream` since the first element is already in the head
    Stream'.Seq.tail
      -- create a sequence from `IntFractPair.stream`
      ⟨IntFractPair.stream v, -- the underlying stream
        stream_isSeq v⟩⟩ -- the proof that th
-/
protected def seq1 (v : K) : Stream'.Seq1 IntFractPair K :=
  ⟨IntFractPair.of v, -- the head
    -- take the tail of `IntFractPair.stream` since the first element is already in the head
    Stream'.Seq.tail
      -- create a sequence from `IntFractPair.stream`
      ⟨IntFractPair.stream v, -- the underlying stream
        stream_isSeq v⟩⟩ -- the proof that the stream is a sequence

end IntFractPair

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: [DivisionRing K] [LinearOrder K] [FloorRing K] (v : K)
  body: let ⟨h, s⟩ := IntFractPair.seq1 v -- get the sequence of integer and fractional parts.
  ⟨h.b, -- the head is just the first integer part
    s.map fun p => ⟨1, p.b⟩⟩ -- the sequence consists of the remaining integer parts as the partial
                            -- denominators; all partial numer

中文:
定义 of
  签名: [DivisionRing K] [LinearOrder K] [FloorRing K] (v : K)
  定义体: let ⟨h, s⟩ := IntFractPair.seq1 v -- get the sequence of integer and fractional parts.
  ⟨h.b, -- the head is just the first integer part
    s.map fun p => ⟨1, p.b⟩⟩ -- the sequence consists of the remaining integer parts as the partial
                            -- denominators; all partial numer
-/
protected def of [DivisionRing K] [LinearOrder K] [FloorRing K] (v : K) : GenContFract K :=
  let ⟨h, s⟩ := IntFractPair.seq1 v -- get the sequence of integer and fractional parts.
  ⟨h.b, -- the head is just the first integer part
    s.map fun p => ⟨1, p.b⟩⟩ -- the sequence consists of the remaining integer parts as the partial
                            -- denominators; all partial numerators are simply 1

end GenContFract
