/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Data.Seq.Defs
public import Mathlib.Algebra.Field.Defs

/-!
# Basic Definitions/Theorems for Continued Fractions

## Summary

We define generalised, simple, and regular continued fractions and functions to evaluate their
convergents. We follow the naming conventions from Wikipedia and [wall2018analytic], Chapter 1.

## Main definitions

1. Generalised continued fractions (gcfs)
2. Simple continued fractions (scfs)
3. (Regular) continued fractions ((r)cfs)
4. Computation of convergents using the recurrence relation in `convs`.
5. Computation of convergents by directly evaluating the fraction described by the gcf in `convs'`.

## Implementation notes

1. The most commonly used kind of continued fractions in the literature are regular continued
   fractions. We hence just call them `ContFract` in the library.
2. We use sequences from `Data.Seq` to encode potentially infinite sequences.

## References

- <https://en.wikipedia.org/wiki/Generalized_continued_fraction>
- [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

## Tags

numerics, number theory, approximations, fractions
-/

@[expose] public section

-- Fix a carrier `α`.
variable (α : Type*)

/-!### Definitions -/

/--
Definition of `GenContFract.Pair` / `GenContFract.Pair` 的定义

English:
structure GenContFract.Pair
  parameters: where
  axioms and operations (2):
    - a : α
    - b : α

中文:
结构 GenContFract.对
  参数: where
  公理与运算 (2 个):
    - a : α
    - b : α
-/
structure GenContFract.Pair where
  /-- Partial numerator -/
  a : α
  /-- Partial denominator -/
  b : α
  deriving Inhabited

open GenContFract

/-! Interlude: define some expected coercions and instances. -/

namespace GenContFract.Pair

variable {α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Repr
  signature: α] : Repr (Pair α)
  body: ⟨fun p _ => "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

中文:
实例 [Repr
  签名: α] : Repr (对 α)
  定义体: ⟨fun p _ => "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩
-/
instance [Repr α] : Repr (Pair α) :=
  ⟨fun p _ => "(a : " ++ repr p.a ++ ", b : " ++ repr p.b ++ ")"⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β : Type*} (f : α -> β) (gp : Pair α)
  body: ⟨f gp.a, f gp.b⟩

中文:
定义 map
  签名: {β : 类型} (f : α -> β) (gp : 对 α)
  定义体: ⟨f gp.a, f gp.b⟩

Depends on / 依赖: gp.a, gp.b, ringChar
-/
def map {β : Type*} (f : α -> β) (gp : Pair α) : Pair β :=
  ⟨f gp.a, f gp.b⟩

section coe

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

/-- The coercion between numerator-denominator pairs happens componentwise. -/
@[coe]
/--
Definition of `coeFn` / `coeFn` 的定义

English:
definition coeFn
  signature: : Pair α -> Pair β
  body: map (↑)

中文:
定义 coeFn
  签名: : 对 α -> 对 β
  定义体: map (↑)
-/
def coeFn : Pair α -> Pair β := map (↑)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Pair α) (Pair β)
  body: ⟨coeFn⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Coe (对 α) (对 β)
  定义体: ⟨coeFn⟩

@[simp, norm_cast]
-/
instance : Coe (Pair α) (Pair β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
/--
theorem `coe_toPair` / 定理 `coe_toPair`

English:
theorem coe_toPair
  given: {a b : α}
  statement: (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β)
  proof: rfl

中文:
定理 coe_toPair
  条件: {a b : α}
  结论: (↑(对.mk a b) : 对 β) = 对.mk (a : β) (b : β)
  证明: rfl
-/
theorem coe_toPair {a b : α} : (↑(Pair.mk a b) : Pair β) = Pair.mk (a : β) (b : β) := rfl

end coe

end GenContFract.Pair

/-- A *generalised continued fraction* (gcf) is a potentially infinite expression of the form
$$
  h + \dfrac{a_0}
            {b_0 + \dfrac{a_1}
                         {b_1 + \dfrac{a_2}
                                      {b_2 + \dfrac{a_3}
                                                   {b_3 + \dots}}}}
$$
where `h` is called the *head term* or *integer part*, the `aᵢ` are called the
*partial numerators* and the `bᵢ` the *partial denominators* of the gcf.
We store the sequence of partial numerators and denominators in a sequence of `GenContFract.Pair`s
`s`.
For convenience, one often writes `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`.
-/
@[ext, wikidata Q4115724]
/--
Definition of `GenContFract` / `GenContFract` 的定义

English:
structure GenContFract
  parameters: where
  axioms and operations (1):
    - h : α

中文:
结构 GenContFract
  参数: where
  公理与运算 (1 个):
    - h : α
-/
structure GenContFract where
  /-- Head term -/
  h : α
  /-- Sequence of partial numerator and denominator pairs. -/
s : Stream'.Seq Pair α

variable {α}

namespace GenContFract

/--
Definition of `ofInteger` / `ofInteger` 的定义

English:
definition ofInteger
  signature: (a : α)
  body: ⟨a, Stream'.Seq.nil⟩

中文:
定义 of整数eger
  签名: (a : α)
  定义体: ⟨a, Stream'.Seq.nil⟩

Depends on / 依赖: Seq.nil, Stream
-/
def ofInteger (a : α) : GenContFract α :=
  ⟨a, Stream'.Seq.nil⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (GenContFract α)
  body: ⟨ofInteger default⟩

中文:
实例 [可居
  签名: α] : 可居 (GenContFract α)
  定义体: ⟨ofInteger default⟩

Depends on / 依赖: ofInteger
-/
instance [Inhabited α] : Inhabited (GenContFract α) :=
  ⟨ofInteger default⟩

/--
Definition of `partNums` / `partNums` 的定义

English:
definition partNums
  signature: (g : GenContFract α)
  body: g.s.map Pair.a

中文:
定义 partNums
  签名: (g : GenContFract α)
  定义体: g.s.map Pair.a

Depends on / 依赖: Pair.a, g.s.map
-/
def partNums (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.a

/--
Definition of `partDens` / `partDens` 的定义

English:
definition partDens
  signature: (g : GenContFract α)
  body: g.s.map Pair.b

中文:
定义 partDens
  签名: (g : GenContFract α)
  定义体: g.s.map Pair.b

Depends on / 依赖: Pair.b, g.s.map
-/
def partDens (g : GenContFract α) : Stream'.Seq α :=
  g.s.map Pair.b

/--
Definition of `TerminatedAt` / `TerminatedAt` 的定义

English:
definition TerminatedAt
  signature: (g : GenContFract α) (n : Nat)
  body: g.s.TerminatedAt n
deriving Decidable

中文:
定义 TerminatedAt
  签名: (g : GenContFract α) (n : 自然数)
  定义体: g.s.TerminatedAt n
deriving Decidable

Depends on / 依赖: TerminatedAt, g.s.TerminatedAt
-/
def TerminatedAt (g : GenContFract α) (n : Nat) : Prop :=
  g.s.TerminatedAt n
deriving Decidable

/--
Definition of `Terminates` / `Terminates` 的定义

English:
definition Terminates
  signature: (g : GenContFract α)
  body: g.s.Terminates

中文:
定义 Terminates
  签名: (g : GenContFract α)
  定义体: g.s.Terminates

Depends on / 依赖: Terminates, g.s.Terminates
-/
def Terminates (g : GenContFract α) : Prop :=
  g.s.Terminates

section coe

/-! Interlude: define some expected coercions. -/

-- Fix another type `β` which we will convert to.
variable {β : Type*} [Coe α β]

/-- The coercion between `GenContFract` happens on the head term
and all numerator-denominator pairs componentwise. -/
@[coe]
/--
Definition of `coeFn` / `coeFn` 的定义

English:
definition coeFn
  signature: : GenContFract α -> GenContFract β
  body: fun g => ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

中文:
定义 coeFn
  签名: : GenContFract α -> GenContFract β
  定义体: fun g => ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

Depends on / 依赖: Stream, g.s.map
-/
def coeFn : GenContFract α -> GenContFract β :=
  fun g => ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (GenContFract α) (GenContFract β)
  body: ⟨coeFn⟩

@[simp, norm_cast]

中文:
实例 :
  签名: Coe (GenContFract α) (GenContFract β)
  定义体: ⟨coeFn⟩

@[simp, norm_cast]
-/
instance : Coe (GenContFract α) (GenContFract β) :=
  ⟨coeFn⟩

@[simp, norm_cast]
/--
theorem `coe_toGenContFract` / 定理 `coe_toGenContFract`

English:
theorem coe_toGenContFract
  given: {g : GenContFract α}
  proof: rfl

中文:
定理 coe_toGenContFract
  条件: {g : GenContFract α}
  证明: rfl
-/
theorem coe_toGenContFract {g : GenContFract α} :
    (g : GenContFract β) =
      ⟨(g.h : β), (g.s.map (↑) : Stream'.Seq <| Pair β)⟩ := rfl

end coe

end GenContFract

/--
Definition of `GenContFract.IsSimpContFract` / `GenContFract.IsSimpContFract` 的定义

English:
definition GenContFract.IsSimpContFract
  signature: (g : GenContFract α)
  body: forall (n : Nat) (aₙ : α), g.partNums.get? n = some aₙ -> aₙ = 1

中文:
定义 GenContFract.IsSimpContFract
  签名: (g : GenContFract α)
  定义体: forall (n : Nat) (aₙ : α), g.partNums.get? n = some aₙ -> aₙ = 1

Depends on / 依赖: g.partNums.get, partNums
-/
def GenContFract.IsSimpContFract (g : GenContFract α)
    [One α] : Prop :=
  forall (n : Nat) (aₙ : α), g.partNums.get? n = some aₙ -> aₙ = 1

variable (α) in
/--
Definition of `SimpContFract` / `SimpContFract` 的定义

English:
definition SimpContFract
  signature: [One α]
  body: { g : GenContFract α // g.IsSimpContFract }

中文:
定义 SimpContFract
  签名: [幺 α]
  定义体: { g : GenContFract α // g.IsSimpContFract }

Depends on / 依赖: GenContFract, IsSimpContFract, g.IsSimpContFract
-/
def SimpContFract [One α] :=
  { g : GenContFract α // g.IsSimpContFract }

-- Interlude: define some expected coercions.
namespace SimpContFract

variable [One α]

/--
Definition of `ofInteger` / `ofInteger` 的定义

English:
definition ofInteger
  signature: (a : α)
  body: ⟨GenContFract.ofInteger a, fun n aₙ h => by cases h⟩

中文:
定义 of整数eger
  签名: (a : α)
  定义体: ⟨GenContFract.ofInteger a, fun n aₙ h => by cases h⟩

Depends on / 依赖: GenContFract, GenContFract.ofInteger, ofInteger
-/
def ofInteger (a : α) : SimpContFract α :=
  ⟨GenContFract.ofInteger a, fun n aₙ h => by cases h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SimpContFract α)
  body: ⟨ofInteger 1⟩

中文:
实例 :
  签名: 可居 (SimpContFract α)
  定义体: ⟨ofInteger 1⟩

Depends on / 依赖: ofInteger
-/
instance : Inhabited (SimpContFract α) :=
  ⟨ofInteger 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (SimpContFract α) (GenContFract α)
  body: ⟨Subtype.val⟩

中文:
实例 :
  签名: Coe (SimpContFract α) (GenContFract α)
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance : Coe (SimpContFract α) (GenContFract α) :=
  ⟨Subtype.val⟩

end SimpContFract

/--
Definition of `SimpContFract.IsContFract` / `SimpContFract.IsContFract` 的定义

English:
definition SimpContFract.IsContFract
  signature: [One α] [Zero α] [LT α]
  body: forall (n : Nat) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ -> 0 < bₙ

中文:
定义 SimpContFract.IsContFract
  签名: [幺 α] [零 α] [LT α]
  定义体: forall (n : Nat) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ -> 0 < bₙ

Depends on / 依赖: GenContFract, partDens, partDens.get
-/
def SimpContFract.IsContFract [One α] [Zero α] [LT α]
    (s : SimpContFract α) : Prop :=
  forall (n : Nat) (bₙ : α),
    (↑s : GenContFract α).partDens.get? n = some bₙ -> 0 < bₙ

variable (α) in
/--
Definition of `ContFract` / `ContFract` 的定义

English:
definition ContFract
  signature: [One α] [Zero α] [LT α]
  body: { s : SimpContFract α // s.IsContFract }

中文:
定义 ContFract
  签名: [幺 α] [零 α] [LT α]
  定义体: { s : SimpContFract α // s.IsContFract }

Depends on / 依赖: IsContFract, SimpContFract, s.IsContFract
-/
def ContFract [One α] [Zero α] [LT α] :=
  { s : SimpContFract α // s.IsContFract }

/-! Interlude: define some expected coercions. -/

namespace ContFract

variable [One α] [Zero α] [LT α]

/--
Definition of `ofInteger` / `ofInteger` 的定义

English:
definition ofInteger
  signature: (a : α)
  body: ⟨SimpContFract.ofInteger a, fun n bₙ h => by cases h⟩

中文:
定义 of整数eger
  签名: (a : α)
  定义体: ⟨SimpContFract.ofInteger a, fun n bₙ h => by cases h⟩

Depends on / 依赖: SimpContFract, SimpContFract.ofInteger, ofInteger
-/
def ofInteger (a : α) : ContFract α :=
  ⟨SimpContFract.ofInteger a, fun n bₙ h => by cases h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ContFract α)
  body: ⟨ofInteger 0⟩

中文:
实例 :
  签名: 可居 (ContFract α)
  定义体: ⟨ofInteger 0⟩

Depends on / 依赖: ofInteger
-/
instance : Inhabited (ContFract α) :=
  ⟨ofInteger 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ContFract α) (SimpContFract α)
  body: ⟨Subtype.val⟩

中文:
实例 :
  签名: Coe (ContFract α) (SimpContFract α)
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance : Coe (ContFract α) (SimpContFract α) :=
  ⟨Subtype.val⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ContFract α) (GenContFract α)
  body: ⟨fun c => c.val⟩

中文:
实例 :
  签名: Coe (ContFract α) (GenContFract α)
  定义体: ⟨fun c => c.val⟩

Depends on / 依赖: c.val
-/
instance : Coe (ContFract α) (GenContFract α) :=
  ⟨fun c => c.val⟩

end ContFract

namespace GenContFract

/-!
### Computation of Convergents

We now define how to compute the convergents of a gcf. There are two standard ways to do this:
directly evaluating the (infinite) fraction described by the gcf or using a recurrence relation.
For (r)cfs, these computations are equivalent as shown in
`Algebra.ContinuedFractions.ConvergentsEquiv`.
-/

-- Fix a division ring for the computations.
variable {K : Type*} [DivisionRing K]

/-!
We start with the definition of the recurrence relation. Given a gcf `g`, for all `n ≥ 1`, we define
- `A₋₁ = 1, A₀ = h, Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
- `B₋₁ = 0, B₀ = 1, Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

`Aₙ, Bₙ` are called the *nth continuants*, `Aₙ` the *nth numerator*, and `Bₙ` the
*nth denominator* of `g`. The *nth convergent* of `g` is given by `Aₙ / Bₙ`.
-/

/--
Definition of `nextNum` / `nextNum` 的定义

English:
definition nextNum
  signature: (a b ppredA predA : K)
  body: b * predA + a * ppredA

中文:
定义 nextNum
  签名: (a b ppredA predA : K)
  定义体: b * predA + a * ppredA

Depends on / 依赖: ppredA
-/
def nextNum (a b ppredA predA : K) : K :=
  b * predA + a * ppredA

/--
Definition of `nextDen` / `nextDen` 的定义

English:
definition nextDen
  signature: (aₙ bₙ ppredB predB : K)
  body: bₙ * predB + aₙ * ppredB

中文:
定义 nextDen
  签名: (aₙ bₙ ppredB predB : K)
  定义体: bₙ * predB + aₙ * ppredB

Depends on / 依赖: ppredB
-/
def nextDen (aₙ bₙ ppredB predB : K) : K :=
  bₙ * predB + aₙ * ppredB

/--
Definition of `nextConts` / `nextConts` 的定义

English:
definition nextConts
  signature: (a b : K) (ppred pred : Pair K)
  body: ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩

中文:
定义 nextConts
  签名: (a b : K) (ppred pred : 对 K)
  定义体: ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩

Depends on / 依赖: nextDen, nextNum, ppred.a, ppred.b, pred.a, pred.b
-/
def nextConts (a b : K) (ppred pred : Pair K) : Pair K :=
  ⟨nextNum a b ppred.a pred.a, nextDen a b ppred.b pred.b⟩

/--
Definition of `contsAux` / `contsAux` 的定义

English:
definition contsAux
  signature: (g : GenContFract K)

中文:
定义 contsAux
  签名: (g : GenContFract K)
-/
def contsAux (g : GenContFract K) : Stream' (Pair K)
  | 0 => ⟨1, 0⟩
  | 1 => ⟨g.h, 1⟩
  | n + 2 =>
    match g.s.get? n with
    | none => contsAux g (n + 1)
    | some gp => nextConts gp.a gp.b (contsAux g n) (contsAux g (n + 1))

/--
Definition of `conts` / `conts` 的定义

English:
definition conts
  signature: (g : GenContFract K)
  body: g.contsAux.tail

中文:
定义 conts
  签名: (g : GenContFract K)
  定义体: g.contsAux.tail

Depends on / 依赖: contsAux, g.contsAux.tail
-/
def conts (g : GenContFract K) : Stream' (Pair K) :=
  g.contsAux.tail

/--
Definition of `nums` / `nums` 的定义

English:
definition nums
  signature: (g : GenContFract K)
  body: g.conts.map Pair.a

中文:
定义 nums
  签名: (g : GenContFract K)
  定义体: g.conts.map Pair.a

Depends on / 依赖: Pair.a, g.conts.map
-/
def nums (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.a

/--
Definition of `dens` / `dens` 的定义

English:
definition dens
  signature: (g : GenContFract K)
  body: g.conts.map Pair.b

中文:
定义 dens
  签名: (g : GenContFract K)
  定义体: g.conts.map Pair.b

Depends on / 依赖: Pair.b, g.conts.map
-/
def dens (g : GenContFract K) : Stream' K :=
  g.conts.map Pair.b

/--
Definition of `convs` / `convs` 的定义

English:
definition convs
  signature: (g : GenContFract K)
  body: fun n : Nat => g.nums n / g.dens n

中文:
定义 convs
  签名: (g : GenContFract K)
  定义体: fun n : Nat => g.nums n / g.dens n

Depends on / 依赖: g.dens, g.nums
-/
def convs (g : GenContFract K) : Stream' K :=
  fun n : Nat => g.nums n / g.dens n

/--
Definition of `convs'Aux` / `convs'Aux` 的定义

English:
definition convs'Aux
  signature: : Stream'.Seq (Pair K) -> Nat -> K

中文:
定义 convs'Aux
  签名: : Stream'.序列 (对 K) -> 自然数 -> K
-/
def convs'Aux : Stream'.Seq (Pair K) -> Nat -> K
  | _, 0 => 0
  | s, n + 1 =>
    match s.head with
    | none => 0
    | some gp => gp.a / (gp.b + convs'Aux s.tail n)

/--
Definition of `convs'` / `convs'` 的定义

English:
definition convs'
  signature: (g : GenContFract K) (n : Nat)
  body: g.h + convs'Aux g.s n

中文:
定义 convs'
  签名: (g : GenContFract K) (n : 自然数)
  定义体: g.h + convs'Aux g.s n
-/
def convs' (g : GenContFract K) (n : Nat) : K :=
  g.h + convs'Aux g.s n

end GenContFract
