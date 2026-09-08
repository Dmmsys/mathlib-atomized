/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Dedekind rings and domains

This file defines the notion of a Dedekind ring (domain),
as a Noetherian integrally closed commutative ring (domain) of Krull dimension at most one.

## Main definitions

- `IsDedekindRing` defines a Dedekind ring as a commutative ring that is
  Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
  `isDedekindRing_iff` shows that this does not depend on the choice of field of fractions.
- `IsDedekindDomain` defines a Dedekind domain as a Dedekind ring that is a domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDedekindRing R`.
This should be safe since the start and end point is the literal same expression,
which the tabled typeclass synthesis algorithm can deal with.

Often, definitions assume that Dedekind rings are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

public section


variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
/-
**Ring.DimensionLEOne** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ring`。
形式化陈述：(R : Type u_1) → [CommRing R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring `R` has Krull dimension at most one if all nonzero prime ideals are maxim
al.
-/
class Ring.DimensionLEOne : Prop where
  (maximalOfPrime : ∀ {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal)

open Ideal Ring
/-
**Ideal.IsPrime.isMaximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [DimensionLEOne R] {p : I
deal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
参数：h : p.IsPrime；hp : p != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.DimensionLEOne.maximalOfPrime`：∀ {R : Type u_1} {inst : CommRing R}
 [self : Ring.DimensionLEOne R] {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal
-/
theorem Ideal.IsPrime.isMaximal {R : Type*} [CommRing R] [DimensionLEOne R]
    {p : Ideal R} (h : p.IsPrime) (hp : p ≠ ⊥) : p.IsMaximal :=
  DimensionLEOne.maximalOfPrime hp h

namespace Ring.DimensionLEOne

/-
**Ring.DimensionLEOne.principal_ideal_ring** 是 Mathlib 中的一个实例，位于命名空间 `Ring.Dimen
sionLEOne`。
形式化陈述：principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] : DimensionLEOn
e A where maximalOfPrime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrime.to_maximal_ideal`：to_maximal_ideal [CommRing R] [IsDomain R] [Is
PrincipalIdealRing R] {S : Ideal R} [hpi : IsPrime S] (hS : S != ⊥) : IsMaximal 
S
-/
instance principal_ideal_ring [IsDomain A] [IsPrincipalIdealRing A] :
    DimensionLEOne A where
  maximalOfPrime := fun nonzero _ =>
    IsPrime.to_maximal_ideal nonzero
/-
**Ring.DimensionLEOne.of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DimensionLEO
ne`。
形式化陈述：of_isIntegral (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R] [Algebr
a R B] [Algebra.IsIntegral R B] [DimensionLEOne R] : DimensionLEOne B where maxi
malOfPrime
参数：B : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsIntegral.isMaximal_of_isMaximal_comap`：∀ {R : Type u_1} [inst : 
CommRing R] {A : Type u_3} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algeb
ra.IsIntegral R A] (I : Ideal A) [I…
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsIntegral.comap_ne_bot`：∀ (R : Type u_1) [inst : CommRing R] {A :
 Type u_3} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.IsIntegral R 
A] [IsDomain A] [No…
-/
theorem of_isIntegral (B : Type*) [CommRing B] [IsDomain B] [Nontrivial R]
    [Algebra R B] [Algebra.IsIntegral R B] [DimensionLEOne R] :
    DimensionLEOne B where
  maximalOfPrime := fun {p} ne_bot _ =>
    IsIntegral.isMaximal_of_isMaximal_comap p
      (Ideal.IsPrime.isMaximal inferInstance (IsIntegral.comap_ne_bot R ne_bot))

@[deprecated (since := "2026-05-08")] alias isIntegralClosure := of_isIntegral

nonrec instance integralClosure [Nontrivial R] [IsDomain A] [Algebra R A] [DimensionLEOne R] :
    DimensionLEOne (integralClosure R A) :=
  DimensionLEOne.of_isIntegral R (integralClosure R A)

variable {R}
/-
**Ring.DimensionLEOne.not_lt_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DimensionLEOne`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [Ring.DimensionLEOne R] (p₀ p₁ p₂ : I
deal R) [hp₁ : p₁.IsPrime] [hp₂ : p₂.IsPrime],   ¬(p₀ < p₁ ∧ p₁ < p₂)
参数：p₀ p₁ p₂ : Ideal R；p₀ < p₁ ∧ p₁ < p₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem not_lt_lt [Ring.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime]
    [hp₂ : p₂.IsPrime] : ¬(p₀ < p₁ ∧ p₁ < p₂)
  | ⟨h01, h12⟩ => h12.ne ((hp₁.isMaximal (bot_le.trans_lt h01).ne').eq_of_le hp₂.ne_top h12.le)
/-
**Ring.DimensionLEOne.eq_bot_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DimensionLEOn
e`。
形式化陈述：eq_bot_of_lt [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime] [P.IsPrim
e] (hpP : p < P) : p = ⊥
参数：p P : Ideal R；hpP : p < P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ring.DimensionLEOne.not_lt_lt`：∀ {R : Type u_1} [inst : CommRing R] [Rin
g.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime] [hp₂ : p₂.IsPrime], 
  ¬(p₀ < p₁ ∧ p₁ < …
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem eq_bot_of_lt [Ring.DimensionLEOne R] (p P : Ideal R) [p.IsPrime] [P.IsPrime] (hpP : p < P) :
    p = ⊥ :=
  by_contra fun hp0 => not_lt_lt ⊥ p P ⟨Ne.bot_lt hp0, hpP⟩

variable {A} in
/-
**Ring.DimensionLEOne.of_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Ring.DimensionLEOn
e`。
形式化陈述：of_ringEquiv [hA : Ring.DimensionLEOne A] (e : R ≃+* A) : Ring.DimensionLE
One R where maximalOfPrime {P} hP_ne hP_prime
参数：e : R ≃+* A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_comap_eq_self_of_equiv`：map_comap_eq_self_of_equiv {E : Type*}
 [EquivLike E R S] [RingEquivClass E R S] (e : E) (I : Ideal S) : map e (comap e
 I) = I
· 使用定理 `Ideal.isMaximal_map_iff_of_bijective`：isMaximal_map_iff_of_bijective : I
sMaximal (map f I) ↔ IsMaximal I
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `Ring.DimensionLEOne.maximalOfPrime`：∀ {R : Type u_1} {inst : CommRing R}
 [self : Ring.DimensionLEOne R] {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.comap_symm`：comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.sym
m = I.map f
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
-/
theorem of_ringEquiv [hA : Ring.DimensionLEOne A] (e : R ≃+* A) : Ring.DimensionLEOne R where
  maximalOfPrime {P} hP_ne hP_prime := by
    rw [← Ideal.map_comap_eq_self_of_equiv e.symm P,
      Ideal.isMaximal_map_iff_of_bijective _ e.symm.bijective]
    apply Ring.DimensionLEOne.maximalOfPrime ?_ (P.comap_isPrime e.symm)
    simp [Ideal.map_eq_bot_iff_of_injective e.injective, hP_ne]

-- TODO: replace `Ring.DimensionLEOne` with `Ring.KrullDimLE`.
/-
**Ring.DimensionLEOne.** 是 Mathlib 中的一个实例，位于命名空间 `Ring.DimensionLEOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {R : Type*} [CommRing R] [Ring.DimensionLEOne R] : Ring.KrullDimLE 1 R :=
  .mk₁' fun _ hI hI' ↦ hI'.isMaximal hI

end Ring.DimensionLEOne

/-- A Dedekind ring is a commutative ring that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is exactly `IsDedekindDomain` minus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fractions:
use `isDedekindRing_iff` to prove `IsDedekindRing` for a given `fraction_map`.
-/
/-
**IsDedekindRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_2) → [CommRing A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Dedekind ring is a commutative ring that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is exactly `IsDedekindDomain` minus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fraction
s:
use `isDedekindRing_iff` to prove `IsDedekindRing` for a given `fraction_map`.
-/
class IsDedekindRing : Prop
  extends IsNoetherian A A, DimensionLEOne A, IsIntegralClosure A A (FractionRing A)

/-- An integral domain is a Dedekind domain if and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
/-
**isDedekindRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing 
A K] : IsDedekindRing A ↔ IsNoetherianRing A ∧ DimensionLEOne A ∧ forall {x : K}
, IsIntegral A x -> exists y, algebraMap A K y = x
参数：K : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
An integral domain is a Dedekind domain if and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction fiel
d.
In particular, this definition does not depend on the choice of this fraction fi
eld.
-/
theorem isDedekindRing_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindRing A ↔
      IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hr, hd, hi⟩ => { hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

/-- A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

This is exactly `IsDedekindRing` plus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fractions:
use `isDedekindDomain_iff` to prove `IsDedekindDomain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`IsDedekindDomainDvr` and `IsDedekindDomainInv`.
-/
/-
**IsDedekindDomain** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_2) → [CommRing A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Dedekind domain is an integral domain that is Noetherian, integrally closed, a
nd
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

This is exactly `IsDedekindRing` plus the `IsDomain` hypothesis.

The integral closure condition is independent of the choice of field of fraction
s:
use `isDedekindDomain_iff` to prove `IsDedekindDomain` for a given `fraction_map
`.

This is the default implementation, but there are equivalent definitions,
`IsDedekindDomainDvr` and `IsDedekindDomainInv`.
-/
class IsDedekindDomain : Prop
  extends IsDomain A, IsDedekindRing A

attribute [instance 90] IsDedekindDomain.toIsDomain

/-- Make a Dedekind domain from a Dedekind ring given that it is a domain.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDedekindRing R`.
This should be safe since the start and end point is the literal same expression,
which the tabled typeclass synthesis algorithm can deal with.
-/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a Dedekind domain from a Dedekind ring given that it is a domain.

`IsDedekindRing` and `IsDedekindDomain` form a cycle in the typeclass hierarchy:
`IsDedekindRing R + IsDomain R` imply `IsDedekindDomain R`, which implies `IsDed
ekindRing R`.
This should be safe since the start and end point is the literal same expression
,
which the tabled typeclass synthesis algorithm can deal with.
-/
instance [IsDomain A] [IsDedekindRing A] : IsDedekindDomain A where

/-- An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
/-
**isDedekindDomain_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDedekindDomain_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRin
g A K] : IsDedekindDomain A ↔ IsDomain A ∧ IsNoetherianRing A ∧ DimensionLEOne A
 ∧ forall {x : K}, IsIntegral A x -> exists y, algebraMap A K y = x
参数：K : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a

--- 原说明 ---
An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction fiel
d.
In particular, this definition does not depend on the choice of this fraction fi
eld.
-/
theorem isDedekindDomain_iff (K : Type*) [CommRing K] [Algebra A K] [IsFractionRing A K] :
    IsDedekindDomain A ↔
      IsDomain A ∧ IsNoetherianRing A ∧ DimensionLEOne A ∧
        ∀ {x : K}, IsIntegral A x → ∃ y, algebraMap A K y = x :=
  ⟨fun _ => ⟨inferInstance, inferInstance, inferInstance,
             fun {_} => (isIntegrallyClosed_iff K).mp inferInstance⟩,
   fun ⟨hid, hr, hd, hi⟩ => { hid, hr, hd, (isIntegrallyClosed_iff K).mpr @hi with }⟩

-- See library note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsPrincipalIdealRing.isDedekindDomain
    [IsDomain A] [IsPrincipalIdealRing A] :
    IsDedekindDomain A :=
  { PrincipalIdealRing.isNoetherianRing, Ring.DimensionLEOne.principal_ideal_ring A,
    UniqueFactorizationMonoid.instIsIntegrallyClosed with }

variable {R} in
/-
**IsLocalRing.primesOver_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.primesOver_eq [IsLocalRing A] [IsDedekindDomain A] [Algebra R 
A] [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p !
= ⊥) : Ideal.primesOver p A = {IsLocalRing.maximalIdeal A}
参数：hp0 : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_nonempty_unique_mem`：eq_singleton_iff_nonempty_uniq
ue_mem : s = {a} ↔ s.Nonempty ∧ forall x in s, x = a
· 使用定理 `Ideal.exists_maximal_ideal_liesOver_of_isIntegral`：exists_maximal_ideal_
liesOver_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R)
 [P.IsMaximal] : exists (Q : Ideal S), …
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.ne_bot_of_mem_primesOver`：ne_bot_of_mem_primesOver [FaithfulSMul A
 B] (hp : p != ⊥) {P : Ideal B} (hP : P in p.primesOver B) : P != ⊥
-/
theorem IsLocalRing.primesOver_eq [IsLocalRing A] [IsDedekindDomain A] [Algebra R A]
    [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Ideal.primesOver p A = {IsLocalRing.maximalIdeal A} := by
  have : IsDomain R := .of_faithfulSMul R A
  refine Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨?_, fun P hP ↦ ?_⟩
  · obtain ⟨w', hmax, hover⟩ := exists_maximal_ideal_liesOver_of_isIntegral (S := A) p
    exact ⟨w', hmax.isPrime, hover⟩
  · exact IsLocalRing.eq_maximalIdeal <| hP.1.isMaximal (Ideal.ne_bot_of_mem_primesOver hp0 hP)
