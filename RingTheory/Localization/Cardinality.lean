/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.GroupTheory.MonoidLocalization.Cardinality
public import Mathlib.RingTheory.OreLocalization.Cardinality

/-!
# Cardinality of localizations

In this file, we establish the cardinality of localizations. In most cases, a localization has
cardinality equal to the base ring. If there are zero-divisors, however, this is no longer true -
for example, `ZMod 6` localized at `{2, 4}` is equal to `ZMod 3`, and if you have zero in your
submonoid, then your localization is trivial (see `IsLocalization.uniqueOfZeroMem`).

## Main statements

* `IsLocalization.cardinalMk_le`: A localization has cardinality no larger than the base ring.
* `IsLocalization.cardinalMk`: If you don't localize at zero-divisors, the localization of a ring
  has cardinality equal to its base ring.

-/

public section


open Cardinal nonZeroDivisors

universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] {L : Type v} [CommSemiring L] [Algebra R L]

namespace IsLocalization

/-
**IsLocalization.lift_cardinalMk_le** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_cardinalMk_le (S : Submonoid R) [IsLocalization S L] : Cardinal.lift.
{u} #L <= Cardinal.lift.{v} #R
参数：S : Submonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.cardinalMk_le`：cardinalMk_le : #(Localization S) <= #M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem lift_cardinalMk_le (S : Submonoid R) [IsLocalization S L] :
    Cardinal.lift.{u} #L ≤ Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk_le S
  rwa [← lift_le.{v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

/-- A localization always has cardinality less than or equal to the base ring. -/
/-
**IsLocalization.cardinalMk_le** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：cardinalMk_le {L : Type u} [CommSemiring L] [Algebra R L] (S : Submonoid R
) [IsLocalization S L] : #L <= #R
参数：S : Submonoid R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsLocalization.lift_cardinalMk_le`：lift_cardinalMk_le (S : Submonoid R) 
[IsLocalization S L] : Cardinal.lift.{u} #L <= Cardinal.lift.{v} #R

--- 原说明 ---
A localization always has cardinality less than or equal to the base ring.
-/
theorem cardinalMk_le {L : Type u} [CommSemiring L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] : #L ≤ #R := by
  simpa using lift_cardinalMk_le (L := L) S

end IsLocalization

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]

namespace Localization

/-
**Localization.cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：cardinalMk {S : Submonoid R} (hS : S <= R⁰) : #(Localization S) = #R
参数：hS : S <= R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.cardinalMk`：cardinalMk (hS : S <= nonZeroDivisorsLeft R)
 : #(OreLocalization S R) = #R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nonZeroDivisorsLeft_eq_nonZeroDivisors`：nonZeroDivisorsLeft_eq_nonZeroDi
visors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀
-/
theorem cardinalMk {S : Submonoid R} (hS : S ≤ R⁰) : #(Localization S) = #R := by
  apply OreLocalization.cardinalMk
  rwa [nonZeroDivisorsLeft_eq_nonZeroDivisors]

end Localization

namespace IsLocalization

variable (L)

/-
**IsLocalization.lift_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：lift_cardinalMk (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰) : Ca
rdinal.lift.{u} #L = Cardinal.lift.{v} #R
参数：S : Submonoid R；hS : S <= R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.cardinalMk`：cardinalMk {S : Submonoid R} (hS : S <= R⁰) : #
(Localization S) = #R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
-/
theorem lift_cardinalMk (S : Submonoid R) [IsLocalization S L] (hS : S ≤ R⁰) :
    Cardinal.lift.{u} #L = Cardinal.lift.{v} #R := by
  have := Localization.cardinalMk hS
  rwa [← lift_inj.{u, v}, lift_mk_eq'.2 ⟨(Localization.algEquiv S L).toEquiv⟩] at this

/-- If you do not localize at any zero-divisors, localization preserves cardinality. -/
/-
**IsLocalization.cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：cardinalMk (L : Type u) [CommRing L] [Algebra R L] (S : Submonoid R) [IsLo
calization S L] (hS : S <= R⁰) : #L = #R
参数：L : Type u；S : Submonoid R；hS : S <= R⁰。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `IsLocalization.lift_cardinalMk`：lift_cardinalMk (S : Submonoid R) [IsLoc
alization S L] (hS : S <= R⁰) : Cardinal.lift.{u} #L = Cardinal.lift.{v} #R

--- 原说明 ---
If you do not localize at any zero-divisors, localization preserves cardinality.
-/
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L]
    (S : Submonoid R) [IsLocalization S L] (hS : S ≤ R⁰) : #L = #R := by
  simpa using lift_cardinalMk L S hS

end IsLocalization

@[simp]
/-
**Cardinal.mk_fractionRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Cardinal.mk_fractionRing (R : Type u) [CommRing R] : #(FractionRing R) = #
R
参数：R : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.cardinalMk`：cardinalMk (L : Type u) [CommRing L] [Algebra
 R L] (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰) : #L = #R
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Cardinal.mk_fractionRing (R : Type u) [CommRing R] : #(FractionRing R) = #R :=
  IsLocalization.cardinalMk (FractionRing R) R⁰ le_rfl

alias FractionRing.cardinalMk := Cardinal.mk_fractionRing

namespace IsFractionRing

variable (R L)

/-
**IsFractionRing.lift_cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：lift_cardinalMk [IsFractionRing R L] : Cardinal.lift.{u} #L = Cardinal.lif
t.{v} #R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.lift_cardinalMk`：lift_cardinalMk (S : Submonoid R) [IsLoc
alization S L] (hS : S <= R⁰) : Cardinal.lift.{u} #L = Cardinal.lift.{v} #R
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lift_cardinalMk [IsFractionRing R L] : Cardinal.lift.{u} #L = Cardinal.lift.{v} #R :=
  IsLocalization.lift_cardinalMk L _ le_rfl
/-
**IsFractionRing.cardinalMk** 是 Mathlib 中的一个定理，位于命名空间 `IsFractionRing`。
形式化陈述：cardinalMk (L : Type u) [CommRing L] [Algebra R L] [IsFractionRing R L] : 
#L = #R
参数：L : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.cardinalMk`：cardinalMk (L : Type u) [CommRing L] [Algebra
 R L] (S : Submonoid R) [IsLocalization S L] (hS : S <= R⁰) : #L = #R
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem cardinalMk (L : Type u) [CommRing L] [Algebra R L] [IsFractionRing R L] : #L = #R :=
  IsLocalization.cardinalMk L _ le_rfl

end IsFractionRing

end CommRing

