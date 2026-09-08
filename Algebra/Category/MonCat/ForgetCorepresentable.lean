/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.CategoryTheory.Yoneda

/-!
# The forgetful functor is corepresentable

The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable
by `ULift ℕ`. Similar results are obtained for the variants `CommMonCat`, `AddMonCat`
and `MonCat`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u

open CategoryTheory Opposite

/-!
### `(ULift ℕ →+ G) ≃ G`

These universe-monomorphic variants of `multiplesHom`/`powersHom` are put here since they
shouldn't be useful outside of category theory.
-/

/-- Monoid homomorphisms from `ULift ℕ` are defined by the image of `1`. -/
@[simps!]
/-
**uliftMultiplesHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uliftMultiplesHom (M : Type u) [AddMonoid M] : M ≃ (ULift.{u} Nat ->+ M)
参数：M : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Monoid homomorphisms from `ULift ℕ` are defined by the image of `1`.
-/
def uliftMultiplesHom (M : Type u) [AddMonoid M] : M ≃ (ULift.{u} ℕ →+ M) :=
  (multiplesHom _).trans AddEquiv.ulift.symm.addMonoidHomCongrLeftEquiv

/-- Monoid homomorphisms from `ULift (Multiplicative ℕ)` are defined by the image
of `Multiplicative.ofAdd 1`. -/
@[simps!]
/-
**uliftPowersHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：uliftPowersHom (M : Type u) [Monoid M] : M ≃ (ULift.{u} (Multiplicative Na
t) ->* M)
参数：M : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Monoid homomorphisms from `ULift (Multiplicative ℕ)` are defined by the image
of `Multiplicative.ofAdd 1`.
-/
def uliftPowersHom (M : Type u) [Monoid M] : M ≃ (ULift.{u} (Multiplicative ℕ) →* M) :=
  (powersHom _).trans MulEquiv.ulift.symm.monoidHomCongrLeftEquiv

/-- The forgetful functor `MonCat.{u} ⥤ Type u` is corepresentable. -/
/-
**MonCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} (Multiplicat
ive Nat)))) ≅ forget MonCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forgetful functor `MonCat.{u} ⥤ Type u` is corepresentable.
-/
def MonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℕ)))) ≅ forget MonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso


/-- The forgetful functor `CommMonCat.{u} ⥤ Type u` is corepresentable. -/
/-
**CommMonCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CommMonCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} (Multipl
icative Nat)))) ≅ forget CommMonCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forgetful functor `CommMonCat.{u} ⥤ Type u` is corepresentable.
-/
def CommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} (Multiplicative ℕ)))) ≅ forget CommMonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftPowersHom M.carrier).symm).toIso

/-- The forgetful functor `AddMonCat.{u} ⥤ Type u` is corepresentable. -/
/-
**AddMonCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddMonCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} Nat))) ≅ 
forget AddMonCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forgetful functor `AddMonCat.{u} ⥤ Type u` is corepresentable.
-/
def AddMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℕ))) ≅ forget AddMonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso

/-- The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable. -/
/-
**AddCommMonCat.coyonedaObjIsoForget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddCommMonCat.coyonedaObjIsoForget : coyoneda.obj (op (of (ULift.{u} Nat))
) ≅ forget AddCommMonCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The forgetful functor `AddCommMonCat.{u} ⥤ Type u` is corepresentable.
-/
def AddCommMonCat.coyonedaObjIsoForget :
    coyoneda.obj (op (of (ULift.{u} ℕ))) ≅ forget AddCommMonCat.{u} :=
  NatIso.ofComponents fun M ↦
    (ConcreteCategory.homEquiv.trans (uliftMultiplesHom M.carrier).symm).toIso
/-
**MonCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MonCat.forget_isCorepresentable : (forget MonCat.{u}).IsCorepresentable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance MonCat.forget_isCorepresentable :
    (forget MonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' MonCat.coyonedaObjIsoForget
/-
**CommMonCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CommMonCat.forget_isCorepresentable : (forget CommMonCat.{u}).IsCorepresen
table
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance CommMonCat.forget_isCorepresentable :
    (forget CommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' CommMonCat.coyonedaObjIsoForget
/-
**AddMonCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddMonCat.forget_isCorepresentable : (forget AddMonCat.{u}).IsCorepresenta
ble
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance AddMonCat.forget_isCorepresentable :
    (forget AddMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddMonCat.coyonedaObjIsoForget
/-
**AddCommMonCat.forget_isCorepresentable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddCommMonCat.forget_isCorepresentable : (forget AddCommMonCat.{u}).IsCore
presentable
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCorepresentable.mk'`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (Type v₁)} {X : 
C}   (e : CategoryTheory.coyoneda.…
-/
instance AddCommMonCat.forget_isCorepresentable :
    (forget AddCommMonCat.{u}).IsCorepresentable :=
  Functor.IsCorepresentable.mk' AddCommMonCat.coyonedaObjIsoForget
