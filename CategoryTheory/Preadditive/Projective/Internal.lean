/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!

# Internal projectivity

This file defines internal projectivity of objects `P` in a category `C` as a class
`InternallyProjective P`. This means that the functor taking internal homs out of `P`
preserves epimorphisms. It also proves that a retract of an internally projective object
is internally projective (see `InternallyProjective.ofRetract`).

This property is important in the setting of light condensed abelian groups, when establishing
the solid theory (see the lecture series on analytic stacks:
https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Functor

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/--
An object `P : C` is *internally projective* if the functor `P ⟶[C] -` taking internal homs
out of `P` preserves epimorphisms.
-/
/-
**CategoryTheory.isInternallyProjective** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：isInternallyProjective : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `P : C` is *internally projective* if the functor `P ⟶[C] -` taking in
ternal homs
out of `P` preserves epimorphisms.
-/
def isInternallyProjective : ObjectProperty C := fun P ↦ (ihom P).PreservesEpimorphisms

/--
An object `P : C` is *internally projective* if the functor `P ⟶[C] -` taking internal homs
out of `P` preserves epimorphisms.
-/
/-
**CategoryTheory.InternallyProjective** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y`。
形式化陈述：InternallyProjective (P : C)
参数：P : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `P : C` is *internally projective* if the functor `P ⟶[C] -` taking in
ternal homs
out of `P` preserves epimorphisms.
-/
abbrev InternallyProjective (P : C) := isInternallyProjective.Is P
/-
**CategoryTheory.InternallyProjective.preserves_epi** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.InternallyProjective`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.MonoidalClosed C] (
P : C) [CategoryTheory.InternallyProjective P],   (CategoryTheory.ihom P).Preser
vesEpimorphisms
参数：P : C；CategoryTheory.ihom P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_is`：prop_of_is (P : ObjectProperty
 C) (X : C) [P.Is X] : P X
-/
instance InternallyProjective.preserves_epi (P : C) [InternallyProjective P] :
    (ihom P).PreservesEpimorphisms :=
  isInternallyProjective.prop_of_is P
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (isInternallyProjective (C := C)).IsStableUnderRetracts where
  of_retract {Y X} r h :=
    have : InternallyProjective X := ⟨h⟩
    have : Retract (ihom Y) (ihom X) := r.op.map internalHom
    PreservesEpimorphisms.ofRetract this

namespace InternallyProjective

/-
**CategoryTheory.InternallyProjective.ofRetract** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.InternallyProjective`。
形式化陈述：ofRetract {X Y : C} (r : Retract Y X) [InternallyProjective X] : Internall
yProjective Y
参数：r : Retract Y X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_retract`：prop_of_retract [IsStable
UnderRetracts P] {X Y : C} (h : Retract X Y) (hY : P Y) : P X
· 使用定理 `CategoryTheory.instIsStableUnderRetractsIsInternallyProjective`：∀ {C : T
ype u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.
MonoidalCategory C]   [inst_2 : CategoryTheory.Monoi…
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_is`：prop_of_is (P : ObjectProperty
 C) (X : C) [P.Is X] : P X
-/
lemma ofRetract {X Y : C} (r : Retract Y X) [InternallyProjective X] : InternallyProjective Y :=
  ⟨isInternallyProjective.prop_of_retract r (isInternallyProjective.prop_of_is _)⟩

end CategoryTheory.InternallyProjective

