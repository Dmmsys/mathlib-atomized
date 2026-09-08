/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Well-powered categories

A category `(C : Type u) [Category.{v} C]` is `[WellPowered.{w} C]`
if `C` is locally small relative to `w` and for every `X : C`,
we have `Small.{w} (Subobject X)`. The most common case is when `w = v`,
in which case, it only involves the condition `Small.{v} (Subobject X)`

(Note that in this situation `Subobject X : Type (max u v)`,
so this is a nontrivial condition for large categories,
but automatic for small categories.)

This is equivalent to the category `MonoOver X` being `EssentiallySmall.{w}` for all `X : C`.

When a category is well-powered, you can obtain nonconstructive witnesses as
`Shrink (Subobject X) : Type w`
and
`equivShrink (Subobject X) : Subobject X ≃ Shrink (Subobject X)`.
-/

public section


universe w v v₂ u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v} C]

/--
A category (with morphisms in `Type v`) is well-powered relative to a universe `w`
if it is locally small and `Subobject X` is `w`-small for every `X`.

We show in `wellPowered_of_essentiallySmall_monoOver` and `essentiallySmall_monoOver`
that this is the case if and only if `MonoOver X` is `w`-essentially small for every `X`.
-/
@[pp_with_univ]
/-
**CategoryTheory.WellPowered** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：WellPowered [LocallySmall.{w} C] : Prop where subobject_small : forall X :
 C, Small.{w} (Subobject X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category (with morphisms in `Type v`) is well-powered relative to a universe `
w`
if it is locally small and `Subobject X` is `w`-small for every `X`.

We show in `wellPowered_of_essentiallySmall_monoOver` and `essentiallySmall_mono
Over`
that this is the case if and only if `MonoOver X` is `w`-essentially small for e
very `X`.
-/
class WellPowered [LocallySmall.{w} C] : Prop where
  subobject_small : ∀ X : C, Small.{w} (Subobject X) := by infer_instance
/-
**CategoryTheory.small_subobject** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：small_subobject [LocallySmall.{w} C] [WellPowered C] (X : C) : Small.{w} (
Subobject X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.WellPowered.subobject_small`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v, u₁} C} {inst_1 : CategoryTheory.LocallySmall.{w, v, u₁} 
C}   [self : CategoryTheory.Well…
-/
instance small_subobject [LocallySmall.{w} C] [WellPowered C] (X : C) :
    Small.{w} (Subobject X) :=
  WellPowered.subobject_small X
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) wellPowered_of_smallCategory (C : Type u₁) [SmallCategory C] :
    WellPowered.{u₁} C where

variable {C}
/-
**CategoryTheory.essentiallySmall_monoOver_iff_small_subobject** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory`。
形式化陈述：essentiallySmall_monoOver_iff_small_subobject (X : C) : EssentiallySmall.{
w} (MonoOver X) ↔ Small.{w} (Subobject X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.essentiallySmall_iff_of_thin`：essentiallySmall_iff_of_thi
n {C : Type u} [Category.{v} C] [Quiver.IsThin C] : EssentiallySmall.{w} C ↔ Sma
ll.{w} (Skeleton C)
-/
theorem essentiallySmall_monoOver_iff_small_subobject (X : C) :
    EssentiallySmall.{w} (MonoOver X) ↔ Small.{w} (Subobject X) :=
  essentiallySmall_iff_of_thin
/-
**CategoryTheory.wellPowered_of_essentiallySmall_monoOver** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory`。
形式化陈述：wellPowered_of_essentiallySmall_monoOver [LocallySmall.{w} C] (h : forall 
X : C, EssentiallySmall.{w} (MonoOver X)) : WellPowered.{w} C
参数：h : forall X : C, EssentiallySmall.{w} (MonoOver X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.essentiallySmall_monoOver_iff_small_subobject`：essentiall
ySmall_monoOver_iff_small_subobject (X : C) : EssentiallySmall.{w} (MonoOver X) 
↔ Small.{w} (Subobject X)
-/
theorem wellPowered_of_essentiallySmall_monoOver [LocallySmall.{w} C]
    (h : ∀ X : C, EssentiallySmall.{w} (MonoOver X)) :
    WellPowered.{w} C :=
  { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }

section

variable [LocallySmall.{w} C] [WellPowered.{w} C]

/-
**CategoryTheory.essentiallySmall_monoOver** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory`。
形式化陈述：essentiallySmall_monoOver (X : C) : EssentiallySmall.{w} (MonoOver X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.essentiallySmall_monoOver_iff_small_subobject`：essentiall
ySmall_monoOver_iff_small_subobject (X : C) : EssentiallySmall.{w} (MonoOver X) 
↔ Small.{w} (Subobject X)
· 使用定理 `CategoryTheory.WellPowered.subobject_small`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v, u₁} C} {inst_1 : CategoryTheory.LocallySmall.{w, v, u₁} 
C}   [self : CategoryTheory.Well…
-/
instance essentiallySmall_monoOver (X : C) : EssentiallySmall.{w} (MonoOver X) :=
  (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)

end

section Equivalence

variable {D : Type u₂} [Category.{v₂} D]

/-
**CategoryTheory.wellPowered_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`
。
形式化陈述：wellPowered_of_equiv (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
 [WellPowered.{w} C] : WellPowered.{w} D
参数：e : C ≌ D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_essentiallySmall_monoOver`：wellPowered_of_
essentiallySmall_monoOver [LocallySmall.{w} C] (h : forall X : C, EssentiallySma
ll.{w} (MonoOver X)) : WellPowered.{w} C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.essentiallySmall_congr`：essentiallySmall_congr {C : Type 
u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (e : C ≌ D) : EssentiallySma
ll.{w} C ↔ EssentiallySmall…
-/
theorem wellPowered_of_equiv (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
    [WellPowered.{w} C] : WellPowered.{w} D :=
  wellPowered_of_essentiallySmall_monoOver fun X =>
    (essentiallySmall_congr (MonoOver.congr X e.symm)).2 <| by infer_instance

/-- Being well-powered is preserved by equivalences. -/
/-
**CategoryTheory.wellPowered_congr** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：wellPowered_congr (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D] : 
WellPowered.{w} C ↔ WellPowered.{w} D
参数：e : C ≌ D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.wellPowered_of_equiv`：wellPowered_of_equiv (e : C ≌ D) [L
ocallySmall.{w} C] [LocallySmall.{w} D] [WellPowered.{w} C] : WellPowered.{w} D

--- 原说明 ---
Being well-powered is preserved by equivalences.
-/
theorem wellPowered_congr (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D] :
    WellPowered.{w} C ↔ WellPowered.{w} D :=
  ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LocallySmall.{w} C] [WellPowered.{w} C] :
    WellPowered.{w, w} (ShrinkHoms C) :=
  wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C)

end Equivalence

end CategoryTheory

