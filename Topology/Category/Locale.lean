/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Frm
public import Mathlib.Topology.Category.CompHaus.Frm

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

@[expose] public section


universe u

open CategoryTheory Opposite Order TopologicalSpace


/-- The category of locales. -/
/-
**Locale** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Locale
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of locales.
-/
def Locale :=
  Frmᵒᵖ deriving LargeCategory

namespace Locale

/-
**Locale.** 是 Mathlib 中的一个实例，位于命名空间 `Locale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort Locale Type* :=
  ⟨fun X => X.unop⟩
/-
**Locale.** 是 Mathlib 中的一个实例，位于命名空间 `Locale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Locale) : Frame X :=
  X.unop.str

/-- Construct a bundled `Locale` from a `Frame`. -/
/-
**Locale.of** 是 Mathlib 中的一个定义，位于命名空间 `Locale`。
形式化陈述：of (α : Type*) [Frame α] : Locale
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `Locale` from a `Frame`.
-/
def of (α : Type*) [Frame α] : Locale :=
  op <| Frm.of α

@[simp]
/-
**Locale.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `Locale`。
形式化陈述：coe_of (α : Type*) [Frame α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [Frame α] : ↥(of α) = α :=
  rfl
/-
**Locale.** 是 Mathlib 中的一个实例，位于命名空间 `Locale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Locale :=
  ⟨of PUnit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps!]
/-
**topToLocale** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topToLocale : TopCat ⥤ Locale
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Top` to `Locale` which forgets that the space has "e
nough points".
-/
def topToLocale : TopCat ⥤ Locale :=
  topCatOpToFrm.rightOp

-- Note, `CompHaus` is too strong. We only need `T0Space`.
/-
**CompHausToLocale.faithful** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompHausToLocale.faithful : (compHausToTop ⋙ topToLocale.{u}).Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TopologicalSpace.Opens.comap_injective`：comap_injective [T0Space β] : In
jective (comap : C(α, β) -> FrameHom (Opens β) (Opens α))
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `CompHausLike.instT2SpaceCarrierObjTopCatCompHausLikeToTop`：∀ (P : TopCat
 → Prop) (X : CompHausLike P), T2Space ↑((CompHausLike.compHausLikeToTop P).obj 
X)
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `CompHausLike.instCompactSpaceCarrierObjTopCatCompHausLikeToTop`：∀ (P : T
opCat → Prop) (X : CompHausLike P), CompactSpace ↑((CompHausLike.compHausLikeToT
op P).obj X)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
-/
instance CompHausToLocale.faithful : (compHausToTop ⋙ topToLocale.{u}).Faithful :=
  ⟨fun h => by
    dsimp at h
    exact ConcreteCategory.ext (Opens.comap_injective (congr_arg Frm.Hom.hom
      (Quiver.Hom.op_inj h)))⟩
