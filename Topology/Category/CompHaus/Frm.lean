/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Frm
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Sets.Opens

/-! The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/

@[expose] public section

universe u

open TopologicalSpace Opposite CategoryTheory

/-- The forgetful functor from `TopCatᵒᵖ` to `Frm`. -/
@[simps]
/-
**topCatOpToFrm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topCatOpToFrm : TopCatᵒᵖ ⥤ Frm where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `TopCatᵒᵖ` to `Frm`.
-/
def topCatOpToFrm : TopCatᵒᵖ ⥤ Frm where
  obj X := Frm.of (Opens (unop X : TopCat))
  map f := Frm.ofHom <| Opens.comap <| (Quiver.Hom.unop f).hom

-- Note, `CompHaus` is too strong. We only need `T0Space`.
/-
**CompHausOpToFrame.faithful** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompHausOpToFrame.faithful : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithf
ul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
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
· 使用定理 `CompHaus.instT2SpaceCarrierToTopTrue`：∀ {X : CompHaus}, T2Space ↑X.toTop
· 使用定理 `NormalSpace.of_regularSpace_lindelofSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [RegularSpace X] [LindelofSpace X], NormalSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `CompHaus.instCompactSpaceCarrierToTopTrue`：∀ {X : CompHaus}, CompactSpac
e ↑X.toTop
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `instLindelofSpaceOfSigmaCompactSpace`：∀ {X : Type u} [inst : Topological
Space X] [SigmaCompactSpace X], LindelofSpace X
· 使用定理 `CompactSpace.sigmaCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
[CompactSpace X], SigmaCompactSpace X
· 使用定理 `FrameHom.ext`：ext {f g : FrameHom α β} (h : forall a, f a = g a) : f = g
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
-/
instance CompHausOpToFrame.faithful : (compHausToTop.op ⋙ topCatOpToFrm.{u}).Faithful :=
  ⟨fun {X _ _ _} h =>  Quiver.Hom.unop_inj <| ConcreteCategory.ext <|
    Opens.comap_injective (β := (unop X).toTop) <| FrameHom.ext <|
      CategoryTheory.congr_fun h⟩
