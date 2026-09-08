/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Module

/-!

# Equivalence of light condensed objects with sheaves on a small site
-/

@[expose] public section

universe u v w

open CategoryTheory Sheaf Functor

namespace LightCondensed

variable {C : Type w} [Category.{v} C]

variable (C) in
/--
The equivalence of categories from light condensed objects to sheaves on a small site
equivalent to light profinite sets.
-/
/-
**LightCondensed.equivSmall** 是 Mathlib 中的一个缩写定义，位于命名空间 `LightCondensed`。
形式化陈述：equivSmall : LightCondensed.{u} C ≌ Sheaf ((equivSmallModel.{u} LightProfi
nite.{u}).inverse.inducedTopology (coherentTopology LightProfinite.{u})) C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instEssentiallySmallLightProfinite`：CategoryTheory.EssentiallySmall.{u, 
u, u + 1} LightProfinite

--- 原说明 ---
The equivalence of categories from light condensed objects to sheaves on a small
 site
equivalent to light profinite sets.
-/
noncomputable abbrev equivSmall :
    LightCondensed.{u} C ≌
      Sheaf ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
        (coherentTopology LightProfinite.{u})) C :=
  (equivSmallModel LightProfinite).sheafCongr _ _ _
/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : LightCondensed.{u} C) : Small.{max u v} (X ⟶ Y) where
  equiv_small :=
    ⟨(equivSmall C).functor.obj X ⟶ (equivSmall C).functor.obj Y,
      ⟨(equivSmall C).fullyFaithfulFunctor.homEquiv⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Sheafifying is preserved under conjugating with the equivalence between light condensed objects
and sheaves on a small site.
-/
/-
**LightCondensed.equivSmallSheafificationIso** 是 Mathlib 中的一个定义，位于命名空间 `LightCon
densed`。
形式化陈述：equivSmallSheafificationIso [HasWeakSheafify (coherentTopology LightProfin
ite.{u}) C] [HasWeakSheafify ((equivSmallModel.{u} LightProfinite.{u}).inverse.i
nducedTopology (coherentTopology LightProfinite.{u})) C] : (equivSmallModel Ligh
tProfinite.{u}).op.congrLeft.inverse ⋙ presheafToSheaf _ _ ⋙ (equivSmall C).func
tor ≅ presheafToSheaf _ _
参数：coherentTopology LightProfinite.{u}；(equivSmallModel.{u} LightProfinite.{u}).
inverse.inducedTopology (coherentTopology LightProfinite.{u})。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instEssentiallySmallLightProfinite`：CategoryTheory.EssentiallySmall.{u, 
u, u + 1} LightProfinite
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Sheafifying is preserved under conjugating with the equivalence between light co
ndensed objects
and sheaves on a small site.
-/
noncomputable def equivSmallSheafificationIso
    [HasWeakSheafify (coherentTopology LightProfinite.{u}) C]
    [HasWeakSheafify ((equivSmallModel.{u} LightProfinite.{u}).inverse.inducedTopology
      (coherentTopology LightProfinite.{u})) C] :
    (equivSmallModel LightProfinite.{u}).op.congrLeft.inverse ⋙ presheafToSheaf _ _ ⋙
      (equivSmall C).functor ≅
    presheafToSheaf _ _ :=
  (conjugateIsoEquiv (sheafificationAdjunction _ _)
    (((equivSmallModel LightProfinite.{u}).op.congrLeft.symm.toAdjunction.comp
    (sheafificationAdjunction _ _)).comp (equivSmall C).toAdjunction)).symm <|
  NatIso.ofComponents (fun X ↦ ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm)

variable (R : Type u) [CommRing R]

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] LightCondensed.forget in
set_option backward.isDefEq.respectTransparency false in
/--
Taking the free condensed module is preserved under conjugating with the equivalence between
light condensed objects and sheaves on a small site.
-/
/-
**LightCondensed.equivSmallFreeIso** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：equivSmallFreeIso : (equivSmall (Type u)).inverse ⋙ free R ⋙ (equivSmall (
ModuleCat R)).functor ≅ Sheaf.composeAndSheafify _ (ModuleCat.free R)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instEssentiallySmallLightProfinite`：CategoryTheory.EssentiallySmall.{u, 
u, u + 1} LightProfinite
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Taking the free condensed module is preserved under conjugating with the equival
ence between
light condensed objects and sheaves on a small site.
-/
noncomputable def equivSmallFreeIso :
    (equivSmall (Type u)).inverse ⋙ free R ⋙ (equivSmall (ModuleCat R)).functor ≅
    Sheaf.composeAndSheafify _ (ModuleCat.free R) :=
  conjugateIsoEquiv (Sheaf.adjunction _ (ModuleCat.adj R))
    (((equivSmall _).symm.toAdjunction.comp
      (freeForgetAdjunction R)).comp (equivSmall _).toAdjunction) |>.symm <| by
  refine NatIso.ofComponents
    (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (isoWhiskerRight ((equivSmallModel LightProfinite).op.invFunIdAssoc _).symm _ ≪≫
        (Functor.associator _ _ _)))

end LightCondensed

