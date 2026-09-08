/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Change of sheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R`
attached to a morphism of sheaves of rings `α : R ⟶ R'`.

-/

@[expose] public section

universe v v' u u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace SheafOfModules

variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- The restriction of scalars functor `SheafOfModules R' ⥤ SheafOfModules R`
induced by a morphism of sheaves of rings `R ⟶ R'`. -/
@[simps]
/-
**SheafOfModules.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：restrictScalars : SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R where obj M
'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.isSheaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.
{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C}   {R : CategoryTheory.Sh
eaf J RingCa…

--- 原说明 ---
The restriction of scalars functor `SheafOfModules R' ⥤ SheafOfModules R`
induced by a morphism of sheaves of rings `R ⟶ R'`.
-/
noncomputable def restrictScalars :
    SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R where
  obj M' :=
    { val := (PresheafOfModules.restrictScalars α.hom).obj M'.val
      isSheaf := M'.isSheaf }
  map φ := { val := (PresheafOfModules.restrictScalars α.hom).map φ.val }
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (restrictScalars.{v} α).Additive where

end SheafOfModules

namespace PresheafOfModules

variable {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {M₁ M₂ : PresheafOfModules.{v} R'}

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `PresheafOfModules.restrictScalars α` induces bijections on
morphisms if `α` is locally surjective and the target presheaf is a sheaf. -/
/-
**PresheafOfModules.restrictHomEquivOfIsLocallySurjective** 是 Mathlib 中的一个定义，位于命
名空间 `PresheafOfModules`。
形式化陈述：restrictHomEquivOfIsLocallySurjective (hM₂ : Presheaf.IsSheaf J M₂.preshea
f) [Presheaf.IsLocallySurjective J α] : (M₁ ⟶ M₂) ≃ ((restrictScalars α).obj M₁ 
⟶ (restrictScalars α).obj M₂) where toFun f
参数：hM₂ : Presheaf.IsSheaf J M₂.presheaf。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `PresheafOfModules.restrictScalars α` induces bijections on
morphisms if `α` is locally surjective and the target presheaf is a sheaf.
-/
noncomputable def restrictHomEquivOfIsLocallySurjective
    (hM₂ : Presheaf.IsSheaf J M₂.presheaf) [Presheaf.IsLocallySurjective J α] :
    (M₁ ⟶ M₂) ≃ ((restrictScalars α).obj M₁ ⟶ (restrictScalars α).obj M₂) where
  toFun f := (restrictScalars α).map f
  invFun g := homMk ((toPresheaf R).map g) (fun X r' m ↦ by
    apply hM₂.isSeparated _ _ (Presheaf.imageSieve_mem J α r')
    rintro Y p ⟨r : R.obj _, hr⟩
    have hg : ∀ (z : M₁.obj X), g.app _ (M₁.map p.op z) = M₂.map p.op (g.app X z) :=
      fun z ↦ CategoryTheory.congr_fun (g.naturality p.op) z
    change M₂.map p.op (g.app X (r' • m)) = M₂.map p.op (r' • show M₂.obj X from g.app X m)
    dsimp at hg ⊢
    rw [← hg, M₂.map_smul, ← hg, ← hr]
    erw [← (g.app _).hom.map_smul]
    rw [M₁.map_smul, ← hr]
    rfl)

end PresheafOfModules

