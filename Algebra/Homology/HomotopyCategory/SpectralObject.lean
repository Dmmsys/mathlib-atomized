/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.SpectralObject

/-!
# The spectral object with values in the homotopy category

Let `C` be an additive category. In this file, we show that the
mapping cone defines a spectral object with values in the homotopy
category of `ℤ`-indexed cochain complexes `C` that is indexed
by the category `CochainComplex C ℤ`.
(It follows that to any functor `ι ⥤ CochainComplex C ℤ` (e.g. a filtered
complex), there is an associated spectral object indexed by `ι`.)

-/

@[expose] public section

namespace HomotopyCategory

open CategoryTheory Limits Triangulated CochainComplex.mappingCone

variable (C : Type*) [Category* C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The functor `ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ` which
sends a morphism of cochain complexes to its mapping cone. -/
@[simps]
/-
**HomotopyCategory.composableArrowsFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCa
tegory`。
形式化陈述：composableArrowsFunctor : ComposableArrows (CochainComplex C Int) 1 ⥤ Coch
ainComplex C Int where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ` which
sends a morphism of cochain complexes to its mapping cone.
-/
noncomputable def composableArrowsFunctor :
    ComposableArrows (CochainComplex C ℤ) 1 ⥤ CochainComplex C ℤ where
  obj f := CochainComplex.mappingCone (f.map' 0 1)
  map φ := map _ _ (φ.app 0) (φ.app 1) (ComposableArrows.naturality' φ 0 1)
  map_id _ := map_id _
  map_comp _ _ := map_comp _ _ _ _ _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The spectral object with values in `(HomotopyCategory C (.up ℤ)` that
is indexed by `CochainComplex C ℤ`. -/
@[simps]
/-
**HomotopyCategory.spectralObjectMappingCone** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy
Category`。
形式化陈述：spectralObjectMappingCone : SpectralObject (HomotopyCategory C (ComplexSha
pe.up Int)) (CochainComplex C Int) where ω₁
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopyCategory.instAdditiveIntUpShiftFunctor`：∀ (C : Type u) [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (n : ℤ)
,   (CategoryTheory.shiftFunctor (Ho…

--- 原说明 ---
The spectral object with values in `(HomotopyCategory C (.up ℤ)` that
is indexed by `CochainComplex C ℤ`.
-/
noncomputable def spectralObjectMappingCone :
    SpectralObject (HomotopyCategory C (ComplexShape.up ℤ)) (CochainComplex C ℤ) where
  ω₁ := composableArrowsFunctor C ⋙ HomotopyCategory.quotient _ _
  δ'.app D := ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (CochainComplex.mappingConeCompTriangle (D.map' 0 1) (D.map' 1 2))).mor₃
  δ'.naturality D₁ D₂ φ := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D₁
    obtain ⟨_, _, _, f', g', rfl⟩ := ComposableArrows.mk₂_surjective D₂
    have eq := CochainComplex.mappingConeCompTriangle_mor₃_naturality f g f' g' φ
    dsimp [ComposableArrows.Precomp.map] at eq ⊢
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    simp [eq]
  distinguished' D := by
    obtain ⟨_, _, _, f, g, rfl⟩ := ComposableArrows.mk₂_surjective D
    exact HomotopyCategory.mappingConeCompTriangleh_distinguished f g

end HomotopyCategory

