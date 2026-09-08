/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.Algebra.Homology.SingleHomology

/-! # The fully faithful embedding of the abelian category in its derived category

In this file, we show that for any `n : ℤ`, the functor
`singleFunctor C n : C ⥤ DerivedCategory C` is fully faithful.

-/

@[expose] public section

universe w v u

open CategoryTheory

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The canonical isomorphism
`DerivedCategory.singleFunctor C n ⋙ DerivedCategory.homologyFunctor C n ≅ 𝟭 C` -/
/-
**DerivedCategory.singleFunctorCompHomologyFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 
`DerivedCategory`。
形式化陈述：singleFunctorCompHomologyFunctorIso (n : Int) : singleFunctor C n ⋙ homolo
gyFunctor C n ≅ 𝟭 C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The canonical isomorphism
`DerivedCategory.singleFunctor C n ⋙ DerivedCategory.homologyFunctor C n ≅ 𝟭 C`
-/
noncomputable def singleFunctorCompHomologyFunctorIso (n : ℤ) :
    singleFunctor C n ⋙ homologyFunctor C n ≅ 𝟭 C :=
  Functor.isoWhiskerRight ((SingleFunctors.evaluation _ _ n).mapIso
    (singleFunctorsPostcompQIso C)) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (homologyFunctorFactors C n) ≪≫
      (HomologicalComplex.homologyFunctorSingleIso _ _ _)
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Faithful where
  map_injective {_ _ f₁ f₂} h := by
    have eq₁ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f₁
    have eq₂ := NatIso.naturality_1 (singleFunctorCompHomologyFunctorIso C n) f₂
    dsimp at eq₁ eq₂
    rw [← eq₁, ← eq₂, h]

set_option backward.isDefEq.respectTransparency false in
/-
**DerivedCategory.** 是 Mathlib 中的一个实例，位于命名空间 `DerivedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Full where
  map_surjective {A B} f := by
    change Q.obj ((CochainComplex.singleFunctor C n).obj A) ⟶
      Q.obj ((CochainComplex.singleFunctor C n).obj B) at f
    suffices ∃ f', f = Q.map f' by
      obtain ⟨f', rfl⟩ := this
      obtain ⟨g, rfl⟩ := (CochainComplex.singleFunctor C n).map_surjective f'
      exact ⟨g, rfl⟩
    obtain ⟨X, _, _, s, _, g, rfl⟩ := right_fac_of_isStrictlyLE_of_isStrictlyGE n n f
    obtain ⟨A₀, ⟨e⟩⟩ := X.exists_iso_single n
    have ⟨φ, hφ⟩ := (CochainComplex.singleFunctor C n).map_surjective (e.inv ≫ s)
    have : IsIso ((singleFunctor C n).map φ) := by
      change IsIso (Q.map ((CochainComplex.singleFunctor C n).map φ))
      rw [hφ, Functor.map_comp]
      infer_instance
    have : IsIso φ := (NatIso.isIso_map_iff (singleFunctorCompHomologyFunctorIso C n) φ).1
        (by dsimp; infer_instance)
    have : IsIso (e.inv ≫ s) := by rw [← hφ]; infer_instance
    have : IsIso s := IsIso.of_isIso_comp_left e.inv s
    exact ⟨inv s ≫ g, by simp⟩

end DerivedCategory

