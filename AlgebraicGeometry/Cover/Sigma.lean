/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Collapsing covers

We define the endofunctor on `Scheme.Cover P` that collapses a cover to a single object cover.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {P : MorphismProperty Scheme.{u}} {S : Scheme.{u}} [IsZariskiLocalAtSource P]
  [UnivLE.{v, u}]

set_option backward.isDefEq.respectTransparency false in
/-- If `𝒰` is a cover of `S`, this is the single object cover where the covering
object is the disjoint union. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.sigma** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Cover`。
形式化陈述：sigma (𝒰 : Cover.{v} (precoverage P) S) : S.Cover (precoverage P) where I₀
参数：𝒰 : Cover.{v} (precoverage P) S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝒰` is a cover of `S`, this is the single object cover where the covering
object is the disjoint union.
-/
noncomputable def sigma (𝒰 : Cover.{v} (precoverage P) S) : S.Cover (precoverage P) where
  I₀ := PUnit.{v + 1}
  X _ := ∐ 𝒰.X
  f _ := Sigma.desc 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun s ↦ ?_, fun _ ↦ IsZariskiLocalAtSource.sigmaDesc 𝒰.map_prop⟩
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq s
    refine ⟨default, Sigma.ι 𝒰.X i y, by simp [← Scheme.Hom.comp_apply]⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.Cover.presieve** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma presieve₀_sigma {S : Scheme.{u}} (𝒰 : Cover.{v} (precoverage P) S) :
    𝒰.sigma.presieve₀ = Presieve.singleton (Sigma.desc 𝒰.f) := by
  refine le_antisymm ?_ fun T g ⟨⟩ ↦ ⟨⟨⟩⟩
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact Presieve.singleton_self _

variable [P.IsMultiplicative] {𝒰 𝒱 : Scheme.Cover.{v} (precoverage P) S}

variable (𝒰) in
/-
**AlgebraicGeometry.Scheme.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique 𝒰.sigma.I₀ := inferInstanceAs <| Unique PUnit.{v + 1}

set_option backward.isDefEq.respectTransparency false in
/-- `𝒰` refines the single object cover defined by `𝒰`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.toSigma** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme.Cover`。
形式化陈述：toSigma (𝒰 : Cover.{v} (precoverage P) S) : 𝒰 ⟶ 𝒰.sigma where s₀ _
参数：𝒰 : Cover.{v} (precoverage P) S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`𝒰` refines the single object cover defined by `𝒰`.
-/
noncomputable def toSigma (𝒰 : Cover.{v} (precoverage P) S) : 𝒰 ⟶ 𝒰.sigma where
  s₀ _ := default
  h₀ i := Sigma.ι _ i

set_option backward.isDefEq.respectTransparency false in
/-- A refinement of coverings induces a refinement on the single object coverings. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.Hom.sigma** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.Cover.Hom`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {S : Al
gebraicGeometry.Scheme} →     [inst : AlgebraicGeometry.IsZariskiLocalAtSource P
] →       [inst_1 : UnivLE.{v, u}] →         {𝒰 𝒱 : AlgebraicGeometry.Scheme.Cov
er (AlgebraicGeometry.Scheme.precoverage P) S} →           (𝒰 ⟶ 𝒱) → (𝒰.sigma ⟶ 
𝒱.sigma)
参数：AlgebraicGeometry.Scheme.precoverage P；𝒰 ⟶ 𝒱；𝒰.sigma ⟶ 𝒱.sigma。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A refinement of coverings induces a refinement on the single object coverings.
-/
noncomputable def Hom.sigma (f : 𝒰 ⟶ 𝒱) : 𝒰.sigma ⟶ 𝒱.sigma where
  s₀ _ := default
  h₀ _ := Sigma.desc fun j ↦ f.h₀ j ≫ Sigma.ι _ (f.s₀ j)
  w₀ _ := Sigma.hom_ext _ _ (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Collapsing a cover to a single object cover is functorial. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.sigmaFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.Cover`。
形式化陈述：sigmaFunctor : S.Cover (precoverage P) ⥤ S.Cover (precoverage P) where obj
 𝒰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Collapsing a cover to a single object cover is functorial.
-/
noncomputable def sigmaFunctor : S.Cover (precoverage P) ⥤ S.Cover (precoverage P) where
  obj 𝒰 := 𝒰.sigma
  map f := Scheme.Cover.Hom.sigma f
  map_id 𝒰 := PreZeroHypercover.Hom.ext rfl <| by
    simp only [sigma_I₀, sigma_X, heq_eq_eq]
    ext j : 1
    exact Sigma.hom_ext _ _ (by simp)
  map_comp f g := PreZeroHypercover.Hom.ext rfl <| by
    simp only [sigma_I₀, sigma_X, heq_eq_eq]
    ext j : 1
    exact Sigma.hom_ext _ _ (by simp)

end AlgebraicGeometry.Scheme.Cover

