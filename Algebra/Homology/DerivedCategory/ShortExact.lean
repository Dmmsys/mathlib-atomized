/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The distinguished triangle attached to a short exact sequence of cochain complexes

Given a short exact short complex `S` in the category `CochainComplex C ℤ`,
we construct a distinguished triangle
`Q.obj S.X₁ ⟶ Q.obj S.X₂ ⟶ Q.obj S.X₃ ⟶ (Q.obj S.X₃)⟦1⟧`
in the derived category of `C`.
(See `triangleOfSES` and `triangleOfSES_distinguished`.)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w v u

open CategoryTheory Category Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

/-- The connecting homomorphism `Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧`
in the derived category when `S` is a short exact short complex of
cochain complexes in an abelian category. -/
/-
**DerivedCategory.triangleOfSES** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：triangleOfSES : Triangle (DerivedCategory C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism `Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧`
in the derived category when `S` is a short exact short complex of
cochain complexes in an abelian category.
-/
noncomputable def triangleOfSESδ :
    Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  inv (Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
    (Q.commShiftIso (1 : ℤ)).hom.app S.X₁

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**DerivedCategory.descShortComplex_triangleOfSES** 是 Mathlib 中的一个引理，位于命名空间 `Deri
vedCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma descShortComplex_triangleOfSESδ :
    dsimp% Q.map (CochainComplex.mappingCone.descShortComplex S) ≫ triangleOfSESδ hS =
    Q.map (CochainComplex.mappingCone.triangle S.f).mor₃ ≫
      (Functor.commShiftIso Q 1).hom.app S.X₁ := by
  simp [triangleOfSESδ]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**DerivedCategory.triangleOfSES** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：triangleOfSES : Triangle (DerivedCategory C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triangleOfSESδ_naturality {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    triangleOfSESδ hS₁ ≫ (Q.map f.τ₁)⟦1⟧' = Q.map f.τ₃ ≫ triangleOfSESδ hS₂ := by
  simp only [triangleOfSESδ, Category.assoc,
    IsIso.inv_comp_eq]
  rw [← Functor.comp_map, ← (Q.commShiftIso (1 : ℤ)).hom.naturality, ← Category.assoc,
    ← Category.assoc, ← Category.assoc, ← Category.assoc, ← Iso.app_hom,
    Iso.cancel_iso_hom_right, ← Q.map_comp]
  simp only [Functor.comp_map, ← CochainComplex.mappingCone.descShortComplex_naturality f,
    Functor.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← Q.map_comp, ← Q.map_comp]
  congr 1
  exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

/-- The distinguished triangle in the derived category associated to a short
exact sequence of cochain complexes. -/
@[simps!]
/-
**DerivedCategory.triangleOfSES** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：triangleOfSES : Triangle (DerivedCategory C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distinguished triangle in the derived category associated to a short
exact sequence of cochain complexes.
-/
noncomputable def triangleOfSES : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The triangle `triangleOfSES` attached to a short exact sequence `S` of cochain
complexes is isomorphic to the standard distinguished triangle associated to
the morphism `S.f`. -/
/-
**DerivedCategory.triangleOfSESIso** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory`。
形式化陈述：triangleOfSESIso : triangleOfSES hS ≅ Q.mapTriangle.obj (CochainComplex.ma
ppingCone.triangle S.f)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.mappingCone.quasiIso_descShortComplex`：quasiIso_descShort
Complex : QuasiIso (descShortComplex S) where quasiIsoAt n
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C

--- 原说明 ---
The triangle `triangleOfSES` attached to a short exact sequence `S` of cochain
complexes is isomorphic to the standard distinguished triangle associated to
the morphism `S.f`.
-/
noncomputable def triangleOfSESIso :
    triangleOfSES hS ≅ Q.mapTriangle.obj (CochainComplex.mappingCone.triangle S.f) := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  refine Iso.symm (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (asIso (Q.map (CochainComplex.mappingCone.descShortComplex S))) ?_ ?_ ?_)
  · dsimp [triangleOfSES]
    simp only [comp_id, id_comp]
  · dsimp
    simp only [← Q.map_comp, CochainComplex.mappingCone.inr_descShortComplex, id_comp]
  · dsimp [triangleOfSESδ]
    rw [CategoryTheory.Functor.map_id, comp_id, IsIso.hom_inv_id_assoc]
/-
**DerivedCategory.triangleOfSES_distinguished** 是 Mathlib 中的一个引理，位于命名空间 `Derived
Category`。
形式化陈述：triangleOfSES_distinguished : triangleOfSES hS in distTriang (DerivedCateg
ory C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DerivedCategory.mem_distTriang_iff`：mem_distTriang_iff (T : Triangle (De
rivedCategory C)) : (T in distTriang (DerivedCategory C)) ↔ exists (X Y : Cochai
nComplex C Int) (f : X ⟶…
-/
lemma triangleOfSES_distinguished :
    triangleOfSES hS ∈ distTriang (DerivedCategory C) := by
  rw [mem_distTriang_iff]
  exact ⟨_, _, S.f, ⟨triangleOfSESIso hS⟩⟩

section map

variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
  (f : S₁ ⟶ S₂)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
The morphism `triangleOfSES h₁ ⟶ triangleOfSES h₂` that is induced by a morphism of short
exact sequences of cochain complexes.
-/
@[simps]
/-
**DerivedCategory.triangleOfSES.map** 是 Mathlib 中的一个定义，位于命名空间 `DerivedCategory.t
riangleOfSES`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Abelian C] →       [inst_2 : HasDerivedCategory C] →         {S₁
 S₂ : CategoryTheory.ShortComplex (CochainComplex C ℤ)} →           (h₁ : S₁.Sho
rtExact) →             (h₂ : S₂.ShortExact) → (S₁ ⟶ S₂) → (DerivedCategory.trian
gleOfSES h₁ ⟶ DerivedCategory.triangleOfSES h₂)
参数：CochainComplex C ℤ；h₁ : S₁.ShortExact；h₂ : S₂.ShortExact；S₁ ⟶ S₂；DerivedCateg
ory.triangleOfSES h₁ ⟶ DerivedCategory.triangleOfSES h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `triangleOfSES h₁ ⟶ triangleOfSES h₂` that is induced by a morphism
 of short
exact sequences of cochain complexes.
-/
noncomputable def triangleOfSES.map : triangleOfSES h₁ ⟶ triangleOfSES h₂ where
  hom₁ := Q.map f.τ₁
  hom₂ := Q.map f.τ₂
  hom₃ := Q.map f.τ₃
  comm₁ := by simp [← Functor.map_comp, f.comm₁₂]
  comm₂ := by simp [← Functor.map_comp, f.comm₂₃]
  comm₃ := by
    dsimp [triangleOfSES, triangleOfSESδ]
    rw [assoc, assoc, IsIso.inv_comp_eq, ← Functor.map_comp_assoc,
      ← CochainComplex.mappingCone.map_descShortComplex,
      Functor.map_comp_assoc, IsIso.hom_inv_id_assoc,
      ← Functor.commShiftIso_hom_naturality,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    exact (CochainComplex.mappingCone.triangleMap S₁.f S₂.f f.τ₁ f.τ₂ f.comm₁₂.symm).comm₃

end map

end DerivedCategory

