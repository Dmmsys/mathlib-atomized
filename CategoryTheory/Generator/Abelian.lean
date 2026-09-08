/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Generator.Preadditive
public import Mathlib.CategoryTheory.Abelian.Opposite

/-!
# A complete abelian category with enough injectives and a separator has an injective coseparator

## Future work
* Once we know that Grothendieck categories have enough injectives, we can use this to conclude
  that Grothendieck categories have an injective coseparator.

## References
* [Peter J Freyd, *Abelian Categories* (Theorem 3.37)][freyd1964abelian]

-/

public section


open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-
**CategoryTheory.Abelian.has_injective_coseparator** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Abelian`。
形式化陈述：has_injective_coseparator [HasLimits C] [EnoughInjectives C] (G : C) (hG :
 IsSeparator G) : exists G : C, Injective G ∧ IsCoseparator G
参数：G : C；hG : IsSeparator G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.locallySmall_of_univLE`：∀ (C : Type u) [inst : CategoryTh
eory.Category.{v, u} C] [UnivLE.{v, w}], CategoryTheory.LocallySmall.{w, v, u} C
· 使用定理 `CategoryTheory.wellPowered_of_isDetector`：wellPowered_of_isDetector [Has
Pullbacks C] (G : C) (hG : IsDetector G) : WellPowered.{v₁} C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.IsSeparator.isDetector`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [CategoryTheory.Balanced C] {G : C},   CategoryTheory
.IsSeparator G → CategoryTh…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_small`：hasProductsOfShape_of
_small (β : Type w₂) [Small.{w₁} β] [HasProducts.{w₁} C] : HasProductsOfShape β 
C
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.Limits.hasProductsOfShape_of_hasProducts`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasProducts C] 
(J : Type w),   CategoryTheory.Limits.HasProd…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Preadditive.isCoseparator_iff`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (G : C), 
  CategoryTheory.IsCoseparator G ↔…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Preadditive.isSeparator_iff`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] (G : C),   
CategoryTheory.IsSeparator G ↔  …
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.op_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {A B : C} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryTheor
y.Mono f.op
· 使用定理 `CategoryTheory.Limits.instEpiFactorThruImageOfHasLimitWalkingParallelPai
rParallelPair`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C
} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasImage f]   [∀ {Z : C} (g…
· 使用定理 `CategoryTheory.Abelian.hasEqualizers`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasEq
ualizers C
· 使用定理 `CategoryTheory.Limits.zero_of_comp_mono`：zero_of_comp_mono {X Y Z : C} {
f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
（共 41 条，此处仅展示前 30 条）
-/
theorem has_injective_coseparator [HasLimits C] [EnoughInjectives C] (G : C) (hG : IsSeparator G) :
    ∃ G : C, Injective G ∧ IsCoseparator G := by
  have : WellPowered.{v} C := wellPowered_of_isDetector G hG.isDetector
  have : HasProductsOfShape (Subobject (op G)) C := hasProductsOfShape_of_small.{v} _ _
  let T : C := Injective.under (piObj fun P : Subobject (op G) => unop P)
  refine ⟨T, inferInstance, (Preadditive.isCoseparator_iff _).2 fun X Y f hf => ?_⟩
  refine (Preadditive.isSeparator_iff _).1 hG _ fun h => ?_
  suffices hh : factorThruImage (h ≫ f) = 0 by
    rw [← Limits.image.fac (h ≫ f), hh, zero_comp]
  let R := Subobject.mk (factorThruImage (h ≫ f)).op
  let q₁ : image (h ≫ f) ⟶ unop R :=
    (Subobject.underlyingIso (factorThruImage (h ≫ f)).op).unop.hom
  let q₂ : unop (R : Cᵒᵖ) ⟶ piObj fun P : Subobject (op G) => unop P :=
    section_ (Pi.π (fun P : Subobject (op G) => (unop P : C)) R)
  let q : image (h ≫ f) ⟶ T := q₁ ≫ q₂ ≫ Injective.ι _
  exact zero_of_comp_mono q
    (by rw [← Injective.comp_factorThru q (Limits.image.ι (h ≫ f)), Limits.image.fac_assoc,
      Category.assoc, hf, comp_zero])
/-
**CategoryTheory.Abelian.has_projective_separator** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Abelian`。
形式化陈述：has_projective_separator [HasColimits C] [EnoughProjectives C] (G : C) (hG
 : IsCoseparator G) : exists G : C, Projective G ∧ IsSeparator G
参数：G : C；hG : IsCoseparator G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.has_injective_coseparator`：has_injective_cosepara
tor [HasLimits C] [EnoughInjectives C] (G : C) (hG : IsSeparator G) : exists G :
 C, Injective G ∧ IsCoseparator G
· 使用定理 `CategoryTheory.Injective.instEnoughInjectivesOppositeOfEnoughProjectives
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.En
oughProjectives C],   CategoryTheory.EnoughInjectives Cᵒᵖ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isSeparator_op_iff`：isSeparator_op_iff (G : C) : IsSepara
tor (op G) ↔ IsCoseparator G
· 使用定理 `CategoryTheory.Injective.instProjectiveUnopOfOpposite`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {J : Cᵒᵖ} [CategoryTheory.Injective J
],   CategoryTheory.Projective (Opposite.un…
· 使用定理 `CategoryTheory.isSeparator_unop_iff`：isSeparator_unop_iff (G : Cᵒᵖ) : Is
Separator (unop G) ↔ IsCoseparator G
-/
theorem has_projective_separator [HasColimits C] [EnoughProjectives C] (G : C)
    (hG : IsCoseparator G) : ∃ G : C, Projective G ∧ IsSeparator G := by
  obtain ⟨T, hT₁, hT₂⟩ := has_injective_coseparator (op G) ((isSeparator_op_iff _).2 hG)
  exact ⟨unop T, inferInstance, (isSeparator_unop_iff _).2 hT₂⟩

end CategoryTheory.Abelian

