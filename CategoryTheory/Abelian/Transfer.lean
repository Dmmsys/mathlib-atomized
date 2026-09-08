/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages
public import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# Transferring "abelian-ness" across a functor

If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (both preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.

A particular example is the transfer of `Abelian` instances from a category `C` to `ShrinkHoms C`;
see `ShrinkHoms.abelian`. In this case, we also transfer the `Preadditive` structure.

See <https://stacks.math.columbia.edu/tag/03A3>

## Notes
The hypotheses, following the statement from the Stacks project,
may appear surprising: we don't ask that the counit of the adjunction is an isomorphism,
but just that we have some potentially unrelated isomorphism `i : F ⋙ G ≅ 𝟭 C`.

However Lemma A1.1.1 from [Elephant] shows that in this situation the counit itself
must be an isomorphism, and thus that `C` is a reflective subcategory of `D`.

Someone may like to formalize that lemma, and restate this theorem in terms of `Reflective`.
(That lemma has a nice string diagrammatic proof that holds in any bicategory.)
-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open Limits

universe v₁ v₂ u₁ u₂

namespace AbelianOfAdjunction

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D)
variable (G : D ⥤ C) [Functor.PreservesZeroMorphisms G]

set_option backward.isDefEq.respectTransparency false in
/-- No point making this an instance, as it requires `i`. -/
/-
**CategoryTheory.AbelianOfAdjunction.hasKernels** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.AbelianOfAdjunction`。
形式化陈述：hasKernels [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C) : HasKernels C
参数：i : F ⋙ G ≅ 𝟭 C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.instHasKernelMapOfPreservesLimitWalkingParallelPai
rParallelPairOfNatHom`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 :
 Ca…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.Functor.instIsSplitMonoApp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…

--- 原说明 ---
No point making this an instance, as it requires `i`.
-/
theorem hasKernels [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C) : HasKernels C :=
  { has_limit {X Y} f := by
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasKernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasKernel_comp_mono _ _
      apply Limits.hasKernel_iso_comp }

set_option backward.isDefEq.respectTransparency false in
/-- No point making this an instance, as it requires `i` and `adj`. -/
/-
**CategoryTheory.AbelianOfAdjunction.hasCokernels** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.AbelianOfAdjunction`。
形式化陈述：hasCokernels (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : HasCokernels C
参数：i : F ⋙ G ≅ 𝟭 C；adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`：leftAdjoint_pre
servesColimits : PreservesColimitsOfSize.{v, u} F where preservesColimitsOfShape
· 使用定理 `CategoryTheory.NatIso.naturality_1`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.instHasCokernelMapOfPreservesColimitWalkingParalle
lPairParallelPairOfNatHom`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, 
u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst
_2 : Ca…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…

--- 原说明 ---
No point making this an instance, as it requires `i` and `adj`.
-/
theorem hasCokernels (i : F ⋙ G ≅ 𝟭 C) (adj : G ⊣ F) : HasCokernels C :=
  { has_colimit {X Y} f := by
      have : PreservesColimits G := adj.leftAdjoint_preservesColimits
      have : i.inv.app X ≫ G.map (F.map f) ≫ i.hom.app Y = f := by
        simpa using NatIso.naturality_1 i f
      rw [← this]
      have : HasCokernel (G.map (F.map f) ≫ i.hom.app _) := Limits.hasCokernel_comp_iso _ _
      apply Limits.hasCokernel_epi_comp }

end AbelianOfAdjunction

open AbelianOfAdjunction

/-- If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (with `G` preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian. -/
@[stacks 03A3, instance_reducible]
/-
**CategoryTheory.abelianOfAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：abelianOfAdjunction {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFi
niteProducts C] {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) (G : D ⥤
 C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 
C) (adj : G ⊣ F) : Abelian C
参数：F : C ⥤ D；G : D ⥤ C；i : F ⋙ G ≅ 𝟭 C；adj : G ⊣ F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.AbelianOfAdjunction.hasKernels`：hasKernels [PreservesFini
teLimits G] (i : F ⋙ G ≅ 𝟭 C) : HasKernels C
· 使用定理 `CategoryTheory.AbelianOfAdjunction.hasCokernels`：hasCokernels (i : F ⋙ G
 ≅ 𝟭 C) (adj : G ⊣ F) : HasCokernels C

--- 原说明 ---
If `C` is an additive category, `D` is an abelian category,
we have `F : C ⥤ D` `G : D ⥤ C` (with `G` preserving zero morphisms),
`G` is left exact (that is, preserves finite limits),
and further we have `adj : G ⊣ F` and `i : F ⋙ G ≅ 𝟭 C`,
then `C` is also abelian.
-/
def abelianOfAdjunction {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    (G : D ⥤ C) [Functor.PreservesZeroMorphisms G] [PreservesFiniteLimits G] (i : F ⋙ G ≅ 𝟭 C)
    (adj : G ⊣ F) : Abelian C := by
  haveI := hasKernels F G i
  haveI := hasCokernels F G i adj
  have : ∀ {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    let arrowIso : Arrow.mk (G.map (F.map f)) ≅ Arrow.mk f :=
      ((Functor.mapArrowFunctor _ _).mapIso i).app (Arrow.mk f)
    have : PreservesColimits G := adj.leftAdjoint_preservesColimits
    let iso : Arrow.mk (G.map (Abelian.coimageImageComparison (F.map f))) ≅
        Arrow.mk (Abelian.coimageImageComparison f) :=
      Abelian.PreservesCoimageImageComparison.iso G (F.map f) ≪≫
        Abelian.coimageImageComparisonFunctor.mapIso arrowIso
    rw [Arrow.isIso_iff_isIso_of_isIso iso.inv]
    infer_instance
  apply Abelian.ofCoimageImageComparisonIsIso

/-- If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
@[instance_reducible]
/-
**CategoryTheory.abelianOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：abelianOfEquivalence {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasF
initeProducts C] {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D) [F.IsEq
uivalence] : Abelian C
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is an additive category equivalent to an abelian category `D`
via a functor that preserves zero morphisms,
then `C` is also abelian.
-/
def abelianOfEquivalence {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteProducts C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (F : C ⥤ D)
    [F.IsEquivalence] : Abelian C :=
  abelianOfAdjunction F F.inv F.asEquivalence.unitIso.symm F.asEquivalence.symm.toAdjunction

namespace ShrinkHoms

universe w

variable {C : Type*} [Category* C] [LocallySmall.{w} C]

section Preadditive

variable [Preadditive C]

variable (C)

/-
**CategoryTheory.ShrinkHoms.preadditive** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.ShrinkHoms`。
形式化陈述：preadditive : Preadditive.{w} (ShrinkHoms C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preadditive : Preadditive.{w} (ShrinkHoms C) :=
  .ofFullyFaithful (equivalence C).fullyFaithfulInverse
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (inverse C).Additive :=
  (equivalence C).symm.fullyFaithfulFunctor.additive_ofFullyFaithful
/-
**CategoryTheory.ShrinkHoms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShrinkHom
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (functor C).Additive :=
  (equivalence C).symm.additive_inverse_of_FullyFaithful
/-
**CategoryTheory.ShrinkHoms.hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.ShrinkHoms`。
形式化陈述：hasLimitsOfShape (J : Type*) [Category* J] [HasLimitsOfShape J C] : HasLim
itsOfShape.{_, _, w} J (ShrinkHoms C)
参数：J : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`：hasLimitsOfSh
ape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] : HasLim
itsOfShape J D
· 使用定理 `CategoryTheory.ShrinkHoms.instIsEquivalenceInverse`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.LocallySmall.{w, v
, u} C],   (CategoryTheory.ShrinkHoms.in…
-/
instance hasLimitsOfShape (J : Type*) [Category* J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, w} J (ShrinkHoms C) :=
  Adjunction.hasLimitsOfShape_of_equivalence (inverse C)
/-
**CategoryTheory.ShrinkHoms.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.ShrinkHoms`。
形式化陈述：hasFiniteLimits [HasFiniteLimits C] : HasFiniteLimits.{w} (ShrinkHoms C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits.{w} (ShrinkHoms C) := ⟨fun _ => inferInstance⟩

end Preadditive

variable (C) in
/-
**CategoryTheory.ShrinkHoms.abelian** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sh
rinkHoms`。
形式化陈述：abelian [Abelian C] : Abelian.{w} (ShrinkHoms C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShrinkHoms.instIsEquivalenceInverse`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.LocallySmall.{w, v
, u} C],   (CategoryTheory.ShrinkHoms.in…
-/
noncomputable instance abelian [Abelian C] :
    Abelian.{w} (ShrinkHoms C) := abelianOfEquivalence (inverse C)

end ShrinkHoms


namespace AsSmall

universe w v u

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C]

variable (C)

/-
**CategoryTheory.AsSmall.preadditive** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.A
sSmall`。
形式化陈述：preadditive : Preadditive (AsSmall.{w} C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance preadditive : Preadditive (AsSmall.{w} C) :=
  .ofFullyFaithful equiv.fullyFaithfulInverse
/-
**CategoryTheory.AsSmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.AsSmall`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (down (C := C)).Additive :=
  equiv.symm.fullyFaithfulFunctor.additive_ofFullyFaithful
/-
**CategoryTheory.AsSmall.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.AsSmall`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (up (C := C)).Additive :=
  equiv.symm.additive_inverse_of_FullyFaithful
/-
**CategoryTheory.AsSmall.hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.AsSmall`。
形式化陈述：hasLimitsOfShape (J : Type*) [Category* J] [HasLimitsOfShape J C] : HasLim
itsOfShape.{_, _, max u v w} J (AsSmall.{w} C)
参数：J : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`：hasLimitsOfSh
ape_of_equivalence (E : D ⥤ C) [E.IsEquivalence] [HasLimitsOfShape J C] : HasLim
itsOfShape J D
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
-/
instance hasLimitsOfShape (J : Type*) [Category* J]
    [HasLimitsOfShape J C] : HasLimitsOfShape.{_, _, max u v w} J (AsSmall.{w} C) :=
  Adjunction.hasLimitsOfShape_of_equivalence equiv.inverse
/-
**CategoryTheory.AsSmall.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.AsSmall`。
形式化陈述：hasFiniteLimits [HasFiniteLimits C] : HasFiniteLimits (AsSmall.{w} C)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
instance hasFiniteLimits [HasFiniteLimits C] :
    HasFiniteLimits (AsSmall.{w} C) := ⟨fun _ => inferInstance⟩

end Preadditive

variable (C) in
/-
**CategoryTheory.AsSmall.abelian** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.AsSma
ll`。
形式化陈述：abelian [Abelian C] : Abelian (AsSmall.{w} C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance abelian [Abelian C] :
    Abelian (AsSmall.{w} C) := abelianOfEquivalence equiv.inverse

end AsSmall

end CategoryTheory

