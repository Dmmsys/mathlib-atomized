/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

-- these `ModuleCat` instances are only used by the `example` below, which `shake` cannot see
public import Mathlib.Algebra.Category.ModuleCat.AB  -- shake: keep
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits  -- shake: keep
public import Mathlib.AlgebraicGeometry.Sites.Affine
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf

/-!
# Affine étale site

In this file we define the small affine étale site of a scheme `S`. The underlying
category is the category of commutative rings `R` equipped with an étale structure
morphism `Spec R ⟶ S`. We show that this category is essentially small,
that it is a dense subsite of the small étale site, and that it is `1`-hypercover
dense, which allows to show that if `S : Scheme.{u}`, then we can sheafify
étale presheaves with values in `Type u`, `AddCommGrpCat.{u}`, etc.

## Main results

- `AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv`: The category of sheaves on the
  small affine étale site is equivalent to the category of schemes on the small étale site.
- `AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`: The category of
  sheaves on the étale site with values in a Grothendieck abelian category is Grothendieck abelian.
-/

@[expose] public noncomputable section

universe u v u'

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- The small affine étale site: The category of affine schemes étale over `S`, whose objects are
commutative rings `R` with an étale structure morphism `Spec R ⟶ S`. -/
/-
**AlgebraicGeometry.Scheme.AffineEtale** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：AffineEtale (S : Scheme.{u}) : Type (u + 1)
参数：S : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The small affine étale site: The category of affine schemes étale over `S`, whos
e objects are
commutative rings `R` with an étale structure morphism `Spec R ⟶ S`.
-/
def AffineEtale (S : Scheme.{u}) : Type (u + 1) :=
  MorphismProperty.CostructuredArrow @Etale.{u} ⊤ Scheme.Spec.{u} S
deriving Category, HasPullbacks

namespace AffineEtale

/-- Construct an object of the small affine étale site. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.AffineEtale.mk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.AffineEtale`。
形式化陈述：{S : AlgebraicGeometry.Scheme} →   {R : CommRingCat} → (f : AlgebraicGeome
try.Spec R ⟶ S) → [AlgebraicGeometry.Etale f] → S.AffineEtale
参数：f : AlgebraicGeometry.Spec R ⟶ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of the small affine étale site.
-/
protected def mk {R : CommRingCat.{u}} (f : Spec R ⟶ S) [Etale f] : AffineEtale S :=
  MorphismProperty.CostructuredArrow.mk ⊤ f ‹_›

/-- The `Spec` functor from the small affine étale site of `S` to the small étale site of `S`. -/
@[simps! obj_left obj_hom map_left]
/-
**AlgebraicGeometry.Scheme.AffineEtale.Spec** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.AffineEtale`。
形式化陈述：(S : AlgebraicGeometry.Scheme) → CategoryTheory.Functor S.AffineEtale S.Et
ale
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Spec` functor from the small affine étale site of `S` to the small étale si
te of `S`.
-/
protected def Spec (S : Scheme.{u}) : S.AffineEtale ⥤ S.Etale :=
  MorphismProperty.CostructuredArrow.toOver _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.AffineEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.AffineEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (AffineEtale.Spec S).Faithful :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Faithful

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.AffineEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.AffineEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (AffineEtale.Spec S).Full :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).Full

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.AffineEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.AffineEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (AffineEtale.Spec S).IsCoverDense S.smallEtaleTopology :=
  inferInstanceAs <| (MorphismProperty.CostructuredArrow.toOver _ _ _).IsCoverDense
    (S.smallGrothendieckTopology _)

variable (S) in
/-- The topology on the small affine étale site is the topology induced by `Spec` from
the small étale site. -/
/-
**AlgebraicGeometry.Scheme.AffineEtale.topology** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.AffineEtale`。
形式化陈述：topology : GrothendieckTopology S.AffineEtale
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on the small affine étale site is the topology induced by `Spec` fr
om
the small étale site.
-/
def topology : GrothendieckTopology S.AffineEtale :=
  (AffineEtale.Spec S).inducedTopology S.smallEtaleTopology
/-
**AlgebraicGeometry.Scheme.AffineEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.AffineEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.IsDenseSubsite (topology S) S.smallEtaleTopology (AffineEtale.Spec S) := by
  dsimp [topology]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.AffineEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.AffineEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor.IsOneHypercoverDense.{u} (AffineEtale.Spec S)
    (topology S) S.smallEtaleTopology :=
  isOneHypercoverDense_toOver_Spec _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.AffineEtale.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.AffineEtale`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EssentiallySmall.{u} S.AffineEtale :=
  essentiallySmall_costructuredArrow_Spec _ fun _ _ _ _ ↦ inferInstance

end AffineEtale

section

variable {A : Type u'} [Category.{u} A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)] [HasColimits A] [HasLimits A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSheafify (AffineEtale.topology S) A :=
  hasSheafifyEssentiallySmallSite.{u} _ _
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ((AffineEtale.Spec S).sheafPushforwardContinuous A
    (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSheafify S.smallEtaleTopology A :=
  Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (AffineEtale.topology S) S.smallEtaleTopology (AffineEtale.Spec S)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (AffineEtale.topology S) S.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (AffineEtale.topology S).WEqualsLocallyBijective A :=
  .ofEssentiallySmall (AffineEtale.topology S)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : S.smallEtaleTopology.WEqualsLocallyBijective A :=
  .transport  _ _ _
    (Functor.IsDenseSubsite.coverPreserving (AffineEtale.topology S) _
      (AffineEtale.Spec S))

-- The `IsGrothendieckAbelian` instances defined below would fail
-- without the next two instances
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Abelian A] : Abelian (Sheaf (AffineEtale.topology S) A) := inferInstance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Abelian A] : Abelian (Sheaf S.smallEtaleTopology A) := inferInstance

variable (S A)

/-- The category of sheaves on the small affine étale site is equivalent to the category of
sheaves on the small étale site. -/
@[simps! inverse]
/-
**AlgebraicGeometry.Scheme.AffineEtale.sheafEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.AffineEtale`。
形式化陈述：(S : AlgebraicGeometry.Scheme) →   (A : Type u') →     [inst : CategoryThe
ory.Category.{u, u'} A] →       [CategoryTheory.Limits.HasLimits A] →         Ca
tegoryTheory.Sheaf (AlgebraicGeometry.Scheme.AffineEtale.topology S) A ≌        
   CategoryTheory.Sheaf S.smallEtaleTopology A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsEquivalenceSheafEtaleSmallEtaleTopologyAf
fineEtaleTopologySheafPushforwardContinuousSpec_1`：∀ {S : AlgebraicGeometry.Sche
me} {A : Type u'} [inst : CategoryTheory.Category.{u, u'} A]   [CategoryTheory.L
imits.HasLimits A],   ((Algebra…

--- 原说明 ---
The category of sheaves on the small affine étale site is equivalent to the cate
gory of
sheaves on the small étale site.
-/
def AffineEtale.sheafEquiv : Sheaf (AffineEtale.topology S) A ≌ Sheaf S.smallEtaleTopology A :=
  ((AffineEtale.Spec S).sheafPushforwardContinuous A
      (topology S) S.smallEtaleTopology).asEquivalence.symm
/-
**AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology** 是 M
athlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isGrothendieckAbelian_sheaf_affineEtaleTopology [Abelian A] [IsGrothendiec
kAbelian.{u} A] : IsGrothendieckAbelian.{u} (Sheaf (AffineEtale.topology S) A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Sheaf.isGrothendieckAbelian_of_essentiallySmall`：isGrothe
ndieckAbelian_of_essentiallySmall {C : Type u₂} [Category.{v₂} C] [EssentiallySm
all.{v} C] (J : GrothendieckTopology C) (A : Type u₁…
· 使用定理 `AlgebraicGeometry.Scheme.AffineEtale.instEssentiallySmall`：∀ {S : Algebr
aicGeometry.Scheme}, CategoryTheory.EssentiallySmall.{u, u, u + 1} S.AffineEtale
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_has_cofiltered_limits`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.HasCo
filteredLimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.Limits.hasCofilteredLimitsOfSize_of_hasLimitsOfSize`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasL
imitsOfSize.{w', w, v, u} C],   CategoryTheory.Limits.Ha…
· 使用定理 `CategoryTheory.RepresentablyFlat.cofiltered`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instRepresentablyFlatOppositeOpOfRepresentablyCoflat`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.RepresentablyCoflat.of_isLeftAdjoint`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.hasFilteredColimitsOfSize`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Abelia
n C}   [self : CategoryTheory.IsGrothendieckAbelian.…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance isGrothendieckAbelian_sheaf_affineEtaleTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf (AffineEtale.topology S) A) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _
/-
**AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology** 是 Ma
thlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isGrothendieckAbelian_sheaf_smallEtaleTopology [Abelian A] [IsGrothendieck
Abelian.{u} A] : IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsGrothendieckAbelian.of_equivalence`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   [inst_2 : CategoryThe…
-/
instance isGrothendieckAbelian_sheaf_smallEtaleTopology
    [Abelian A] [IsGrothendieckAbelian.{u} A] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology A) :=
  IsGrothendieckAbelian.of_equivalence (AffineEtale.sheafEquiv S A)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个示例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (R : Type u) [Ring R] :
    IsGrothendieckAbelian.{u} (Sheaf S.smallEtaleTopology (ModuleCat.{u} R)) :=
  inferInstance

end

end AlgebraicGeometry.Scheme

