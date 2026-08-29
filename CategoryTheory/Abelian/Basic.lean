/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Johan Commelin, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Abelian.NonPreadditive

/-!
# Abelian categories

This file contains the definition and basic properties of abelian categories.

There are many definitions of abelian category. Our definition is as follows:
A category is called abelian if it is preadditive,
has finite products, kernels, and cokernels,
and if every monomorphism and epimorphism is normal.

It should be noted that if we also assume finite coproducts, then preadditivity is
actually a consequence of the other properties, as we show in
`Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`. However, this fact is of little practical
relevance, since essentially all interesting abelian categories come with a
preadditive structure. In this way, by requiring preadditivity, we allow the
user to pass in the "native" preadditive structure for the specific category they are
working with.

## Main definitions

* `Abelian` is the type class indicating that a category is abelian. It extends `Preadditive`.
* `Abelian.image f` is `kernel (cokernel.π f)`, and
* `Abelian.coimage f` is `cokernel (kernel.ι f)`.

## Main results

* In an abelian category, mono + epi = iso.
* If `f : X ⟶ Y`, then the map `factorThruImage f : X ⟶ image f` is an epimorphism, and the map
  `factorThruCoimage f : coimage f ⟶ Y` is a monomorphism.
* Factoring through the image and coimage is a strong epi-mono factorisation. This means that
  * every abelian category has images. We provide the isomorphism
    `imageIsoImage : abelian.image f ≅ limits.image f`.
  * the canonical morphism `coimageImageComparison : coimage f ⟶ image f`
    is an isomorphism.
* We provide the alternate characterisation of an abelian category as a category with
  (co)kernels and finite products, and in which the canonical coimage-image comparison morphism
  is always an isomorphism.
* Every epimorphism is a cokernel of its kernel. Every monomorphism is a kernel of its cokernel.
* The pullback of an epimorphism is an epimorphism. The pushout of a monomorphism is a monomorphism.
  (This is not to be confused with the fact that the pullback of a monomorphism is a monomorphism,
  which is true in any category).

## Implementation notes

The typeclass `Abelian` does not extend `NonPreadditiveAbelian`,
to avoid having to deal with comparing the two `HasZeroMorphisms` instances
(one from `Preadditive` in `Abelian`, and the other a field of `NonPreadditiveAbelian`).
As a consequence, at the beginning of this file we trivially build
a `NonPreadditiveAbelian` instance from an `Abelian` instance,
and use this to restate a number of theorems,
in each case just reusing the proof from `Mathlib/CategoryTheory/Abelian/NonPreadditive.lean`.

We don't show this yet, but abelian categories are finitely complete and finitely cocomplete.
However, the limits we can construct at this level of generality will most likely be less nice than
the ones that can be created in specific applications. For this reason, we adopt the following
convention:

* If the statement of a theorem involves limits, the existence of these limits should be made an
  explicit typeclass parameter.
* If a limit only appears in a proof, but not in the statement of a theorem, the limit should not
  be a typeclass parameter, but instead be created using `Abelian.hasPullbacks` or a similar
  definition.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
* [P. Aluffi, *Algebra: Chapter 0*][aluffi2016]

-/

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (C)

/-- A (preadditive) category `C` is called abelian if it has all finite products,
all kernels and cokernels, and if every monomorphism is the kernel of some morphism
and every epimorphism is the cokernel of some morphism.

(This definition implies the existence of zero objects:
finite products give a terminal object, and in a preadditive category
any terminal object is a zero object.)
-/
@[wikidata Q318737]
/--
Definition of `Abelian` / `Abelian` 的定义

English:
class Abelian
  parameters: extends Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C
  extends: Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C
  axioms and operations (3):
    - [has_finite_products : HasFiniteProducts C]
    - [has_kernels : HasKernels C]
    - [has_cokernels : HasCokernels C]

中文:
类 交换
  参数: extends 预加性 C, 是正规单态射范畴 C, 是正规满态射范畴 C
  继承: 预加性 C, 是正规单态射范畴 C, 是正规满态射范畴 C
  公理与运算 (3 个):
    - [has_finite_products : 有FiniteProducts C]
    - [has_kernels : 有Kernels C]
    - [has_cokernels : 有余kernels C]
-/
class Abelian extends Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C where
  [has_finite_products : HasFiniteProducts C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]

-- These instances should have a lower priority, or typeclass search times out.
attribute [instance 100] Abelian.has_finite_products
attribute [instance 100] Abelian.has_kernels Abelian.has_cokernels

end CategoryTheory

open CategoryTheory

/-!
We begin by providing an alternative constructor:
a preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category.
-/


namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [Limits.HasKernels C] [Limits.HasCokernels C]

namespace OfCoimageImageComparisonIsIso

/-- The factorisation of a morphism through its abelian image. -/
@[simps]
/--
Definition of `imageMonoFactorisation` / `imageMonoFactorisation` 的定义

English:
definition imageMonoFactorisation
  signature: {X Y : C} (f : X ⟶ Y)
  body: Abelian.image f
  m := kernel.ι _
  m_mono := inferInstance
  e := kernel.lift _ f (cokernel.condition _)
  fac := kernel.lift_ι _ _ _

中文:
定义 imageMonoFactorisation
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: Abelian.image f
  m := kernel.ι _
  m_mono := inferInstance
  e := kernel.lift _ f (cokernel.condition _)
  fac := kernel.lift_ι _ _ _

Depends on / 依赖: Abelian, Abelian.image
-/
def imageMonoFactorisation {X Y : C} (f : X ⟶ Y) : MonoFactorisation f where
  I := Abelian.image f
  m := kernel.ι _
  m_mono := inferInstance
  e := kernel.lift _ f (cokernel.condition _)
  fac := kernel.lift_ι _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
theorem `imageMonoFactorisation_e'` / 定理 `imageMonoFactorisation_e'`

English:
theorem imageMonoFactorisation_e'
  given: {X Y : C} (f : X ⟶ Y)
  proof: by
  dsimp
  ext
  simp only [Abelian.coimageImageComparison, Category.assoc,
    cokernel.π_desc_assoc]

中文:
定理 imageMonoFactorisation_e'
  条件: {X Y : C} (f : X ⟶ Y)
  证明: by
  dsimp
  ext
  simp only [Abelian.coimageImageComparison, Category.assoc,
    cokernel.π_desc_assoc]

Depends on / 依赖: Abelian, Abelian.coimageImageComparison, Category, Category.assoc, coimageImageComparison, cokernel
-/
theorem imageMonoFactorisation_e' {X Y : C} (f : X ⟶ Y) :
    (imageMonoFactorisation f).e = cokernel.π _ ≫ Abelian.coimageImageComparison f := by
  dsimp
  ext
  simp only [Abelian.coimageImageComparison, Category.assoc,
    cokernel.π_desc_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `imageFactorisation` / `imageFactorisation` 的定义

English:
definition imageFactorisation
  signature: {X Y : C} (f : X ⟶ Y) [IsIso (Abelian.coimageImageComparison f)]
  body: imageMonoFactorisation f
  isImage :=
    { lift := fun F => inv (Abelian.coimageImageComparison f) ≫ cokernel.desc _ F.e F.kernel_ι_comp
      lift_fac := fun F => by
        rw [imageMonoFactorisation_m]
        simp only [Category.assoc]
        rw [IsIso.inv_comp_eq]
        ext
        simp }

中文:
定义 imageFactorisation
  签名: {X Y : C} (f : X ⟶ Y) [是同构 (交换.coimageImageComparison f)]
  定义体: imageMonoFactorisation f
  isImage :=
    { lift := fun F => inv (Abelian.coimageImageComparison f) ≫ cokernel.desc _ F.e F.kernel_ι_comp
      lift_fac := fun F => by
        rw [imageMonoFactorisation_m]
        simp only [Category.assoc]
        rw [IsIso.inv_comp_eq]
        ext
        simp }

Depends on / 依赖: imageMonoFactorisation
-/
def imageFactorisation {X Y : C} (f : X ⟶ Y) [IsIso (Abelian.coimageImageComparison f)] :
    ImageFactorisation f where
  F := imageMonoFactorisation f
  isImage :=
    { lift := fun F => inv (Abelian.coimageImageComparison f) ≫ cokernel.desc _ F.e F.kernel_ι_comp
      lift_fac := fun F => by
        rw [imageMonoFactorisation_m]
        simp only [Category.assoc]
        rw [IsIso.inv_comp_eq]
        ext
        simp }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] {X Y
  body: by
  rw [imageMonoFactorisation_e']
  exact IsIso.comp_isIso

中文:
实例 [有ZeroObject
  签名: C] {X Y
  定义体: by
  rw [imageMonoFactorisation_e']
  exact IsIso.comp_isIso

Depends on / 依赖: IsIso.comp_isIso, comp_isIso, imageMonoFactorisation_e
-/
instance [HasZeroObject C] {X Y : C} (f : X ⟶ Y) [Mono f]
    [IsIso (Abelian.coimageImageComparison f)] : IsIso (imageMonoFactorisation f).e := by
  rw [imageMonoFactorisation_e']
  exact IsIso.comp_isIso

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasZeroObject
  signature: C] {X Y
  body: by
  dsimp
  infer_instance

中文:
实例 [有ZeroObject
  签名: C] {X Y
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: HasInitial, IsCofiltered, infer_instance, of_hasInitial
-/
instance [HasZeroObject C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsIso (imageMonoFactorisation f).m := by
  dsimp
  infer_instance

variable [forall {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f)]

/--
theorem `hasImages` / 定理 `hasImages`

English:
theorem hasImages
  statement: HasImages C
  proof: { has_image := fun {_} {_} f => { exists_image := ⟨imageFactorisation f⟩ } }

中文:
定理 hasImages
  结论: 有Images C
  证明: { has_image := fun {_} {_} f => { exists_image := ⟨imageFactorisation f⟩ } }

Depends on / 依赖: exists_image, has_image, imageFactorisation
-/
theorem hasImages : HasImages C :=
  { has_image := fun {_} {_} f => { exists_image := ⟨imageFactorisation f⟩ } }

variable [Limits.HasFiniteProducts C]

attribute [local instance] Limits.HasFiniteBiproducts.of_hasFiniteProducts

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isNormalMonoCategory` / 引理 `isNormalMonoCategory`

English:
lemma isNormalMonoCategory
  statement: IsNormalMonoCategory C where
  proof: ⟨{
      Z := _
      g := cokernel.π f
      w := by simp
      isLimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : KernelFork (cokernel.π f)) :
            (limit.lift (parallelPair (cokernel.π f) 0) s ≫ inv (imageMonoFactorisation f).e) ≫
            Fork.ι (KernelFork.ofι _ (cokernel.condition f)) = Fork.ι s := ?_
        · refine isLimitAux _ (fun A => limit.lift _ _ ≫ inv (imageMonoFactorisation f).e) aux ?_
          intro A g hg
          rw [KernelFork.ι_ofι] at hg
          rw [← cancel_mono f]; rw [hg]; rw [← aux]; rw [KernelFork.ι_ofι]
        · simp only [KernelFork.ι_ofι, Category.assoc]
          convert! limit.lift_π s WalkingParallelPair.zero using 2
          rw [IsIso.inv_comp_eq]; rw [eq_comm]
          exact (imageMonoFactorisation f).fac }⟩

中文:
引理 isNormalMonoCategory
  结论: 是正规单态射范畴 C where
  证明: ⟨{
      Z := _
      g := cokernel.π f
      w := by simp
      isLimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : KernelFork (cokernel.π f)) :
            (limit.lift (parallelPair (cokernel.π f) 0) s ≫ inv (imageMonoFactorisation f).e) ≫
            Fork.ι (KernelFork.ofι _ (cokernel.condition f)) = Fork.ι s := ?_
        · refine isLimitAux _ (fun A => limit.lift _ _ ≫ inv (imageMonoFactorisation f).e) aux ?_
          intro A g hg
          rw [KernelFork.ι_ofι] at hg
          rw [← cancel_mono f]; rw [hg]; rw [← aux]; rw [KernelFork.ι_ofι]
        · simp only [KernelFork.ι_ofι, Category.assoc]
          convert! limit.lift_π s WalkingParallelPair.zero using 2
          rw [IsIso.inv_comp_eq]; rw [eq_comm]
          exact (imageMonoFactorisation f).fac }⟩
-/
lemma isNormalMonoCategory : IsNormalMonoCategory C where
  normalMonoOfMono f m := ⟨{
      Z := _
      g := cokernel.π f
      w := by simp
      isLimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : KernelFork (cokernel.π f)) :
            (limit.lift (parallelPair (cokernel.π f) 0) s ≫ inv (imageMonoFactorisation f).e) ≫
            Fork.ι (KernelFork.ofι _ (cokernel.condition f)) = Fork.ι s := ?_
        · refine isLimitAux _ (fun A => limit.lift _ _ ≫ inv (imageMonoFactorisation f).e) aux ?_
          intro A g hg
          rw [KernelFork.ι_ofι] at hg
          rw [← cancel_mono f]; rw [hg]; rw [← aux]; rw [KernelFork.ι_ofι]
        · simp only [KernelFork.ι_ofι, Category.assoc]
          convert! limit.lift_π s WalkingParallelPair.zero using 2
          rw [IsIso.inv_comp_eq]; rw [eq_comm]
          exact (imageMonoFactorisation f).fac }⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isNormalEpiCategory` / 引理 `isNormalEpiCategory`

English:
lemma isNormalEpiCategory
  statement: IsNormalEpiCategory C where
  proof: ⟨{
      W := kernel f
      g := kernel.ι _
      w := kernel.condition _
      isColimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : CokernelCofork (kernel.ι f)) :
            Cofork.π (CokernelCofork.ofπ _ (kernel.condition f)) ≫
              inv (imageMonoFactorisation f).m ≫ inv (Abelian.coimageImageComparison f) ≫
                colimit.desc (parallelPair (kernel.ι f) 0) s = Cofork.π s := ?_
        · refine isColimitAux _ (fun A => inv (imageMonoFactorisation f).m ≫
                  inv (Abelian.coimageImageComparison f) ≫ colimit.desc _ _) aux ?_
          intro A g hg
          rw [CokernelCofork.π_ofπ] at hg
          rw [← cancel_epi f]; rw [hg]; rw [← aux]; rw [CokernelCofork.π_ofπ]
        · simp only [CokernelCofork.π_ofπ, ← Category.assoc]
          convert! colimit.ι_desc s WalkingParallelPair.one using 2
          rw [IsIso.comp_inv_eq]; rw [IsIso.comp_inv_eq]; rw [eq_comm]; rw [← imageMonoFactorisation_e']
          exact (imageMonoFactorisation f).fac }⟩

中文:
引理 isNormalEpiCategory
  结论: 是正规满态射范畴 C where
  证明: ⟨{
      W := kernel f
      g := kernel.ι _
      w := kernel.condition _
      isColimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : CokernelCofork (kernel.ι f)) :
            Cofork.π (CokernelCofork.ofπ _ (kernel.condition f)) ≫
              inv (imageMonoFactorisation f).m ≫ inv (Abelian.coimageImageComparison f) ≫
                colimit.desc (parallelPair (kernel.ι f) 0) s = Cofork.π s := ?_
        · refine isColimitAux _ (fun A => inv (imageMonoFactorisation f).m ≫
                  inv (Abelian.coimageImageComparison f) ≫ colimit.desc _ _) aux ?_
          intro A g hg
          rw [CokernelCofork.π_ofπ] at hg
          rw [← cancel_epi f]; rw [hg]; rw [← aux]; rw [CokernelCofork.π_ofπ]
        · simp only [CokernelCofork.π_ofπ, ← Category.assoc]
          convert! colimit.ι_desc s WalkingParallelPair.one using 2
          rw [IsIso.comp_inv_eq]; rw [IsIso.comp_inv_eq]; rw [eq_comm]; rw [← imageMonoFactorisation_e']
          exact (imageMonoFactorisation f).fac }⟩
-/
lemma isNormalEpiCategory : IsNormalEpiCategory C where
  normalEpiOfEpi f m := ⟨{
      W := kernel f
      g := kernel.ι _
      w := kernel.condition _
      isColimit := by
        haveI : Limits.HasImages C := hasImages
        haveI : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
        haveI : HasZeroObject C := Limits.hasZeroObject_of_hasFiniteBiproducts _
        have aux (s : CokernelCofork (kernel.ι f)) :
            Cofork.π (CokernelCofork.ofπ _ (kernel.condition f)) ≫
              inv (imageMonoFactorisation f).m ≫ inv (Abelian.coimageImageComparison f) ≫
                colimit.desc (parallelPair (kernel.ι f) 0) s = Cofork.π s := ?_
        · refine isColimitAux _ (fun A => inv (imageMonoFactorisation f).m ≫
                  inv (Abelian.coimageImageComparison f) ≫ colimit.desc _ _) aux ?_
          intro A g hg
          rw [CokernelCofork.π_ofπ] at hg
          rw [← cancel_epi f]; rw [hg]; rw [← aux]; rw [CokernelCofork.π_ofπ]
        · simp only [CokernelCofork.π_ofπ, ← Category.assoc]
          convert! colimit.ι_desc s WalkingParallelPair.one using 2
          rw [IsIso.comp_inv_eq]; rw [IsIso.comp_inv_eq]; rw [eq_comm]; rw [← imageMonoFactorisation_e']
          exact (imageMonoFactorisation f).fac }⟩

end OfCoimageImageComparisonIsIso

variable [forall {X Y : C} (f : X ⟶ Y), IsIso (Abelian.coimageImageComparison f)]
  [Limits.HasFiniteProducts C]

attribute [local instance] OfCoimageImageComparisonIsIso.isNormalMonoCategory

attribute [local instance] OfCoimageImageComparisonIsIso.isNormalEpiCategory

/-- A preadditive category with kernels, cokernels, and finite products,
in which the coimage-image comparison morphism is always an isomorphism,
is an abelian category. -/
@[stacks 0109
"The Stacks project uses this characterisation at the definition of an abelian category.",
  instance_reducible]
/--
Definition of `ofCoimageImageComparisonIsIso` / `ofCoimageImageComparisonIsIso` 的定义

English:
definition ofCoimageImageComparisonIsIso
  signature: : Abelian C where

中文:
定义 ofCoimageImageComparisonIsIso
  签名: : 交换 C where
-/
def ofCoimageImageComparisonIsIso : Abelian C where

end CategoryTheory.Abelian

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Porting note: this should be an instance,
-- but triggers https://github.com/leanprover/lean4/issues/2055
-- (this is still the case despite that issue being closed now).
-- We set it as a local instance instead.
-- instance (priority := 100)
-- Turning it into a global instance breaks `Mathlib/Algebra/Category/ModuleCat/Sheaf/Free.lean`.
/--
theorem `hasFiniteBiproducts` / 定理 `hasFiniteBiproducts`

English:
theorem hasFiniteBiproducts
  statement: HasFiniteBiproducts C
  proof: Limits.HasFiniteBiproducts.of_hasFiniteProducts

中文:
定理 hasFiniteBiproducts
  结论: 有FiniteBiproducts C
  证明: Limits.HasFiniteBiproducts.of_hasFiniteProducts

Depends on / 依赖: HasFiniteBiproducts, Limits, Limits.HasFiniteBiproducts.of_hasFiniteProducts, of_hasFiniteProducts
-/
theorem hasFiniteBiproducts : HasFiniteBiproducts C :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

attribute [local instance] hasFiniteBiproducts

instance (priority := 100) hasBinaryBiproducts : HasBinaryBiproducts C :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _

instance (priority := 100) hasZeroObject : HasZeroObject C :=
  hasZeroObject_of_hasInitial_object

section ToNonPreadditiveAbelian

/-- Every abelian category is, in particular, `NonPreadditiveAbelian`. -/
@[instance_reducible]
/--
Definition of `nonPreadditiveAbelian` / `nonPreadditiveAbelian` 的定义

English:
definition nonPreadditiveAbelian
  signature: : NonPreadditiveAbelian C
  body: { ‹Abelian C› with }

中文:
定义 nonPreadditiveAbelian
  签名: : NonPreadditiveAbelian C
  定义体: { ‹Abelian C› with }

Depends on / 依赖: Abelian
-/
def nonPreadditiveAbelian : NonPreadditiveAbelian C :=
  { ‹Abelian C› with }

end ToNonPreadditiveAbelian

section

/-! We now promote some instances that were constructed using `nonPreadditiveAbelian`. -/


attribute [local instance] nonPreadditiveAbelian

variable {P Q : C} (f : P ⟶ Q)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (Abelian.factorThruImage f)
  body: by infer_instance

中文:
实例 :
  签名: 满态射 (交换.factorThruImage f)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Epi (Abelian.factorThruImage f) := by infer_instance

/--
Instance `isIso_factorThruImage` / 实例 `isIso_factorThruImage`

English:
instance isIso_factorThruImage
  signature: [Mono f]
  body: by infer_instance

中文:
实例 isIso_factorThruImage
  签名: [单态射 f]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance isIso_factorThruImage [Mono f] : IsIso (Abelian.factorThruImage f) := by infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (Abelian.factorThruCoimage f)
  body: by infer_instance

中文:
实例 :
  签名: 单态射 (交换.factorThruCoimage f)
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Mono (Abelian.factorThruCoimage f) := by infer_instance

/--
Instance `isIso_factorThruCoimage` / 实例 `isIso_factorThruCoimage`

English:
instance isIso_factorThruCoimage
  signature: [Epi f]
  body: by infer_instance

中文:
实例 isIso_factorThruCoimage
  签名: [满态射 f]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance isIso_factorThruCoimage [Epi f] : IsIso (Abelian.factorThruCoimage f) := by infer_instance

end

section Factor

attribute [local instance] nonPreadditiveAbelian

variable {P Q : C} (f : P ⟶ Q)

section

/--
theorem `mono_of_kernel_ι_eq_zero` / 定理 `mono_of_kernel_ι_eq_zero`

English:
theorem mono_of_kernel_ι_eq_zero
  given: (h : kernel.ι f = 0)
  statement: Mono f
  proof: mono_of_kernel_zero h

中文:
定理 mono_of_kernel_ι_eq_zero
  条件: (h : kernel.ι f = 0)
  结论: 单态射 f
  证明: mono_of_kernel_zero h

Depends on / 依赖: mono_of_kernel_zero
-/
theorem mono_of_kernel_ι_eq_zero (h : kernel.ι f = 0) : Mono f :=
  mono_of_kernel_zero h

/--
theorem `epi_of_cokernel_π_eq_zero` / 定理 `epi_of_cokernel_π_eq_zero`

English:
theorem epi_of_cokernel_π_eq_zero
  given: (h : cokernel.π f = 0)
  statement: Epi f
  proof: epi_of_cokernel_zero h

中文:
定理 epi_of_cokernel_π_eq_zero
  条件: (h : cokernel.π f = 0)
  结论: 满态射 f
  证明: epi_of_cokernel_zero h

Depends on / 依赖: epi_of_cokernel_zero
-/
theorem epi_of_cokernel_π_eq_zero (h : cokernel.π f = 0) : Epi f :=
  epi_of_cokernel_zero h

end

section

variable {f}

/--
theorem `image_ι_comp_eq_zero` / 定理 `image_ι_comp_eq_zero`

English:
theorem image_ι_comp_eq_zero
  given: {R : C} {g : Q ⟶ R} (h : f ≫ g = 0)
  statement: Abelian.image.ι f ≫ g = 0
  proof: zero_of_epi_comp (Abelian.factorThruImage f) by simp [h]

中文:
定理 image_ι_comp_eq_zero
  条件: {R : C} {g : Q ⟶ R} (h : f ≫ g = 0)
  结论: 交换.像.ι f ≫ g = 0
  证明: zero_of_epi_comp (Abelian.factorThruImage f) by simp [h]

Depends on / 依赖: Abelian, Abelian.factorThruImage, factorThruImage, zero_of_epi_comp
-/
theorem image_ι_comp_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : Abelian.image.ι f ≫ g = 0 :=
zero_of_epi_comp (Abelian.factorThruImage f) by simp [h]

/--
theorem `comp_coimage_π_eq_zero` / 定理 `comp_coimage_π_eq_zero`

English:
theorem comp_coimage_π_eq_zero
  given: {R : C} {g : Q ⟶ R} (h : f ≫ g = 0)
  statement: f ≫ Abelian.coimage.π g = 0
  proof: zero_of_comp_mono (Abelian.factorThruCoimage g) by simp [h]

中文:
定理 comp_coimage_π_eq_zero
  条件: {R : C} {g : Q ⟶ R} (h : f ≫ g = 0)
  结论: f ≫ 交换.coimage.π g = 0
  证明: zero_of_comp_mono (Abelian.factorThruCoimage g) by simp [h]

Depends on / 依赖: Abelian, Abelian.factorThruCoimage, factorThruCoimage, zero_of_comp_mono
-/
theorem comp_coimage_π_eq_zero {R : C} {g : Q ⟶ R} (h : f ≫ g = 0) : f ≫ Abelian.coimage.π g = 0 :=
zero_of_comp_mono (Abelian.factorThruCoimage g) by simp [h]

end

/-- Factoring through the image is a strong epi-mono factorisation. -/
@[simps]
/--
Definition of `imageStrongEpiMonoFactorisation` / `imageStrongEpiMonoFactorisation` 的定义

English:
definition imageStrongEpiMonoFactorisation
  signature: : StrongEpiMonoFactorisation f where
  body: Abelian.image f
  m := image.ι f
  m_mono := by infer_instance
  e := Abelian.factorThruImage f
  e_strong_epi := strongEpi_of_epi _

中文:
定义 imageStrongEpiMonoFactorisation
  签名: : StrongEpiMonoFactorisation f where
  定义体: Abelian.image f
  m := image.ι f
  m_mono := by infer_instance
  e := Abelian.factorThruImage f
  e_strong_epi := strongEpi_of_epi _

Depends on / 依赖: Abelian, Abelian.image
-/
def imageStrongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := Abelian.image f
  m := image.ι f
  m_mono := by infer_instance
  e := Abelian.factorThruImage f
  e_strong_epi := strongEpi_of_epi _

/-- Factoring through the coimage is a strong epi-mono factorisation. -/
@[simps]
/--
Definition of `coimageStrongEpiMonoFactorisation` / `coimageStrongEpiMonoFactorisation` 的定义

English:
definition coimageStrongEpiMonoFactorisation
  signature: : StrongEpiMonoFactorisation f where
  body: Abelian.coimage f
  m := Abelian.factorThruCoimage f
  m_mono := by infer_instance
  e := coimage.π f
  e_strong_epi := strongEpi_of_epi _

中文:
定义 coimageStrongEpiMonoFactorisation
  签名: : StrongEpiMonoFactorisation f where
  定义体: Abelian.coimage f
  m := Abelian.factorThruCoimage f
  m_mono := by infer_instance
  e := coimage.π f
  e_strong_epi := strongEpi_of_epi _

Depends on / 依赖: Abelian, Abelian.coimage, coimage
-/
def coimageStrongEpiMonoFactorisation : StrongEpiMonoFactorisation f where
  I := Abelian.coimage f
  m := Abelian.factorThruCoimage f
  m_mono := by infer_instance
  e := coimage.π f
  e_strong_epi := strongEpi_of_epi _

end Factor

section HasStrongEpiMonoFactorisations

/-- An abelian category has strong epi-mono factorisations. -/
instance (priority := 100) : HasStrongEpiMonoFactorisations C :=
  HasStrongEpiMonoFactorisations.mk fun f => imageStrongEpiMonoFactorisation f

-- In particular, this means that it has well-behaved images.
example : HasImages C := by infer_instance

example : HasImageMaps C := by infer_instance

end HasStrongEpiMonoFactorisations

section Images

variable {X Y : C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (coimageImageComparison f)
  body: by
  convert!
    Iso.isIso_hom
      (IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage
        (imageStrongEpiMonoFactorisation f).toMonoIsImage)
  ext
  change _ = _ ≫ (imageStrongEpiMonoFactorisation f).m
  simp [-imageStrongEpiMonoFactorisation_m]

中文:
实例 :
  签名: 是同构 (coimageImageComparison f)
  定义体: by
  convert!
    Iso.isIso_hom
      (IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage
        (imageStrongEpiMonoFactorisation f).toMonoIsImage)
  ext
  change _ = _ ≫ (imageStrongEpiMonoFactorisation f).m
  simp [-imageStrongEpiMonoFactorisation_m]

Depends on / 依赖: IsImage, IsImage.isoExt, Iso.isIso_hom, coimageStrongEpiMonoFactorisation, convert, imageStrongEpiMonoFactorisation, imageStrongEpiMonoFactorisation_m, isIso_hom, isoExt, toMonoIsImage
-/
instance : IsIso (coimageImageComparison f) := by
  convert!
    Iso.isIso_hom
      (IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage
        (imageStrongEpiMonoFactorisation f).toMonoIsImage)
  ext
  change _ = _ ≫ (imageStrongEpiMonoFactorisation f).m
  simp [-imageStrongEpiMonoFactorisation_m]

/--
Definition of `coimageIsoImage` / `coimageIsoImage` 的定义

English:
abbreviation coimageIsoImage
  signature: : Abelian.coimage f ≅ Abelian.image f
  body: asIso (coimageImageComparison f)

中文:
缩写 coimageIsoImage
  签名: : 交换.coimage f ≅ 交换.像 f
  定义体: asIso (coimageImageComparison f)

Depends on / 依赖: coimageImageComparison
-/
abbrev coimageIsoImage : Abelian.coimage f ≅ Abelian.image f :=
  asIso (coimageImageComparison f)

/--
Definition of `coimageIsoImage'` / `coimageIsoImage'` 的定义

English:
abbreviation coimageIsoImage'
  signature: : Abelian.coimage f ≅ image f
  body: IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

中文:
缩写 coimageIsoImage'
  签名: : 交换.coimage f ≅ 像 f
  定义体: IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, coimageStrongEpiMonoFactorisation, isImage, isoExt, toMonoIsImage
-/
abbrev coimageIsoImage' : Abelian.coimage f ≅ image f :=
  IsImage.isoExt (coimageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coimageIsoImage'_hom` / 定理 `coimageIsoImage'_hom`

English:
theorem coimageIsoImage'_hom
  proof: by
  ext
  simp only [← cancel_mono (Limits.image.ι f), IsImage.isoExt_hom, cokernel.π_desc,
    Category.assoc, IsImage.lift_ι, coimageStrongEpiMonoFactorisation_m,
    Limits.image.fac]

中文:
定理 coimageIsoImage'_hom
  证明: by
  ext
  simp only [← cancel_mono (Limits.image.ι f), IsImage.isoExt_hom, cokernel.π_desc,
    Category.assoc, IsImage.lift_ι, coimageStrongEpiMonoFactorisation_m,
    Limits.image.fac]
-/
theorem coimageIsoImage'_hom :
    (coimageIsoImage' f).hom =
      cokernel.desc _ (factorThruImage f) (by simp [← cancel_mono (Limits.image.ι f)]) := by
  ext
  simp only [← cancel_mono (Limits.image.ι f), IsImage.isoExt_hom, cokernel.π_desc,
    Category.assoc, IsImage.lift_ι, coimageStrongEpiMonoFactorisation_m,
    Limits.image.fac]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `factorThruImage_comp_coimageIsoImage'_inv` / 定理 `factorThruImage_comp_coimageIsoImage'_inv`

English:
theorem factorThruImage_comp_coimageIsoImage'_inv
  proof: by
  simp only [IsImage.isoExt_inv, image.isImage_lift, image.fac_lift,
    coimageStrongEpiMonoFactorisation_e]

中文:
定理 factorThruImage_comp_coimageIsoImage'_inv
  证明: by
  simp only [IsImage.isoExt_inv, image.isImage_lift, image.fac_lift,
    coimageStrongEpiMonoFactorisation_e]

Depends on / 依赖: IsImage, IsImage.isoExt_inv, coimageStrongEpiMonoFactorisation_e, fac_lift, image.fac_lift, image.isImage_lift, isImage_lift, isoExt_inv
-/
theorem factorThruImage_comp_coimageIsoImage'_inv :
    factorThruImage f ≫ (coimageIsoImage' f).inv = cokernel.π _ := by
  simp only [IsImage.isoExt_inv, image.isImage_lift, image.fac_lift,
    coimageStrongEpiMonoFactorisation_e]

variable {Z : C} (g : Y ⟶ Z)

/--
lemma `image.ι_comp_eq_zero` / 引理 `image.ι_comp_eq_zero`

English:
lemma image.ι_comp_eq_zero
  statement: image.ι f ≫ g = 0 ↔ f ≫ g = 0
  proof: by
  simp [← cancel_epi (Abelian.factorThruImage _)]

中文:
引理 像.ι_comp_eq_zero
  结论: 像.ι f ≫ g = 0 ↔ f ≫ g = 0
  证明: by
  simp [← cancel_epi (Abelian.factorThruImage _)]
-/
@[simp] lemma image.ι_comp_eq_zero : image.ι f ≫ g = 0 ↔ f ≫ g = 0 := by
  simp [← cancel_epi (Abelian.factorThruImage _)]

/--
lemma `coimage.comp_π_eq_zero` / 引理 `coimage.comp_π_eq_zero`

English:
lemma coimage.comp_π_eq_zero
  statement: f ≫ coimage.π g = 0 ↔ f ≫ g = 0
  proof: by
  simp [← cancel_mono (Abelian.factorThruCoimage _)]

中文:
引理 coimage.comp_π_eq_zero
  结论: f ≫ coimage.π g = 0 ↔ f ≫ g = 0
  证明: by
  simp [← cancel_mono (Abelian.factorThruCoimage _)]
-/
@[simp] lemma coimage.comp_π_eq_zero : f ≫ coimage.π g = 0 ↔ f ≫ g = 0 := by
  simp [← cancel_mono (Abelian.factorThruCoimage _)]

/-- `Abelian.image` as a functor from the arrow category. -/
@[simps]
/--
Definition of `im` / `im` 的定义

English:
definition im
  signature: : Arrow C ⥤ C where
  body: Abelian.image f.hom
map {f g} u := kernel.lift _ (Abelian.image.ι f.hom ≫ u.right) by simp [← Arrow.w_assoc u]

中文:
定义 im
  签名: : 箭头 C ⥤ C where
  定义体: Abelian.image f.hom
map {f g} u := kernel.lift _ (Abelian.image.ι f.hom ≫ u.right) by simp [← Arrow.w_assoc u]

Depends on / 依赖: Abelian, Abelian.image, f.hom
-/
def im : Arrow C ⥤ C where
  obj f := Abelian.image f.hom
map {f g} u := kernel.lift _ (Abelian.image.ι f.hom ≫ u.right) by simp [← Arrow.w_assoc u]

/-- `Abelian.coimage` as a functor from the arrow category. -/
@[simps]
/--
Definition of `coim` / `coim` 的定义

English:
definition coim
  signature: : Arrow C ⥤ C where
  body: Abelian.coimage f.hom
map {f g} u := cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom) by
    simp [← Category.assoc, coimage.comp_π_eq_zero]; simp

中文:
定义 coim
  签名: : 箭头 C ⥤ C where
  定义体: Abelian.coimage f.hom
map {f g} u := cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom) by
    simp [← Category.assoc, coimage.comp_π_eq_zero]; simp

Depends on / 依赖: Abelian, Abelian.coimage, coimage, f.hom
-/
def coim : Arrow C ⥤ C where
  obj f := Abelian.coimage f.hom
map {f g} u := cokernel.desc _ (u.left ≫ Abelian.coimage.π g.hom) by
    simp [← Category.assoc, coimage.comp_π_eq_zero]; simp

set_option backward.defeqAttrib.useBackward true in
/-- The image and coimage of an arrow are naturally isomorphic. -/
@[simps!]
/--
Definition of `coimIsoIm` / `coimIsoIm` 的定义

English:
definition coimIsoIm
  signature: : coim (C := C) ≅ im
  body: NatIso.ofComponents fun _ => Abelian.coimageIsoImage _

中文:
定义 coimIsoIm
  签名: : coim (C := C) ≅ im
  定义体: NatIso.ofComponents fun _ => Abelian.coimageIsoImage _
-/
def coimIsoIm : coim (C := C) ≅ im :=
  NatIso.ofComponents fun _ => Abelian.coimageIsoImage _

/--
Definition of `imageIsoImage` / `imageIsoImage` 的定义

English:
abbreviation imageIsoImage
  signature: : Abelian.image f ≅ image f
  body: IsImage.isoExt (imageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

中文:
缩写 imageIsoImage
  签名: : 交换.像 f ≅ 像 f
  定义体: IsImage.isoExt (imageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

Depends on / 依赖: Image.isImage, IsImage, IsImage.isoExt, imageStrongEpiMonoFactorisation, isImage, isoExt, toMonoIsImage
-/
abbrev imageIsoImage : Abelian.image f ≅ image f :=
  IsImage.isoExt (imageStrongEpiMonoFactorisation f).toMonoIsImage (Image.isImage f)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `imageIsoImage_hom_comp_image_ι` / 定理 `imageIsoImage_hom_comp_image_ι`

English:
theorem imageIsoImage_hom_comp_image_ι
  statement: (imageIsoImage f).hom ≫ Limits.image.ι _ = kernel.ι _
  proof: by
  simp only [IsImage.isoExt_hom, IsImage.lift_ι, imageStrongEpiMonoFactorisation_m]

中文:
定理 imageIsoImage_hom_comp_image_ι
  结论: (imageIsoImage f).hom ≫ Limits.像.ι _ = kernel.ι _
  证明: by
  simp only [IsImage.isoExt_hom, IsImage.lift_ι, imageStrongEpiMonoFactorisation_m]

Depends on / 依赖: IsImage, IsImage.isoExt_hom, IsImage.lift_, imageStrongEpiMonoFactorisation_m, isoExt_hom
-/
theorem imageIsoImage_hom_comp_image_ι : (imageIsoImage f).hom ≫ Limits.image.ι _ = kernel.ι _ := by
  simp only [IsImage.isoExt_hom, IsImage.lift_ι, imageStrongEpiMonoFactorisation_m]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `imageIsoImage_inv` / 定理 `imageIsoImage_inv`

English:
theorem imageIsoImage_inv
  proof: by
  ext
  rw [IsImage.isoExt_inv]; rw [image.isImage_lift]; rw [Limits.image.fac_lift]; rw [imageStrongEpiMonoFactorisation_e]; rw [Category.assoc]; rw [kernel.lift_ι]; rw [equalizer_as_kernel]; rw [kernel.lift_ι]; rw [Limits.image.fac]

中文:
定理 imageIsoImage_inv
  证明: by
  ext
  rw [IsImage.isoExt_inv]; rw [image.isImage_lift]; rw [Limits.image.fac_lift]; rw [imageStrongEpiMonoFactorisation_e]; rw [Category.assoc]; rw [kernel.lift_ι]; rw [equalizer_as_kernel]; rw [kernel.lift_ι]; rw [Limits.image.fac]

Depends on / 依赖: Category, Category.assoc, IsImage, IsImage.isoExt_inv, Limits, Limits.image.fac, Limits.image.fac_lift, equalizer_as_kernel, fac_lift, image.isImage_lift, imageStrongEpiMonoFactorisation_e, isImage_lift, isoExt_inv, kernel, kernel.lift_
-/
theorem imageIsoImage_inv :
    (imageIsoImage f).inv =
      kernel.lift _ (Limits.image.ι f) (by simp [← cancel_epi (factorThruImage f)]) := by
  ext
  rw [IsImage.isoExt_inv]; rw [image.isImage_lift]; rw [Limits.image.fac_lift]; rw [imageStrongEpiMonoFactorisation_e]; rw [Category.assoc]; rw [kernel.lift_ι]; rw [equalizer_as_kernel]; rw [kernel.lift_ι]; rw [Limits.image.fac]

end Images

section CokernelOfKernel

variable {X Y : C} {f : X ⟶ Y}

attribute [local instance] nonPreadditiveAbelian

/--
Definition of `epiIsCokernelOfKernel` / `epiIsCokernelOfKernel` 的定义

English:
definition epiIsCokernelOfKernel
  signature: [Epi f] (s : Fork f 0) (h : IsLimit s)
  body: NonPreadditiveAbelian.epiIsCokernelOfKernel s h

中文:
定义 epiIsCokernelOfKernel
  签名: [满态射 f] (s : 叉 f 0) (h : 是极限 s)
  定义体: NonPreadditiveAbelian.epiIsCokernelOfKernel s h

Depends on / 依赖: NonPreadditiveAbelian, NonPreadditiveAbelian.epiIsCokernelOfKernel, epiIsCokernelOfKernel
-/
def epiIsCokernelOfKernel [Epi f] (s : Fork f 0) (h : IsLimit s) :
    IsColimit (CokernelCofork.ofπ f (KernelFork.condition s)) :=
  NonPreadditiveAbelian.epiIsCokernelOfKernel s h

/--
Definition of `monoIsKernelOfCokernel` / `monoIsKernelOfCokernel` 的定义

English:
definition monoIsKernelOfCokernel
  signature: [Mono f] (s : Cofork f 0) (h : IsColimit s)
  body: NonPreadditiveAbelian.monoIsKernelOfCokernel s h

中文:
定义 monoIsKernelOfCokernel
  签名: [单态射 f] (s : 余叉 f 0) (h : 是余极限 s)
  定义体: NonPreadditiveAbelian.monoIsKernelOfCokernel s h

Depends on / 依赖: NonPreadditiveAbelian, NonPreadditiveAbelian.monoIsKernelOfCokernel, monoIsKernelOfCokernel
-/
def monoIsKernelOfCokernel [Mono f] (s : Cofork f 0) (h : IsColimit s) :
    IsLimit (KernelFork.ofι f (CokernelCofork.condition s)) :=
  NonPreadditiveAbelian.monoIsKernelOfCokernel s h

variable (f)

/--
Definition of `epiDesc` / `epiDesc` 的定义

English:
definition epiDesc
  signature: [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0)
  body: (epiIsCokernelOfKernel _ (limit.isLimit _)).desc (CokernelCofork.ofπ _ hg)

@[reassoc (attr := simp)]

中文:
定义 epiDesc
  签名: [满态射 f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0)
  定义体: (epiIsCokernelOfKernel _ (limit.isLimit _)).desc (CokernelCofork.ofπ _ hg)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, epiIsCokernelOfKernel, isLimit, limit.isLimit
-/
def epiDesc [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) : Y ⟶ T :=
  (epiIsCokernelOfKernel _ (limit.isLimit _)).desc (CokernelCofork.ofπ _ hg)

@[reassoc (attr := simp)]
/--
theorem `comp_epiDesc` / 定理 `comp_epiDesc`

English:
theorem comp_epiDesc
  given: [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0)
  proof: (epiIsCokernelOfKernel _ (limit.isLimit _)).fac (CokernelCofork.ofπ _ hg) WalkingParallelPair.one

中文:
定理 comp_epiDesc
  条件: [满态射 f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0)
  证明: (epiIsCokernelOfKernel _ (limit.isLimit _)).fac (CokernelCofork.ofπ _ hg) WalkingParallelPair.one

Depends on / 依赖: CokernelCofork, CokernelCofork.of, WalkingParallelPair, WalkingParallelPair.one, epiIsCokernelOfKernel, isLimit, limit.isLimit
-/
theorem comp_epiDesc [Epi f] {T : C} (g : X ⟶ T) (hg : kernel.ι f ≫ g = 0) :
    f ≫ epiDesc f g hg = g :=
  (epiIsCokernelOfKernel _ (limit.isLimit _)).fac (CokernelCofork.ofπ _ hg) WalkingParallelPair.one

/--
Definition of `monoLift` / `monoLift` 的定义

English:
definition monoLift
  signature: [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0)
  body: (monoIsKernelOfCokernel _ (colimit.isColimit _)).lift (KernelFork.ofι _ hg)

@[reassoc (attr := simp)]

中文:
定义 monoLift
  签名: [单态射 f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0)
  定义体: (monoIsKernelOfCokernel _ (colimit.isColimit _)).lift (KernelFork.ofι _ hg)

@[reassoc (attr := simp)]

Depends on / 依赖: KernelFork, KernelFork.of, colimit, colimit.isColimit, isColimit, monoIsKernelOfCokernel
-/
def monoLift [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) : T ⟶ X :=
  (monoIsKernelOfCokernel _ (colimit.isColimit _)).lift (KernelFork.ofι _ hg)

@[reassoc (attr := simp)]
/--
theorem `monoLift_comp` / 定理 `monoLift_comp`

English:
theorem monoLift_comp
  given: [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0)
  proof: (monoIsKernelOfCokernel _ (colimit.isColimit _)).fac (KernelFork.ofι _ hg)
    WalkingParallelPair.zero

中文:
定理 monoLift_comp
  条件: [单态射 f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0)
  证明: (monoIsKernelOfCokernel _ (colimit.isColimit _)).fac (KernelFork.ofι _ hg)
    WalkingParallelPair.zero

Depends on / 依赖: KernelFork, KernelFork.of, WalkingParallelPair, WalkingParallelPair.zero, colimit, colimit.isColimit, isColimit, monoIsKernelOfCokernel
-/
theorem monoLift_comp [Mono f] {T : C} (g : T ⟶ Y) (hg : g ≫ cokernel.π f = 0) :
    monoLift f g hg ≫ f = g :=
  (monoIsKernelOfCokernel _ (colimit.isColimit _)).fac (KernelFork.ofι _ hg)
    WalkingParallelPair.zero

section

variable {D : Type*} [Category* D] [HasZeroMorphisms D]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitMapConeOfKernelForkOfι` / `isLimitMapConeOfKernelForkOfι` 的定义

English:
definition isLimitMapConeOfKernelForkOfι
  body: by
  let e : parallelPair (cokernel.π (F.map i)) 0 ≅ parallelPair (cokernel.π i) 0 ⋙ F :=
    parallelPair.ext (Iso.refl _) (asIso (cokernelComparison i F)) (by simp) (by simp)
  refine IsLimit.postcomposeInvEquiv e _ ?_
  let hi := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (F.map i))
  refine IsLimit.ofIsoLimit hi (Fork.ext (Iso.refl _) ?_)
  change 𝟙 _ ≫ F.map i ≫ 𝟙 _ = F.map i
  rw [Category.comp_id]; rw [Category.id_comp]

中文:
定义 isLimitMapConeOfKernelForkOfι
  定义体: by
  let e : parallelPair (cokernel.π (F.map i)) 0 ≅ parallelPair (cokernel.π i) 0 ⋙ F :=
    parallelPair.ext (Iso.refl _) (asIso (cokernelComparison i F)) (by simp) (by simp)
  refine IsLimit.postcomposeInvEquiv e _ ?_
  let hi := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (F.map i))
  refine IsLimit.ofIsoLimit hi (Fork.ext (Iso.refl _) ?_)
  change 𝟙 _ ≫ F.map i ≫ 𝟙 _ = F.map i
  rw [Category.comp_id]; rw [Category.id_comp]

Depends on / 依赖: Abelian, Abelian.monoIsKernelOfCokernel, Category, Category.comp_id, Category.id_comp, F.map, Fork.ext, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeInvEquiv, Iso.refl, cokernel, cokernelComparison, cokernelIsCokernel, comp_id, id_comp, monoIsKernelOfCokernel, ofIsoLimit, parallelPair, parallelPair.ext
-/
noncomputable def isLimitMapConeOfKernelForkOfι
    {X Y : D} (i : X ⟶ Y) [HasCokernel i] (F : D ⥤ C)
    [F.PreservesZeroMorphisms] [Mono (F.map i)]
    [PreservesColimit (parallelPair i 0) F] :
    IsLimit (F.mapCone (KernelFork.ofι i (cokernel.condition i))) := by
  let e : parallelPair (cokernel.π (F.map i)) 0 ≅ parallelPair (cokernel.π i) 0 ⋙ F :=
    parallelPair.ext (Iso.refl _) (asIso (cokernelComparison i F)) (by simp) (by simp)
  refine IsLimit.postcomposeInvEquiv e _ ?_
  let hi := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (F.map i))
  refine IsLimit.ofIsoLimit hi (Fork.ext (Iso.refl _) ?_)
  change 𝟙 _ ≫ F.map i ≫ 𝟙 _ = F.map i
  rw [Category.comp_id]; rw [Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitMapCoconeOfCokernelCoforkOfπ` / `isColimitMapCoconeOfCokernelCoforkOfπ` 的定义

English:
definition isColimitMapCoconeOfCokernelCoforkOfπ
  body: by
  let e : parallelPair (kernel.ι p) 0 ⋙ F ≅ parallelPair (kernel.ι (F.map p)) 0 :=
    parallelPair.ext (asIso (kernelComparison p F)) (Iso.refl _) (by simp) (by simp)
  refine IsColimit.precomposeInvEquiv e _ ?_
  let hp := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (F.map p))
  refine IsColimit.ofIsoColimit hp (Cofork.ext (Iso.refl _) ?_)
  change F.map p ≫ 𝟙 _ = 𝟙 _ ≫ F.map p
  rw [Category.comp_id]; rw [Category.id_comp]

中文:
定义 isColimitMapCoconeOfCokernelCoforkOfπ
  定义体: by
  let e : parallelPair (kernel.ι p) 0 ⋙ F ≅ parallelPair (kernel.ι (F.map p)) 0 :=
    parallelPair.ext (asIso (kernelComparison p F)) (Iso.refl _) (by simp) (by simp)
  refine IsColimit.precomposeInvEquiv e _ ?_
  let hp := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (F.map p))
  refine IsColimit.ofIsoColimit hp (Cofork.ext (Iso.refl _) ?_)
  change F.map p ≫ 𝟙 _ = 𝟙 _ ≫ F.map p
  rw [Category.comp_id]; rw [Category.id_comp]

Depends on / 依赖: Abelian, Abelian.epiIsCokernelOfKernel, Category, Category.comp_id, Category.id_comp, Cofork, Cofork.ext, F.map, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeInvEquiv, Iso.refl, comp_id, epiIsCokernelOfKernel, id_comp, kernel, kernelComparison, kernelIsKernel, ofIsoColimit, parallelPair
-/
noncomputable def isColimitMapCoconeOfCokernelCoforkOfπ
    {X Y : D} (p : X ⟶ Y) [HasKernel p] (F : D ⥤ C)
    [F.PreservesZeroMorphisms] [Epi (F.map p)]
    [PreservesLimit (parallelPair p 0) F] :
    IsColimit (F.mapCocone (CokernelCofork.ofπ p (kernel.condition p))) := by
  let e : parallelPair (kernel.ι p) 0 ⋙ F ≅ parallelPair (kernel.ι (F.map p)) 0 :=
    parallelPair.ext (asIso (kernelComparison p F)) (Iso.refl _) (by simp) (by simp)
  refine IsColimit.precomposeInvEquiv e _ ?_
  let hp := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (F.map p))
  refine IsColimit.ofIsoColimit hp (Cofork.ext (Iso.refl _) ?_)
  change F.map p ≫ 𝟙 _ = 𝟙 _ ≫ F.map p
  rw [Category.comp_id]; rw [Category.id_comp]

end

end CokernelOfKernel

section

instance (priority := 100) hasEqualizers : HasEqualizers C :=
  Preadditive.hasEqualizers_of_hasKernels

/-- Any abelian category has pullbacks -/
instance (priority := 100) hasPullbacks : HasPullbacks C :=
  hasPullbacks_of_hasBinaryProducts_of_hasEqualizers C

end

section

instance (priority := 100) hasCoequalizers : HasCoequalizers C :=
  Preadditive.hasCoequalizers_of_hasCokernels

/-- Any abelian category has pushouts -/
instance (priority := 100) hasPushouts : HasPushouts C :=
  hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers C

instance (priority := 100) hasFiniteLimits : HasFiniteLimits C :=
  Limits.hasFiniteLimits_of_hasEqualizers_and_finite_products

instance (priority := 100) hasFiniteColimits : HasFiniteColimits C :=
  Limits.hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

end

namespace PullbackToBiproductIsKernel

variable [Limits.HasPullbacks C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-! This section contains a slightly technical result about pullbacks and biproducts.
    We will need it in the proof that the pullback of an epimorphism is an epimorphism. -/


/--
Definition of `pullbackToBiproduct` / `pullbackToBiproduct` 的定义

English:
abbreviation pullbackToBiproduct
  signature: : pullback f g ⟶ X ⊞ Y
  body: biprod.lift (pullback.fst f g) (pullback.snd f g)

中文:
缩写 pullbackToBiproduct
  签名: : pullback f g ⟶ X ⊞ Y
  定义体: biprod.lift (pullback.fst f g) (pullback.snd f g)

Depends on / 依赖: biprod, biprod.lift, pullback, pullback.fst, pullback.snd
-/
abbrev pullbackToBiproduct : pullback f g ⟶ X ⊞ Y :=
  biprod.lift (pullback.fst f g) (pullback.snd f g)

/--
Definition of `pullbackToBiproductFork` / `pullbackToBiproductFork` 的定义

English:
abbreviation pullbackToBiproductFork
  signature: : KernelFork (biprod.desc f (-g))
  body: KernelFork.ofι (pullbackToBiproduct f g) by
    rw [biprod.lift_desc]; rw [comp_neg]; rw [pullback.condition]; rw [add_neg_cancel]

中文:
缩写 pullbackToBiproductFork
  签名: : 核叉 (biprod.desc f (-g))
  定义体: KernelFork.ofι (pullbackToBiproduct f g) by
    rw [biprod.lift_desc]; rw [comp_neg]; rw [pullback.condition]; rw [add_neg_cancel]

Depends on / 依赖: KernelFork, KernelFork.of, add_neg_cancel, biprod, biprod.lift_desc, comp_neg, condition, lift_desc, pullback, pullback.condition, pullbackToBiproduct
-/
abbrev pullbackToBiproductFork : KernelFork (biprod.desc f (-g)) :=
KernelFork.ofι (pullbackToBiproduct f g) by
    rw [biprod.lift_desc]; rw [comp_neg]; rw [pullback.condition]; rw [add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitPullbackToBiproduct` / `isLimitPullbackToBiproduct` 的定义

English:
definition isLimitPullbackToBiproduct
  signature: : IsLimit (pullbackToBiproductFork f g)
  body: Fork.IsLimit.mk _
    (fun s =>
pullback.lift (Fork.ι s ≫ biprod.fst) (Fork.ι s ≫ biprod.snd)
sub_eq_zero.1 by
          rw [Category.assoc]; rw [Category.assoc]; rw [← comp_sub]; rw [sub_eq_add_neg]; rw [← comp_neg]; rw [←
            biprod.desc_eq]; rw [KernelFork.condition s])
    (fun s => by
      apply biprod.hom_ext <;> rw [Fork.ι_ofι, Category.assoc]
      · rw [biprod.lift_fst, pullback.lift_fst]
      · rw [biprod.lift_snd, pullback.lift_snd])
    fun s m h => by apply pullback.hom_ext <;> simp [← h]

中文:
定义 isLimitPullbackToBiproduct
  签名: : 是极限 (pullbackToBiproductFork f g)
  定义体: Fork.IsLimit.mk _
    (fun s =>
pullback.lift (Fork.ι s ≫ biprod.fst) (Fork.ι s ≫ biprod.snd)
sub_eq_zero.1 by
          rw [Category.assoc]; rw [Category.assoc]; rw [← comp_sub]; rw [sub_eq_add_neg]; rw [← comp_neg]; rw [←
            biprod.desc_eq]; rw [KernelFork.condition s])
    (fun s => by
      apply biprod.hom_ext <;> rw [Fork.ι_ofι, Category.assoc]
      · rw [biprod.lift_fst, pullback.lift_fst]
      · rw [biprod.lift_snd, pullback.lift_snd])
    fun s m h => by apply pullback.hom_ext <;> simp [← h]

Depends on / 依赖: Category, Category.assoc, Fork.IsLimit.mk, IsLimit, KernelFork, KernelFork.condition, biprod, biprod.desc_eq, biprod.fst, biprod.hom_ext, biprod.lift_fst, biprod.lift_snd, biprod.snd, comp_neg, comp_sub, condition, desc_eq, hom_ext, lift_fst, lift_snd
-/
def isLimitPullbackToBiproduct : IsLimit (pullbackToBiproductFork f g) :=
  Fork.IsLimit.mk _
    (fun s =>
pullback.lift (Fork.ι s ≫ biprod.fst) (Fork.ι s ≫ biprod.snd)
sub_eq_zero.1 by
          rw [Category.assoc]; rw [Category.assoc]; rw [← comp_sub]; rw [sub_eq_add_neg]; rw [← comp_neg]; rw [←
            biprod.desc_eq]; rw [KernelFork.condition s])
    (fun s => by
      apply biprod.hom_ext <;> rw [Fork.ι_ofι, Category.assoc]
      · rw [biprod.lift_fst, pullback.lift_fst]
      · rw [biprod.lift_snd, pullback.lift_snd])
    fun s m h => by apply pullback.hom_ext <;> simp [← h]

end PullbackToBiproductIsKernel

namespace BiproductToPushoutIsCokernel

variable [Limits.HasPushouts C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

/--
Definition of `biproductToPushout` / `biproductToPushout` 的定义

English:
abbreviation biproductToPushout
  signature: : Y ⊞ Z ⟶ pushout f g
  body: biprod.desc (pushout.inl _ _) (pushout.inr _ _)

中文:
缩写 biproductToPushout
  签名: : Y ⊞ Z ⟶ pushout f g
  定义体: biprod.desc (pushout.inl _ _) (pushout.inr _ _)

Depends on / 依赖: biprod, biprod.desc, pushout, pushout.inl, pushout.inr
-/
abbrev biproductToPushout : Y ⊞ Z ⟶ pushout f g :=
  biprod.desc (pushout.inl _ _) (pushout.inr _ _)

/--
Definition of `biproductToPushoutCofork` / `biproductToPushoutCofork` 的定义

English:
abbreviation biproductToPushoutCofork
  signature: : CokernelCofork (biprod.lift f (-g))
  body: CokernelCofork.ofπ (biproductToPushout f g) by
    rw [biprod.lift_desc]; rw [neg_comp]; rw [pushout.condition]; rw [add_neg_cancel]

中文:
缩写 biproductToPushoutCofork
  签名: : 余核余叉 (biprod.lift f (-g))
  定义体: CokernelCofork.ofπ (biproductToPushout f g) by
    rw [biprod.lift_desc]; rw [neg_comp]; rw [pushout.condition]; rw [add_neg_cancel]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, add_neg_cancel, biprod, biprod.lift_desc, biproductToPushout, condition, lift_desc, neg_comp, pushout, pushout.condition
-/
abbrev biproductToPushoutCofork : CokernelCofork (biprod.lift f (-g)) :=
CokernelCofork.ofπ (biproductToPushout f g) by
    rw [biprod.lift_desc]; rw [neg_comp]; rw [pushout.condition]; rw [add_neg_cancel]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitBiproductToPushout` / `isColimitBiproductToPushout` 的定义

English:
definition isColimitBiproductToPushout
  signature: : IsColimit (biproductToPushoutCofork f g)
  body: Cofork.IsColimit.mk _
    (fun s =>
pushout.desc (biprod.inl ≫ Cofork.π s) (biprod.inr ≫ Cofork.π s)
sub_eq_zero.1 by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [← sub_comp]; rw [sub_eq_add_neg]; rw [← neg_comp]; rw [←
            biprod.lift_eq]; rw [Cofork.condition s]; rw [zero_comp])
    (fun s => by apply biprod.hom_ext' <;> simp)
    fun s m h => by apply pushout.hom_ext <;> simp [← h]

中文:
定义 isColimitBiproductToPushout
  签名: : 是余极限 (biproductToPushoutCofork f g)
  定义体: Cofork.IsColimit.mk _
    (fun s =>
pushout.desc (biprod.inl ≫ Cofork.π s) (biprod.inr ≫ Cofork.π s)
sub_eq_zero.1 by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [← sub_comp]; rw [sub_eq_add_neg]; rw [← neg_comp]; rw [←
            biprod.lift_eq]; rw [Cofork.condition s]; rw [zero_comp])
    (fun s => by apply biprod.hom_ext' <;> simp)
    fun s m h => by apply pushout.hom_ext <;> simp [← h]

Depends on / 依赖: Category, Category.assoc, Cofork, Cofork.IsColimit.mk, Cofork.condition, IsColimit, biprod, biprod.hom_ext, biprod.inl, biprod.inr, biprod.lift_eq, condition, hom_ext, lift_eq, neg_comp, pushout, pushout.desc, pushout.hom_ext, sub_comp, sub_eq_add_neg
-/
def isColimitBiproductToPushout : IsColimit (biproductToPushoutCofork f g) :=
  Cofork.IsColimit.mk _
    (fun s =>
pushout.desc (biprod.inl ≫ Cofork.π s) (biprod.inr ≫ Cofork.π s)
sub_eq_zero.1 by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [← sub_comp]; rw [sub_eq_add_neg]; rw [← neg_comp]; rw [←
            biprod.lift_eq]; rw [Cofork.condition s]; rw [zero_comp])
    (fun s => by apply biprod.hom_ext' <;> simp)
    fun s m h => by apply pushout.hom_ext <;> simp [← h]

end BiproductToPushoutIsCokernel

section EpiPullback

variable [Limits.HasPullbacks C] {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `epi_pullback_of_epi_f` / 实例 `epi_pullback_of_epi_f`

English:
instance epi_pullback_of_epi_f
  signature: [Epi f]
  body: -- It will suffice to consider some morphism e : Y ⟶ R such that
    -- pullback.snd f g ≫ e = 0 and show that e = 0.
    epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (0, e) : X ⊞ Y⟶ R.
    let u := biprod.desc (0 : X ⟶ R) e
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then f ≫ d = 0:
    have : f ≫ d = 0 := calc
      f ≫ d = (biprod.inl ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inl_desc _ _
    -- But f is an epimorphism, so d = 0...
    have : d = 0 := (cancel_epi f).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inr ≫ biprod.desc (0 : X ⟶ R) e := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inr ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _

中文:
实例 epi_pullback_of_epi_f
  签名: [满态射 f]
  定义体: -- It will suffice to consider some morphism e : Y ⟶ R such that
    -- pullback.snd f g ≫ e = 0 and show that e = 0.
    epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (0, e) : X ⊞ Y⟶ R.
    let u := biprod.desc (0 : X ⟶ R) e
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then f ≫ d = 0:
    have : f ≫ d = 0 := calc
      f ≫ d = (biprod.inl ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inl_desc _ _
    -- But f is an epimorphism, so d = 0...
    have : d = 0 := (cancel_epi f).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inr ≫ biprod.desc (0 : X ⟶ R) e := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inr ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _
-/
instance epi_pullback_of_epi_f [Epi f] : Epi (pullback.snd f g) :=
  -- It will suffice to consider some morphism e : Y ⟶ R such that
    -- pullback.snd f g ≫ e = 0 and show that e = 0.
    epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (0, e) : X ⊞ Y⟶ R.
    let u := biprod.desc (0 : X ⟶ R) e
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then f ≫ d = 0:
    have : f ≫ d = 0 := calc
      f ≫ d = (biprod.inl ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inl_desc _ _
    -- But f is an epimorphism, so d = 0...
    have : d = 0 := (cancel_epi f).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inr ≫ biprod.desc (0 : X ⟶ R) e := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inr ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inr ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `epi_pullback_of_epi_g` / 实例 `epi_pullback_of_epi_g`

English:
instance epi_pullback_of_epi_g
  signature: [Epi g]
  body: -- It will suffice to consider some morphism e : X ⟶ R such that
  -- pullback.fst f g ≫ e = 0 and show that e = 0.
  epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (e, 0) : X ⊞ Y ⟶ R.
    let u := biprod.desc e (0 : Y ⟶ R)
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then (-g) ≫ d = 0:
    have : (-g) ≫ d = 0 := calc
      (-g) ≫ d = (biprod.inr ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inr_desc _ _
    -- But g is an epimorphism, thus so is -g, so d = 0...
    have : d = 0 := (cancel_epi (-g)).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inl ≫ biprod.desc e (0 : Y ⟶ R) := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inl ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _

中文:
实例 epi_pullback_of_epi_g
  签名: [满态射 g]
  定义体: -- It will suffice to consider some morphism e : X ⟶ R such that
  -- pullback.fst f g ≫ e = 0 and show that e = 0.
  epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (e, 0) : X ⊞ Y ⟶ R.
    let u := biprod.desc e (0 : Y ⟶ R)
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then (-g) ≫ d = 0:
    have : (-g) ≫ d = 0 := calc
      (-g) ≫ d = (biprod.inr ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inr_desc _ _
    -- But g is an epimorphism, thus so is -g, so d = 0...
    have : d = 0 := (cancel_epi (-g)).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inl ≫ biprod.desc e (0 : Y ⟶ R) := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inl ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _
-/
instance epi_pullback_of_epi_g [Epi g] : Epi (pullback.fst f g) :=
  -- It will suffice to consider some morphism e : X ⟶ R such that
  -- pullback.fst f g ≫ e = 0 and show that e = 0.
  epi_of_cancel_zero _ fun {R} e h => by
    -- Consider the morphism u := (e, 0) : X ⊞ Y ⟶ R.
    let u := biprod.desc e (0 : Y ⟶ R)
    -- The composite pullback f g ⟶ X ⊞ Y ⟶ R is zero by assumption.
    have hu : PullbackToBiproductIsKernel.pullbackToBiproduct f g ≫ u = 0 := by simpa [u]
    -- pullbackToBiproduct f g is a kernel of (f, -g), so (f, -g) is a
    -- cokernel of pullbackToBiproduct f g
    have :=
      epiIsCokernelOfKernel _
        (PullbackToBiproductIsKernel.isLimitPullbackToBiproduct f g)
    -- We use this fact to obtain a factorization of u through (f, -g) via some d : Z ⟶ R.
    obtain ⟨d, hd⟩ := CokernelCofork.IsColimit.desc' this u hu
    dsimp at d; dsimp [u] at hd
    -- But then (-g) ≫ d = 0:
    have : (-g) ≫ d = 0 := calc
      (-g) ≫ d = (biprod.inr ≫ biprod.desc f (-g)) ≫ d := by rw [biprod.inr_desc]
      _ = biprod.inr ≫ u := by rw [Category.assoc, hd]
      _ = 0 := biprod.inr_desc _ _
    -- But g is an epimorphism, thus so is -g, so d = 0...
    have : d = 0 := (cancel_epi (-g)).1 (by simpa)
    -- ...or, in other words, e = 0.
    calc
      e = biprod.inl ≫ biprod.desc e (0 : Y ⟶ R) := by rw [biprod.inl_desc]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ d := by rw [← hd]
      _ = biprod.inl ≫ biprod.desc f (-g) ≫ 0 := by rw [this]
      _ = (biprod.inl ≫ biprod.desc f (-g)) ≫ 0 := by rw [← Category.assoc]
      _ = 0 := HasZeroMorphisms.comp_zero _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_snd_of_isLimit` / 定理 `epi_snd_of_isLimit`

English:
theorem epi_snd_of_isLimit
  given: [Epi f] {s : PullbackCone f g} (hs : IsLimit s)
  statement: Epi s.snd
  proof: by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.right) :=
    Abelian.epi_pullback_of_epi_f f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

中文:
定理 epi_snd_of_isLimit
  条件: [满态射 f] {s : PullbackCone f g} (hs : 是极限 s)
  结论: 满态射 s.snd
  证明: by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.right) :=
    Abelian.epi_pullback_of_epi_f f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

Depends on / 依赖: Abelian, Abelian.epi_pullback_of_epi_f, IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, NatTrans, NatTrans.app, WalkingCospan, WalkingCospan.right, conePointUniqueUpToIso_hom_comp, cospan, epi_of_epi_fac, epi_pullback_of_epi_f, isLimit, limit.cone, limit.isLimit
-/
theorem epi_snd_of_isLimit [Epi f] {s : PullbackCone f g} (hs : IsLimit s) : Epi s.snd := by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.right) :=
    Abelian.epi_pullback_of_epi_f f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_fst_of_isLimit` / 定理 `epi_fst_of_isLimit`

English:
theorem epi_fst_of_isLimit
  given: [Epi g] {s : PullbackCone f g} (hs : IsLimit s)
  statement: Epi s.fst
  proof: by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.left) :=
    Abelian.epi_pullback_of_epi_g f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

中文:
定理 epi_fst_of_isLimit
  条件: [满态射 g] {s : PullbackCone f g} (hs : 是极限 s)
  结论: 满态射 s.fst
  证明: by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.left) :=
    Abelian.epi_pullback_of_epi_g f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

Depends on / 依赖: Abelian, Abelian.epi_pullback_of_epi_g, IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, NatTrans, NatTrans.app, WalkingCospan, WalkingCospan.left, conePointUniqueUpToIso_hom_comp, cospan, epi_of_epi_fac, epi_pullback_of_epi_g, isLimit, limit.cone, limit.isLimit
-/
theorem epi_fst_of_isLimit [Epi g] {s : PullbackCone f g} (hs : IsLimit s) : Epi s.fst := by
  have : Epi (NatTrans.app (limit.cone (cospan f g)).π WalkingCospan.left) :=
    Abelian.epi_pullback_of_epi_g f g
  apply epi_of_epi_fac (IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) hs _)

/--
theorem `epi_fst_of_factor_thru_epi_mono_factorization` / 定理 `epi_fst_of_factor_thru_epi_mono_factorization`

English:
theorem epi_fst_of_factor_thru_epi_mono_factorization
  statement: (g₁ : Y ⟶ W) [Epi g₁] (g₂ : W ⟶ Z) [Mono g₂]
  proof: by
  apply epi_fst_of_isLimit _ _ (PullbackCone.isLimitOfFactors f g g₂ f' g₁ hf hg t ht)

中文:
定理 epi_fst_of_factor_thru_epi_mono_factorization
  结论: (g₁ : Y ⟶ W) [满态射 g₁] (g₂ : W ⟶ Z) [单态射 g₂]
  证明: by
  apply epi_fst_of_isLimit _ _ (PullbackCone.isLimitOfFactors f g g₂ f' g₁ hf hg t ht)

Depends on / 依赖: PullbackCone, PullbackCone.isLimitOfFactors, epi_fst_of_isLimit, isLimitOfFactors
-/
theorem epi_fst_of_factor_thru_epi_mono_factorization (g₁ : Y ⟶ W) [Epi g₁] (g₂ : W ⟶ Z) [Mono g₂]
    (hg : g₁ ≫ g₂ = g) (f' : X ⟶ W) (hf : f' ≫ g₂ = f) (t : PullbackCone f g) (ht : IsLimit t) :
    Epi t.fst := by
  apply epi_fst_of_isLimit _ _ (PullbackCone.isLimitOfFactors f g g₂ f' g₁ hf hg t ht)

end EpiPullback

section MonoPushout

variable [Limits.HasPushouts C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mono_pushout_of_mono_f` / 实例 `mono_pushout_of_mono_f`

English:
instance mono_pushout_of_mono_f
  signature: [Mono f]
  body: mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift (0 : R ⟶ Y) e
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ f = 0 := calc
      d ≫ f = d ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = u ≫ biprod.fst := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_fst _ _
    have : d = 0 := (cancel_mono f).1 (by simpa)
    calc
      e = biprod.lift (0 : R ⟶ Y) e ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [Category.assoc]
      _ = 0 := zero_comp

中文:
实例 mono_pushout_of_mono_f
  签名: [单态射 f]
  定义体: mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift (0 : R ⟶ Y) e
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ f = 0 := calc
      d ≫ f = d ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = u ≫ biprod.fst := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_fst _ _
    have : d = 0 := (cancel_mono f).1 (by simpa)
    calc
      e = biprod.lift (0 : R ⟶ Y) e ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [Category.assoc]
      _ = 0 := zero_comp

Depends on / 依赖: BiproductToPushoutIsCokernel, BiproductToPushoutIsCokernel.biproductToPushout, BiproductToPushoutIsCokernel.isColimitBiproductToPushout, Category, Category.assoc, IsLimit, KernelFork, KernelFork.IsLimit.lift, biprod, biprod.fst, biprod.lift, biprod.lift_fst, biproductToPushout, isColimitBiproductToPushout, lift_fst, monoIsKernelOfCokernel, mono_of_cancel_zero
-/
instance mono_pushout_of_mono_f [Mono f] : Mono (pushout.inr _ _ : Z ⟶ pushout f g) :=
  mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift (0 : R ⟶ Y) e
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ f = 0 := calc
      d ≫ f = d ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = u ≫ biprod.fst := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_fst _ _
    have : d = 0 := (cancel_mono f).1 (by simpa)
    calc
      e = biprod.lift (0 : R ⟶ Y) e ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.snd := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [Category.assoc]
      _ = 0 := zero_comp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `mono_pushout_of_mono_g` / 实例 `mono_pushout_of_mono_g`

English:
instance mono_pushout_of_mono_g
  signature: [Mono g]
  body: mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift e (0 : R ⟶ Z)
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ (-g) = 0 := calc
      d ≫ (-g) = d ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = biprod.lift e (0 : R ⟶ Z) ≫ biprod.snd := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_snd _ _
    have : d = 0 := (cancel_mono (-g)).1 (by simpa)
    calc
      e = biprod.lift e (0 : R ⟶ Z) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [Category.assoc]
      _ = 0 := zero_comp

中文:
实例 mono_pushout_of_mono_g
  签名: [单态射 g]
  定义体: mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift e (0 : R ⟶ Z)
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ (-g) = 0 := calc
      d ≫ (-g) = d ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = biprod.lift e (0 : R ⟶ Z) ≫ biprod.snd := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_snd _ _
    have : d = 0 := (cancel_mono (-g)).1 (by simpa)
    calc
      e = biprod.lift e (0 : R ⟶ Z) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [Category.assoc]
      _ = 0 := zero_comp

Depends on / 依赖: BiproductToPushoutIsCokernel, BiproductToPushoutIsCokernel.biproductToPushout, BiproductToPushoutIsCokernel.isColimitBiproductToPushout, Catego, IsLimit, KernelFork, KernelFork.IsLimit.lift, biprod, biprod.lift, biprod.lift_snd, biprod.snd, biproductToPushout, isColimitBiproductToPushout, lift_snd, monoIsKernelOfCokernel, mono_of_cancel_zero
-/
instance mono_pushout_of_mono_g [Mono g] : Mono (pushout.inl f g) :=
  mono_of_cancel_zero _ fun {R} e h => by
    let u := biprod.lift e (0 : R ⟶ Z)
    have hu : u ≫ BiproductToPushoutIsCokernel.biproductToPushout f g = 0 := by simpa [u]
    have :=
      monoIsKernelOfCokernel _
        (BiproductToPushoutIsCokernel.isColimitBiproductToPushout f g)
    obtain ⟨d, hd⟩ := KernelFork.IsLimit.lift' this u hu
    dsimp at d
    dsimp [u] at hd
    have : d ≫ (-g) = 0 := calc
      d ≫ (-g) = d ≫ biprod.lift f (-g) ≫ biprod.snd := by rw [biprod.lift_snd]
      _ = biprod.lift e (0 : R ⟶ Z) ≫ biprod.snd := by rw [← Category.assoc, hd]
      _ = 0 := biprod.lift_snd _ _
    have : d = 0 := (cancel_mono (-g)).1 (by simpa)
    calc
      e = biprod.lift e (0 : R ⟶ Z) ≫ biprod.fst := by rw [biprod.lift_fst]
      _ = (d ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [← hd]
      _ = (0 ≫ biprod.lift f (-g)) ≫ biprod.fst := by rw [this]
      _ = 0 ≫ biprod.lift f (-g) ≫ biprod.fst := by rw [Category.assoc]
      _ = 0 := zero_comp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_inr_of_isColimit` / 定理 `mono_inr_of_isColimit`

English:
theorem mono_inr_of_isColimit
  given: [Mono f] {s : PushoutCocone f g} (hs : IsColimit s)
  statement: Mono s.inr
  proof: by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.right) :=
    Abelian.mono_pushout_of_mono_f f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

中文:
定理 mono_inr_of_isColimit
  条件: [单态射 f] {s : PushoutCocone f g} (hs : 是余极限 s)
  结论: 单态射 s.inr
  证明: by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.right) :=
    Abelian.mono_pushout_of_mono_f f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

Depends on / 依赖: Abelian, Abelian.mono_pushout_of_mono_f, IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, NatTrans, NatTrans.app, WalkingCospan, WalkingCospan.right, cocone, colimit, colimit.cocone, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, isColimit, mono_of_mono_fac, mono_pushout_of_mono_f
-/
theorem mono_inr_of_isColimit [Mono f] {s : PushoutCocone f g} (hs : IsColimit s) : Mono s.inr := by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.right) :=
    Abelian.mono_pushout_of_mono_f f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_inl_of_isColimit` / 定理 `mono_inl_of_isColimit`

English:
theorem mono_inl_of_isColimit
  given: [Mono g] {s : PushoutCocone f g} (hs : IsColimit s)
  statement: Mono s.inl
  proof: by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.left) :=
    Abelian.mono_pushout_of_mono_g f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

中文:
定理 mono_inl_of_isColimit
  条件: [单态射 g] {s : PushoutCocone f g} (hs : 是余极限 s)
  结论: 单态射 s.inl
  证明: by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.left) :=
    Abelian.mono_pushout_of_mono_g f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

Depends on / 依赖: Abelian, Abelian.mono_pushout_of_mono_g, IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, NatTrans, NatTrans.app, WalkingCospan, WalkingCospan.left, cocone, colimit, colimit.cocone, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, isColimit, mono_of_mono_fac, mono_pushout_of_mono_g
-/
theorem mono_inl_of_isColimit [Mono g] {s : PushoutCocone f g} (hs : IsColimit s) : Mono s.inl := by
  have : Mono (NatTrans.app (colimit.cocone (span f g)).ι WalkingCospan.left) :=
    Abelian.mono_pushout_of_mono_g f g
  apply
    mono_of_mono_fac (IsColimit.comp_coconePointUniqueUpToIso_hom hs (colimit.isColimit _) _)

/--
theorem `mono_inl_of_factor_thru_epi_mono_factorization` / 定理 `mono_inl_of_factor_thru_epi_mono_factorization`

English:
theorem mono_inl_of_factor_thru_epi_mono_factorization
  statement: (f : X ⟶ Y) (g : X ⟶ Z) (g₁ : X ⟶ W) [Epi g₁]
  proof: by
  apply mono_inl_of_isColimit _ _ (PushoutCocone.isColimitOfFactors _ _ _ _ _ hf hg t ht)

中文:
定理 mono_inl_of_factor_thru_epi_mono_factorization
  结论: (f : X ⟶ Y) (g : X ⟶ Z) (g₁ : X ⟶ W) [满态射 g₁]
  证明: by
  apply mono_inl_of_isColimit _ _ (PushoutCocone.isColimitOfFactors _ _ _ _ _ hf hg t ht)

Depends on / 依赖: PushoutCocone, PushoutCocone.isColimitOfFactors, isColimitOfFactors, mono_inl_of_isColimit
-/
theorem mono_inl_of_factor_thru_epi_mono_factorization (f : X ⟶ Y) (g : X ⟶ Z) (g₁ : X ⟶ W) [Epi g₁]
    (g₂ : W ⟶ Z) [Mono g₂] (hg : g₁ ≫ g₂ = g) (f' : W ⟶ Y) (hf : g₁ ≫ f' = f)
    (t : PushoutCocone f g) (ht : IsColimit t) : Mono t.inl := by
  apply mono_inl_of_isColimit _ _ (PushoutCocone.isColimitOfFactors _ _ _ _ _ hf hg t ht)

end MonoPushout

end CategoryTheory.Abelian

namespace CategoryTheory.NonPreadditiveAbelian

variable (C : Type u) [Category.{v} C] [NonPreadditiveAbelian C]

/-- Every `NonPreadditiveAbelian` category can be promoted to an abelian category. -/
@[instance_reducible]
/--
Definition of `abelian` / `abelian` 的定义

English:
definition abelian
  signature: : Abelian C where
  body: NonPreadditiveAbelian.preadditive
  normalMonoOfMono := fun f _ => ⟨normalMonoOfMono f⟩
  normalEpiOfEpi := fun f _ => ⟨normalEpiOfEpi f⟩

中文:
定义 abelian
  签名: : 交换 C where
  定义体: NonPreadditiveAbelian.preadditive
  normalMonoOfMono := fun f _ => ⟨normalMonoOfMono f⟩
  normalEpiOfEpi := fun f _ => ⟨normalEpiOfEpi f⟩

Depends on / 依赖: NonPreadditiveAbelian, NonPreadditiveAbelian.preadditive, preadditive
-/
def abelian : Abelian C where
  toPreadditive := NonPreadditiveAbelian.preadditive
  normalMonoOfMono := fun f _ => ⟨normalMonoOfMono f⟩
  normalEpiOfEpi := fun f _ => ⟨normalEpiOfEpi f⟩

end CategoryTheory.NonPreadditiveAbelian

namespace CategoryTheory.Abelian

variable {C : Type*} [Category C] [Preadditive C]

/--
Definition of `AbelianStruct` / `AbelianStruct` 的定义

English:
structure AbelianStruct
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (12):
    - kernelFork : KernelFork f
    - isLimitKernelFork : IsLimit kernelFork
    - cokernelCofork : CokernelCofork f
    - isColimitCokernelCofork : IsColimit cokernelCofork
    - image : C
    - imageπ : X ⟶ image
    - ι_imageπ : kernelFork.ι ≫ imageπ = 0  [default: by cat_disch]
    - imageIsCokernel : IsColimit (CokernelCofork.ofπ _ ι_imageπ)
    - imageι : image ⟶ Y
    - imageι_π : imageι ≫ cokernelCofork.π = 0  [default: by cat_disch]
    - imageIsKernel : IsLimit (KernelFork.ofι _ imageι_π)
    - fac : imageπ ≫ imageι = f  [default: by cat_disch]

中文:
结构 交换结构
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (12 个):
    - kernelFork : 核叉 f
    - isLimitKernelFork : 是极限 kernelFork
    - cokernelCofork : 余核余叉 f
    - isColimitCokernelCofork : 是余极限 cokernelCofork
    - image : C
    - imageπ : X ⟶ 像
    - ι_imageπ : kernelFork.ι ≫ imageπ = 0  [默认: by cat_disch]
    - imageIsCokernel : 是余极限 (余核余叉.ofπ _ ι_imageπ)
    - imageι : 像 ⟶ Y
    - imageι_π : imageι ≫ cokernelCofork.π = 0  [默认: by cat_disch]
    - imageIsKernel : 是极限 (核叉.ofι _ imageι_π)
    - fac : imageπ ≫ imageι = f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure AbelianStruct {X Y : C} (f : X ⟶ Y) where
  /-- a limit kernel fork of `f` -/
  kernelFork : KernelFork f
  /-- the kernel fork is a limit -/
  isLimitKernelFork : IsLimit kernelFork
  /-- a colimit cokernel cofork of `f` -/
  cokernelCofork : CokernelCofork f
  /-- the cokernel cofork is a a limit -/
  isColimitCokernelCofork : IsColimit cokernelCofork
  /-- the image of `f` -/
  image : C
  /-- the projection to the image -/
  imageπ : X ⟶ image
  ι_imageπ : kernelFork.ι ≫ imageπ = 0 := by cat_disch
  /-- the image is a cokernel -/
  imageIsCokernel : IsColimit (CokernelCofork.ofπ _ ι_imageπ)
  /-- the inclusion of the image -/
  imageι : image ⟶ Y
  imageι_π : imageι ≫ cokernelCofork.π = 0 := by cat_disch
  /-- the image is a kernel -/
  imageIsKernel : IsLimit (KernelFork.ofι _ imageι_π)
  fac : imageπ ≫ imageι = f := by cat_disch

namespace AbelianStruct

attribute [reassoc (attr := simp)] ι_imageπ imageι_π fac

end AbelianStruct

set_option backward.isDefEq.respectTransparency false in
/-- Constructor for abelian categories. We assume that the category `C` is
preadditive, has finite products, and that any morphism `f : X ⟶ Y` has
a kernel `i : K ⟶ X`, a cokernel `p : Y ⟶ Q` such that `f` factors as `f = π ≫ ι`
where `π : X ⟶ I` is a cokernel of `i` and `ι : I ⟶ Y` is a kernel of `p`.
This assumption is packaged in a structure `AbelianStruct f`. -/
@[instance_reducible]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: [HasFiniteProducts C]
  body: ⟨fun f => ⟨_, (h f).some.isLimitKernelFork⟩⟩
  has_cokernels := ⟨fun f => ⟨_, (h f).some.isColimitCokernelCofork⟩⟩
  normalMonoOfMono f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      Z := hf.cokernelCofork.pt
      g := hf.cokernelCofork.π
      w := by simp
      isLimit :=
        have : IsIso hf.imageπ :=
          CokernelCofork.IsColimit.isIso_π _ hf.imageIsCokernel (by simp [← cancel_mono f])
        IsLimit.ofIsoLimit hf.imageIsKernel (Fork.ext (asIso hf.imageπ)).symm }⟩
  normalEpiOfEpi f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      W := hf.kernelFork.pt
      g := hf.kernelFork.ι
      w := by simp
      isColimit :=
        have : IsIso hf.imageι :=
          KernelFork.IsLimit.isIso_ι _ hf.imageIsKernel (by simp [← cancel_epi f])
        IsColimit.ofIsoColimit hf.imageIsCokernel (Cofork.ext (asIso hf.imageι)) }⟩

中文:
定义 mk'
  签名: [有FiniteProducts C]
  定义体: ⟨fun f => ⟨_, (h f).some.isLimitKernelFork⟩⟩
  has_cokernels := ⟨fun f => ⟨_, (h f).some.isColimitCokernelCofork⟩⟩
  normalMonoOfMono f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      Z := hf.cokernelCofork.pt
      g := hf.cokernelCofork.π
      w := by simp
      isLimit :=
        have : IsIso hf.imageπ :=
          CokernelCofork.IsColimit.isIso_π _ hf.imageIsCokernel (by simp [← cancel_mono f])
        IsLimit.ofIsoLimit hf.imageIsKernel (Fork.ext (asIso hf.imageπ)).symm }⟩
  normalEpiOfEpi f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      W := hf.kernelFork.pt
      g := hf.kernelFork.ι
      w := by simp
      isColimit :=
        have : IsIso hf.imageι :=
          KernelFork.IsLimit.isIso_ι _ hf.imageIsKernel (by simp [← cancel_epi f])
        IsColimit.ofIsoColimit hf.imageIsCokernel (Cofork.ext (asIso hf.imageι)) }⟩

Depends on / 依赖: isLimitKernelFork, some.isLimitKernelFork
-/
noncomputable def mk' [HasFiniteProducts C]
    (h : forall ⦃X Y : C⦄ (f : X ⟶ Y), Nonempty (AbelianStruct f)) :
    Abelian C where
  has_kernels := ⟨fun f => ⟨_, (h f).some.isLimitKernelFork⟩⟩
  has_cokernels := ⟨fun f => ⟨_, (h f).some.isColimitCokernelCofork⟩⟩
  normalMonoOfMono f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      Z := hf.cokernelCofork.pt
      g := hf.cokernelCofork.π
      w := by simp
      isLimit :=
        have : IsIso hf.imageπ :=
          CokernelCofork.IsColimit.isIso_π _ hf.imageIsCokernel (by simp [← cancel_mono f])
        IsLimit.ofIsoLimit hf.imageIsKernel (Fork.ext (asIso hf.imageπ)).symm }⟩
  normalEpiOfEpi f _ := by
    obtain ⟨hf⟩ := h f
    exact ⟨{
      W := hf.kernelFork.pt
      g := hf.kernelFork.ι
      w := by simp
      isColimit :=
        have : IsIso hf.imageι :=
          KernelFork.IsLimit.isIso_ι _ hf.imageIsKernel (by simp [← cancel_epi f])
        IsColimit.ofIsoColimit hf.imageIsCokernel (Cofork.ext (asIso hf.imageι)) }⟩

end CategoryTheory.Abelian
