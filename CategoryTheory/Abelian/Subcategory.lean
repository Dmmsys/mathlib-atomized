/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Subcategories of abelian categories

Let `C` be an abelian category. Given `P : ObjectProperty C` which contains
zero, is closed under kernels, cokernels and finite products, we show that the
full subcategory defined by `P` is abelian.

-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] (P : ObjectProperty C)

/--
lemma `preservesMonomorphisms_ι_of_isNormalEpiCategory` / 引理 `preservesMonomorphisms_ι_of_isNormalEpiCategory`

English:
lemma preservesMonomorphisms_ι_of_isNormalEpiCategory
  statement: [HasZeroMorphisms C] [HasFiniteCoproducts C]
  proof: have := P.preservesKernels_ι
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels P.ι

中文:
引理 preservesMonomorphisms_ι_of_isNormalEpiCategory
  结论: [HasZeroMorphisms C] [HasFiniteCoproducts C]
  证明: have := P.preservesKernels_ι
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels P.ι

Depends on / 依赖: NormalEpiCategory, NormalEpiCategory.preservesMonomorphisms_of_preservesKernels, P.preservesKernels_, preservesMonomorphisms_of_preservesKernels
-/
lemma preservesMonomorphisms_ι_of_isNormalEpiCategory [HasZeroMorphisms C] [HasFiniteCoproducts C]
    [HasKernels C] [HasCokernels C] [IsNormalEpiCategory C] [HasZeroObject C] [P.ContainsZero]
    [P.IsClosedUnderKernels] : P.ι.PreservesMonomorphisms :=
  have := P.preservesKernels_ι
  NormalEpiCategory.preservesMonomorphisms_of_preservesKernels P.ι

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Abelian
  signature: C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
  body: have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    ⟨{Z := .mk _ (P.prop_cokernel f.hom X.property Y.property)
      g := P.homMk (cokernel.π f.hom)
      w := by cat_disch
      isLimit := isLimitOfReflects P.ι ((KernelFork.isLimitMapConeEquiv _ _).symm
        (Abelian.monoIsKernelOfCoke

中文:
实例 [Abelian
  签名: C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
  定义体: have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    ⟨{Z := .mk _ (P.prop_cokernel f.hom X.property Y.property)
      g := P.homMk (cokernel.π f.hom)
      w := by cat_disch
      isLimit := isLimitOfReflects P.ι ((KernelFork.isLimitMapConeEquiv _ _).symm
        (Abelian.monoIsKernelOfCoke

Depends on / 依赖: Abelian, Abelian.monoIsKernelOfCokernel, KernelFork, KernelFork.isLimitMapConeEquiv, P.homMk, P.preservesMonomorphisms_, P.prop_cokernel, X.property, Y.property, cat_disch, cokernel, cokernelIsCokernel, f.hom, isLimit, isLimitMapConeEquiv, isLimitOfReflects, monoIsKernelOfCokernel, prop_cokernel, property
-/
instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
    IsNormalMonoCategory P.FullSubcategory where
  normalMonoOfMono {X Y} f :=
    have := P.preservesMonomorphisms_ι_of_isNormalEpiCategory
    ⟨{Z := .mk _ (P.prop_cokernel f.hom X.property Y.property)
      g := P.homMk (cokernel.π f.hom)
      w := by cat_disch
      isLimit := isLimitOfReflects P.ι ((KernelFork.isLimitMapConeEquiv _ _).symm
        (Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel (P.ι.map f)) :))}⟩

/--
lemma `preservesEpimorphisms_ι_of_isNormalMonoCategory` / 引理 `preservesEpimorphisms_ι_of_isNormalMonoCategory`

English:
lemma preservesEpimorphisms_ι_of_isNormalMonoCategory
  statement: [HasZeroMorphisms C] [HasFiniteProducts C]
  proof: have := P.preservesCokernels_ι
  NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels P.ι

中文:
引理 preservesEpimorphisms_ι_of_isNormalMonoCategory
  结论: [HasZeroMorphisms C] [HasFiniteProducts C]
  证明: have := P.preservesCokernels_ι
  NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels P.ι

Depends on / 依赖: NormalMonoCategory, NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels, P.preservesCokernels_, preservesEpimorphisms_of_preservesCokernels
-/
lemma preservesEpimorphisms_ι_of_isNormalMonoCategory [HasZeroMorphisms C] [HasFiniteProducts C]
    [HasKernels C] [HasCokernels C] [IsNormalMonoCategory C] [HasZeroObject C] [P.ContainsZero]
    [P.IsClosedUnderCokernels] : P.ι.PreservesEpimorphisms :=
  have := P.preservesCokernels_ι
  NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels P.ι

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Abelian
  signature: C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
  body: have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
    ⟨{W := .mk _ (P.prop_kernel f.hom X.property Y.property)
      g := P.homMk (kernel.ι f.hom)
      w := by cat_disch
      isColimit := isColimitOfReflects P.ι ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (Abelian.epiIsCoker

中文:
实例 [Abelian
  签名: C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
  定义体: have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
    ⟨{W := .mk _ (P.prop_kernel f.hom X.property Y.property)
      g := P.homMk (kernel.ι f.hom)
      w := by cat_disch
      isColimit := isColimitOfReflects P.ι ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (Abelian.epiIsCoker

Depends on / 依赖: Abelian, Abelian.epiIsCokernelOfKernel, CokernelCofork, CokernelCofork.isColimitMapCoconeEquiv, P.homMk, P.preservesEpimorphisms_, P.prop_kernel, X.property, Y.property, cat_disch, epiIsCokernelOfKernel, f.hom, isColimit, isColimitMapCoconeEquiv, isColimitOfReflects, kernel, kernelIsKernel, prop_kernel, property
-/
instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] :
    IsNormalEpiCategory P.FullSubcategory where
  normalEpiOfEpi {X Y} f :=
    have := P.preservesEpimorphisms_ι_of_isNormalMonoCategory
    ⟨{W := .mk _ (P.prop_kernel f.hom X.property Y.property)
      g := P.homMk (kernel.ι f.hom)
      w := by cat_disch
      isColimit := isColimitOfReflects P.ι ((CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (P.ι.map f)) :))}⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Abelian
  signature: C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]

中文:
实例 [Abelian
  签名: C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
-/
instance [Abelian C] [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderFiniteProducts] : Abelian P.FullSubcategory where

end CategoryTheory.ObjectProperty
