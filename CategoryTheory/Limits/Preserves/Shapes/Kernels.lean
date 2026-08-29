/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Preserving (co)kernels

Constructions to relate the notions of preserving (co)kernels and reflecting (co)kernels
to concrete (co)forks.

In particular, we show that `kernel_comparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,0`, as well as the dual result.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

namespace CategoryTheory.Limits

namespace KernelFork

variable {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[reassoc (attr := simp)]
/--
lemma `map_condition` / 引理 `map_condition`

English:
lemma map_condition
  statement: G.map c.ι ≫ G.map f = 0
  proof: by
  rw [← G.map_comp]; rw [c.condition]; rw [G.map_zero]

中文:
引理 map_condition
  结论: G.map c.ι ≫ G.map f = 0
  证明: by
  rw [← G.map_comp]; rw [c.condition]; rw [G.map_zero]

Depends on / 依赖: G.map_comp, G.map_zero, c.condition, condition, map_comp, map_zero
-/
lemma map_condition : G.map c.ι ≫ G.map f = 0 := by
  rw [← G.map_comp]; rw [c.condition]; rw [G.map_zero]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : KernelFork (G.map f)
  body: KernelFork.ofι (G.map c.ι) (c.map_condition G)

@[simp]

中文:
定义 map
  签名: : 核叉 (G.map f)
  定义体: KernelFork.ofι (G.map c.ι) (c.map_condition G)

@[simp]

Depends on / 依赖: G.map, KernelFork, KernelFork.of, c.map_condition, map_condition
-/
def map : KernelFork (G.map f) :=
  KernelFork.ofι (G.map c.ι) (c.map_condition G)

@[simp]
/--
lemma `map_ι` / 引理 `map_ι`

English:
lemma map_ι
  statement: (c.map G).ι = G.map c.ι
  proof: rfl

中文:
引理 map_ι
  结论: (c.map G).ι = G.map c.ι
  证明: rfl
-/
lemma map_ι : (c.map G).ι = G.map c.ι := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitMapConeEquiv` / `isLimitMapConeEquiv` 的定义

English:
definition isLimitMapConeEquiv
  signature: :
  body: by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

中文:
定义 isLimitMapConeEquiv
  签名: :
  定义体: by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, cat_disch, equivIsoLimit, parallelPair, parallelPair.ext, postcomposeHomEquiv, symm.trans
-/
def isLimitMapConeEquiv :
    IsLimit (G.mapCone c) ≃ IsLimit (c.map G) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

/--
Definition of `mapIsLimit` / `mapIsLimit` 的定义

English:
definition mapIsLimit
  signature: (hc : IsLimit c) (G : C ⥤ D)
  body: c.isLimitMapConeEquiv G (isLimitOfPreserves G hc)

中文:
定义 mapIsLimit
  签名: (hc : 是极限 c) (G : C ⥤ D)
  定义体: c.isLimitMapConeEquiv G (isLimitOfPreserves G hc)

Depends on / 依赖: c.isLimitMapConeEquiv, isLimitMapConeEquiv, isLimitOfPreserves
-/
def mapIsLimit (hc : IsLimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesLimit (parallelPair f 0) G] :
    IsLimit (c.map G) :=
  c.isLimitMapConeEquiv G (isLimitOfPreserves G hc)

end KernelFork

section Kernels

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = 0)

/--
Definition of `isLimitMapConeForkEquiv'` / `isLimitMapConeForkEquiv'` 的定义

English:
definition isLimitMapConeForkEquiv'
  signature: :
  body: KernelFork.isLimitMapConeEquiv _ _

中文:
定义 isLimitMapConeForkEquiv'
  签名: :
  定义体: KernelFork.isLimitMapConeEquiv _ _

Depends on / 依赖: KernelFork, KernelFork.isLimitMapConeEquiv, isLimitMapConeEquiv
-/
def isLimitMapConeForkEquiv' :
    IsLimit (G.mapCone (KernelFork.ofι h w)) ≃
      IsLimit
        (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Fork (G.map f) 0) :=
  KernelFork.isLimitMapConeEquiv _ _

/--
Definition of `isLimitForkMapOfIsLimit'` / `isLimitForkMapOfIsLimit'` 的定义

English:
definition isLimitForkMapOfIsLimit'
  signature: [PreservesLimit (parallelPair f 0) G]
  body: isLimitMapConeForkEquiv' G w (isLimitOfPreserves G l)

中文:
定义 isLimitForkMapOfIsLimit'
  签名: [保持极限 (parallelPair f 0) G]
  定义体: isLimitMapConeForkEquiv' G w (isLimitOfPreserves G l)

Depends on / 依赖: isLimitMapConeForkEquiv, isLimitOfPreserves
-/
def isLimitForkMapOfIsLimit' [PreservesLimit (parallelPair f 0) G]
    (l : IsLimit (KernelFork.ofι h w)) :
    IsLimit
      (KernelFork.ofι (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitMapConeForkEquiv' G w (isLimitOfPreserves G l)

variable (f)
variable [HasKernel f]

/--
Definition of `isLimitOfHasKernelOfPreservesLimit` / `isLimitOfHasKernelOfPreservesLimit` 的定义

English:
definition isLimitOfHasKernelOfPreservesLimit
  signature: [PreservesLimit (parallelPair f 0) G]
  body: isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)

中文:
定义 isLimitOfHasKernelOfPreservesLimit
  签名: [保持极限 (parallelPair f 0) G]
  定义体: isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)

Depends on / 依赖: condition, isLimitForkMapOfIsLimit, kernel, kernel.condition, kernelIsKernel
-/
def isLimitOfHasKernelOfPreservesLimit [PreservesLimit (parallelPair f 0) G] :
    IsLimit
      (Fork.ofι (G.map (kernel.ι f))
          (by simp only [← G.map_comp, kernel.condition, comp_zero, Functor.map_zero]) :
        Fork (G.map f) 0) :=
  isLimitForkMapOfIsLimit' G (kernel.condition f) (kernelIsKernel f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimit
  signature: (parallelPair f 0) G] : HasKernel (G.map f) where
  body: ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

中文:
实例 [保持极限
  签名: (parallelPair f 0) G] : HasKernel (G.map f) where
  定义体: ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

Depends on / 依赖: isLimitOfHasKernelOfPreservesLimit
-/
instance [PreservesLimit (parallelPair f 0) G] : HasKernel (G.map f) where
  exists_limit := ⟨⟨_, isLimitOfHasKernelOfPreservesLimit G f⟩⟩

variable [HasKernel (G.map f)]

/--
lemma `PreservesKernel.of_iso_comparison` / 引理 `PreservesKernel.of_iso_comparison`

English:
lemma PreservesKernel.of_iso_comparison
  given: [i : IsIso (kernelComparison f G)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i

中文:
引理 PreservesKernel.of_iso_comparison
  条件: [i : 是同构 (kernelComparison f G)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i

Depends on / 依赖: G.map, IsLimit, IsLimit.ofPointIso, condition, isLimitMapConeForkEquiv, kernel, kernel.condition, kernelIsKernel, ofPointIso, preservesLimit_of_preserves_limit_cone
-/
lemma PreservesKernel.of_iso_comparison [i : IsIso (kernelComparison f G)] :
    PreservesLimit (parallelPair f 0) G := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  apply (isLimitMapConeForkEquiv' G (kernel.condition f)).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (kernelIsKernel (G.map f)) i

variable [PreservesLimit (parallelPair f 0) G]

/--
Definition of `PreservesKernel.iso` / `PreservesKernel.iso` 的定义

English:
definition PreservesKernel.iso
  signature: : G.obj (kernel f) ≅ kernel (G.map f)
  body: IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)

@[reassoc (attr := simp)]

中文:
定义 PreservesKernel.iso
  签名: : G.obj (kernel f) ≅ kernel (G.map f)
  定义体: IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, isLimitOfHasKernelOfPreservesLimit, limit.isLimit
-/
def PreservesKernel.iso : G.obj (kernel f) ≅ kernel (G.map f) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasKernelOfPreservesLimit G f) (limit.isLimit _)

@[reassoc (attr := simp)]
/--
theorem `PreservesKernel.iso_inv_ι` / 定理 `PreservesKernel.iso_inv_ι`

English:
theorem PreservesKernel.iso_inv_ι
  proof: IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOfHasKernelOfPreservesLimit G f)
    (limit.isLimit _) (WalkingParallelPair.zero)

中文:
定理 PreservesKernel.iso_inv_ι
  证明: IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOfHasKernelOfPreservesLimit G f)
    (limit.isLimit _) (WalkingParallelPair.zero)

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingParallelPair, WalkingParallelPair.zero, conePointUniqueUpToIso_inv_comp, isLimit, isLimitOfHasKernelOfPreservesLimit, limit.isLimit
-/
theorem PreservesKernel.iso_inv_ι :
    (PreservesKernel.iso G f).inv ≫ G.map (kernel.ι f) = kernel.ι (G.map f) :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOfHasKernelOfPreservesLimit G f)
    (limit.isLimit _) (WalkingParallelPair.zero)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `PreservesKernel.iso_hom` / 定理 `PreservesKernel.iso_hom`

English:
theorem PreservesKernel.iso_hom
  statement: (PreservesKernel.iso G f).hom = kernelComparison f G
  proof: by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]

中文:
定理 PreservesKernel.iso_hom
  结论: (PreservesKernel.iso G f).hom = kernelComparison f G
  证明: by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]

Depends on / 依赖: PreservesKernel, PreservesKernel.iso, cancel_mono, kernel
-/
theorem PreservesKernel.iso_hom : (PreservesKernel.iso G f).hom = kernelComparison f G := by
  rw [← cancel_mono (kernel.ι _)]
  simp [PreservesKernel.iso]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (kernelComparison f G)
  body: by
  rw [← PreservesKernel.iso_hom]
  infer_instance

@[reassoc]

中文:
实例 :
  签名: 是同构 (kernelComparison f G)
  定义体: by
  rw [← PreservesKernel.iso_hom]
  infer_instance

@[reassoc]

Depends on / 依赖: PreservesKernel, PreservesKernel.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (kernelComparison f G) := by
  rw [← PreservesKernel.iso_hom]
  infer_instance

@[reassoc]
/--
theorem `kernel_map_comp_preserves_kernel_iso_inv` / 定理 `kernel_map_comp_preserves_kernel_iso_inv`

English:
theorem kernel_map_comp_preserves_kernel_iso_inv
  statement: {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
  proof: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [PreservesKernel.iso_hom]; rw [Iso.eq_inv_comp]; rw [PreservesKernel.iso_hom]; rw [kernelComparison_comp_kernel_map]

中文:
定理 kernel_map_comp_preserves_kernel_iso_inv
  结论: {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
  证明: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [PreservesKernel.iso_hom]; rw [Iso.eq_inv_comp]; rw [PreservesKernel.iso_hom]; rw [kernelComparison_comp_kernel_map]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.eq_inv_comp, PreservesKernel, PreservesKernel.iso_hom, comp_inv_eq, eq_inv_comp, iso_hom, kernelComparison_comp_kernel_map
-/
theorem kernel_map_comp_preserves_kernel_iso_inv {X' Y' : C} (g : X' ⟶ Y') [HasKernel g]
    [HasKernel (G.map g)] [PreservesLimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        (PreservesKernel.iso G _).inv =
      (PreservesKernel.iso G _).inv ≫ G.map (kernel.map f g p q hpq) := by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [PreservesKernel.iso_hom]; rw [Iso.eq_inv_comp]; rw [PreservesKernel.iso_hom]; rw [kernelComparison_comp_kernel_map]

end Kernels

namespace CokernelCofork

variable {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
  (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

@[reassoc (attr := simp)]
/--
lemma `map_condition` / 引理 `map_condition`

English:
lemma map_condition
  statement: G.map f ≫ G.map c.π = 0
  proof: by
  rw [← G.map_comp]; rw [c.condition]; rw [G.map_zero]

中文:
引理 map_condition
  结论: G.map f ≫ G.map c.π = 0
  证明: by
  rw [← G.map_comp]; rw [c.condition]; rw [G.map_zero]

Depends on / 依赖: G.map_comp, G.map_zero, c.condition, condition, map_comp, map_zero
-/
lemma map_condition : G.map f ≫ G.map c.π = 0 := by
  rw [← G.map_comp]; rw [c.condition]; rw [G.map_zero]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : CokernelCofork (G.map f)
  body: CokernelCofork.ofπ (G.map c.π) (c.map_condition G)

@[simp]

中文:
定义 map
  签名: : 余核余叉 (G.map f)
  定义体: CokernelCofork.ofπ (G.map c.π) (c.map_condition G)

@[simp]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, G.map, c.map_condition, map_condition
-/
def map : CokernelCofork (G.map f) :=
  CokernelCofork.ofπ (G.map c.π) (c.map_condition G)

@[simp]
/--
lemma `map_π` / 引理 `map_π`

English:
lemma map_π
  statement: (c.map G).π = G.map c.π
  proof: rfl

中文:
引理 map_π
  结论: (c.map G).π = G.map c.π
  证明: rfl
-/
lemma map_π : (c.map G).π = G.map c.π := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitMapCoconeEquiv` / `isColimitMapCoconeEquiv` 的定义

English:
definition isColimitMapCoconeEquiv
  signature: :
  body: by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cocone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

中文:
定义 isColimitMapCoconeEquiv
  签名: :
  定义体: by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cocone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, cat_disch, equivIsoColimit, parallelPair, parallelPair.ext, precomposeHomEquiv, symm.trans
-/
def isColimitMapCoconeEquiv :
    IsColimit (G.mapCocone c) ≃ IsColimit (c.map G) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_ <;> simp
  exact Cocone.ext (Iso.refl _) (by rintro (_ | _) <;> cat_disch)

/--
Definition of `mapIsColimit` / `mapIsColimit` 的定义

English:
definition mapIsColimit
  signature: (hc : IsColimit c) (G : C ⥤ D)
  body: c.isColimitMapCoconeEquiv G (isColimitOfPreserves G hc)

中文:
定义 mapIsColimit
  签名: (hc : 是余极限 c) (G : C ⥤ D)
  定义体: c.isColimitMapCoconeEquiv G (isColimitOfPreserves G hc)

Depends on / 依赖: c.isColimitMapCoconeEquiv, isColimitMapCoconeEquiv, isColimitOfPreserves
-/
def mapIsColimit (hc : IsColimit c) (G : C ⥤ D)
    [Functor.PreservesZeroMorphisms G] [PreservesColimit (parallelPair f 0) G] :
    IsColimit (c.map G) :=
  c.isColimitMapCoconeEquiv G (isColimitOfPreserves G hc)

end CokernelCofork

section Cokernels

variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]
  {X Y Z : C} {f : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = 0)

/--
Definition of `isColimitMapCoconeCoforkEquiv'` / `isColimitMapCoconeCoforkEquiv'` 的定义

English:
definition isColimitMapCoconeCoforkEquiv'
  signature: :
  body: CokernelCofork.isColimitMapCoconeEquiv _ _

中文:
定义 isColimitMapCoconeCoforkEquiv'
  签名: :
  定义体: CokernelCofork.isColimitMapCoconeEquiv _ _

Depends on / 依赖: CokernelCofork, CokernelCofork.isColimitMapCoconeEquiv, isColimitMapCoconeEquiv
-/
def isColimitMapCoconeCoforkEquiv' :
    IsColimit (G.mapCocone (CokernelCofork.ofπ h w)) ≃
      IsColimit
        (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
          Cofork (G.map f) 0) :=
  CokernelCofork.isColimitMapCoconeEquiv _ _

/--
Definition of `isColimitCoforkMapOfIsColimit'` / `isColimitCoforkMapOfIsColimit'` 的定义

English:
definition isColimitCoforkMapOfIsColimit'
  signature: [PreservesColimit (parallelPair f 0) G]
  body: isColimitMapCoconeCoforkEquiv' G w (isColimitOfPreserves G l)

中文:
定义 isColimitCoforkMapOfIsColimit'
  签名: [保持余极限 (parallelPair f 0) G]
  定义体: isColimitMapCoconeCoforkEquiv' G w (isColimitOfPreserves G l)

Depends on / 依赖: isColimitMapCoconeCoforkEquiv, isColimitOfPreserves
-/
def isColimitCoforkMapOfIsColimit' [PreservesColimit (parallelPair f 0) G]
    (l : IsColimit (CokernelCofork.ofπ h w)) :
    IsColimit
      (CokernelCofork.ofπ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitMapCoconeCoforkEquiv' G w (isColimitOfPreserves G l)

variable (f)
variable [HasCokernel f]

/--
Definition of `isColimitOfHasCokernelOfPreservesColimit` / `isColimitOfHasCokernelOfPreservesColimit` 的定义

English:
definition isColimitOfHasCokernelOfPreservesColimit
  signature: [PreservesColimit (parallelPair f 0) G]
  body: isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)

中文:
定义 isColimitOfHasCokernelOfPreservesColimit
  签名: [保持余极限 (parallelPair f 0) G]
  定义体: isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)

Depends on / 依赖: cokernel, cokernel.condition, cokernelIsCokernel, condition, isColimitCoforkMapOfIsColimit
-/
def isColimitOfHasCokernelOfPreservesColimit [PreservesColimit (parallelPair f 0) G] :
    IsColimit
      (Cofork.ofπ (G.map (cokernel.π f))
          (by simp only [← G.map_comp, cokernel.condition, zero_comp, Functor.map_zero]) :
        Cofork (G.map f) 0) :=
  isColimitCoforkMapOfIsColimit' G (cokernel.condition f) (cokernelIsCokernel f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesColimit
  signature: (parallelPair f 0) G] : HasCokernel (G.map f) where
  body: ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

中文:
实例 [保持余极限
  签名: (parallelPair f 0) G] : HasCokernel (G.map f) where
  定义体: ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

Depends on / 依赖: forget, isColimitOfHasCokernelOfPreservesColimit
-/
instance [PreservesColimit (parallelPair f 0) G] : HasCokernel (G.map f) where
  exists_colimit := ⟨⟨_, isColimitOfHasCokernelOfPreservesColimit G f⟩⟩

variable [HasCokernel (G.map f)]

/--
lemma `PreservesCokernel.of_iso_comparison` / 引理 `PreservesCokernel.of_iso_comparison`

English:
lemma PreservesCokernel.of_iso_comparison
  given: [i : IsIso (cokernelComparison f G)]
  proof: by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  apply (isColimitMapCoconeCoforkEquiv' G (cokernel.condition f)).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (cokernelIsCokernel (G.map f)) i

中文:
引理 PreservesCokernel.of_iso_comparison
  条件: [i : 是同构 (cokernelComparison f G)]
  证明: by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  apply (isColimitMapCoconeCoforkEquiv' G (cokernel.condition f)).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (cokernelIsCokernel (G.map f)) i

Depends on / 依赖: G.map, IsColimit, IsColimit.ofPointIso, cokernel, cokernel.condition, cokernelIsCokernel, condition, isColimitMapCoconeCoforkEquiv, ofPointIso, preservesColimit_of_preserves_colimit_cocone
-/
lemma PreservesCokernel.of_iso_comparison [i : IsIso (cokernelComparison f G)] :
    PreservesColimit (parallelPair f 0) G := by
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  apply (isColimitMapCoconeCoforkEquiv' G (cokernel.condition f)).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _ (cokernelIsCokernel (G.map f)) i

variable [PreservesColimit (parallelPair f 0) G]

/--
Definition of `PreservesCokernel.iso` / `PreservesCokernel.iso` 的定义

English:
definition PreservesCokernel.iso
  signature: : G.obj (cokernel f) ≅ cokernel (G.map f)
  body: IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _)

@[reassoc (attr := simp)]

中文:
定义 PreservesCokernel.iso
  签名: : G.obj (cokernel f) ≅ cokernel (G.map f)
  定义体: IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfHasCokernelOfPreservesColimit
-/
def PreservesCokernel.iso : G.obj (cokernel f) ≅ cokernel (G.map f) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _)

@[reassoc (attr := simp)]
/--
theorem `PreservesCokernel.π_iso_hom` / 定理 `PreservesCokernel.π_iso_hom`

English:
theorem PreservesCokernel.π_iso_hom
  statement: G.map (cokernel.π f) ≫ (iso G f).hom = cokernel.π (G.map f)
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _) (WalkingParallelPair.one)

中文:
定理 PreservesCokernel.π_iso_hom
  结论: G.map (cokernel.π f) ≫ (iso G f).hom = cokernel.π (G.map f)
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _) (WalkingParallelPair.one)

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, WalkingParallelPair, WalkingParallelPair.one, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, isColimit, isColimitOfHasCokernelOfPreservesColimit
-/
theorem PreservesCokernel.π_iso_hom : G.map (cokernel.π f) ≫ (iso G f).hom = cokernel.π (G.map f) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitOfHasCokernelOfPreservesColimit G f)
    (colimit.isColimit _) (WalkingParallelPair.one)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `PreservesCokernel.iso_inv` / 定理 `PreservesCokernel.iso_inv`

English:
theorem PreservesCokernel.iso_inv
  statement: (PreservesCokernel.iso G f).inv = cokernelComparison f G
  proof: by
  rw [← cancel_epi (cokernel.π _)]
  simp [PreservesCokernel.iso]

中文:
定理 PreservesCokernel.iso_inv
  结论: (PreservesCokernel.iso G f).inv = cokernelComparison f G
  证明: by
  rw [← cancel_epi (cokernel.π _)]
  simp [PreservesCokernel.iso]

Depends on / 依赖: PreservesCokernel, PreservesCokernel.iso, cancel_epi, cokernel
-/
theorem PreservesCokernel.iso_inv : (PreservesCokernel.iso G f).inv = cokernelComparison f G := by
  rw [← cancel_epi (cokernel.π _)]
  simp [PreservesCokernel.iso]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (cokernelComparison f G)
  body: by
  rw [← PreservesCokernel.iso_inv]
  infer_instance

@[reassoc]

中文:
实例 :
  签名: 是同构 (cokernelComparison f G)
  定义体: by
  rw [← PreservesCokernel.iso_inv]
  infer_instance

@[reassoc]

Depends on / 依赖: PreservesCokernel, PreservesCokernel.iso_inv, infer_instance, iso_inv
-/
instance : IsIso (cokernelComparison f G) := by
  rw [← PreservesCokernel.iso_inv]
  infer_instance

@[reassoc]
/--
theorem `preserves_cokernel_iso_comp_cokernel_map` / 定理 `preserves_cokernel_iso_comp_cokernel_map`

English:
theorem preserves_cokernel_iso_comp_cokernel_map
  statement: {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
  proof: by
  rw [← Iso.comp_inv_eq]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [PreservesCokernel.iso_inv]; rw [cokernel_map_comp_cokernelComparison]; rw [PreservesCokernel.iso_inv]

中文:
定理 preserves_cokernel_iso_comp_cokernel_map
  结论: {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
  证明: by
  rw [← Iso.comp_inv_eq]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [PreservesCokernel.iso_inv]; rw [cokernel_map_comp_cokernelComparison]; rw [PreservesCokernel.iso_inv]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.eq_inv_comp, PreservesCokernel, PreservesCokernel.iso_inv, cokernel_map_comp_cokernelComparison, comp_inv_eq, eq_inv_comp, iso_inv
-/
theorem preserves_cokernel_iso_comp_cokernel_map {X' Y' : C} (g : X' ⟶ Y') [HasCokernel g]
    [HasCokernel (G.map g)] [PreservesColimit (parallelPair g 0) G] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    (PreservesCokernel.iso G _).hom ≫
        cokernel.map (G.map f) (G.map g) (G.map p) (G.map q)
          (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (cokernel.map f g p q hpq) ≫ (PreservesCokernel.iso G _).hom := by
  rw [← Iso.comp_inv_eq]; rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [PreservesCokernel.iso_inv]; rw [cokernel_map_comp_cokernelComparison]; rw [PreservesCokernel.iso_inv]

end Cokernels

variable (X Y : C) (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `preservesKernel_zero` / 实例 `preservesKernel_zero`

English:
instance preservesKernel_zero
  signature: :
  body: ⟨by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))⟩

中文:
实例 preservesKernel_zero
  签名: :
  定义体: ⟨by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))⟩

Depends on / 依赖: Fork.ext, G.mapIso, G.map_zero, IsLimit, IsLimit.ofIsoLimit, KernelFork, KernelFork.IsLimit.isIso_, KernelFork.IsLimit.ofId, KernelFork.isLimitMapConeEquiv, isLimitMapConeEquiv, mapIso, map_zero, ofIsoLimit
-/
instance preservesKernel_zero :
    PreservesLimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := KernelFork.IsLimit.isIso_ι c hc rfl
    refine (KernelFork.isLimitMapConeEquiv c G).symm ?_
    refine IsLimit.ofIsoLimit (KernelFork.IsLimit.ofId _ (G.map_zero _ _)) ?_
    exact (Fork.ext (G.mapIso (asIso (Fork.ι c))).symm (by simp))⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `preservesCokernel_zero` / 实例 `preservesCokernel_zero`

English:
instance preservesCokernel_zero
  signature: :
  body: ⟨by
    have := CokernelCofork.IsColimit.isIso_π c hc rfl
    refine (CokernelCofork.isColimitMapCoconeEquiv c G).symm ?_
    refine IsColimit.ofIsoColimit (CokernelCofork.IsColimit.ofId _ (G.map_zero _ _)) ?_
    exact (Cofork.ext (G.mapIso (asIso (Cofork.π c))) (by simp))⟩

中文:
实例 preservesCokernel_zero
  签名: :
  定义体: ⟨by
    have := CokernelCofork.IsColimit.isIso_π c hc rfl
    refine (CokernelCofork.isColimitMapCoconeEquiv c G).symm ?_
    refine IsColimit.ofIsoColimit (CokernelCofork.IsColimit.ofId _ (G.map_zero _ _)) ?_
    exact (Cofork.ext (G.mapIso (asIso (Cofork.π c))) (by simp))⟩

Depends on / 依赖: Cofork, Cofork.ext, CokernelCofork, CokernelCofork.IsColimit.isIso_, CokernelCofork.IsColimit.ofId, CokernelCofork.isColimitMapCoconeEquiv, G.mapIso, G.map_zero, IsColimit, IsColimit.ofIsoColimit, isColimitMapCoconeEquiv, mapIso, map_zero, ofIsoColimit
-/
noncomputable instance preservesCokernel_zero :
    PreservesColimit (parallelPair (0 : X ⟶ Y) 0) G where
  preserves {c} hc := ⟨by
    have := CokernelCofork.IsColimit.isIso_π c hc rfl
    refine (CokernelCofork.isColimitMapCoconeEquiv c G).symm ?_
    refine IsColimit.ofIsoColimit (CokernelCofork.IsColimit.ofId _ (G.map_zero _ _)) ?_
    exact (Cofork.ext (G.mapIso (asIso (Cofork.π c))) (by simp))⟩

variable {X Y}

/--
lemma `preservesKernel_zero'` / 引理 `preservesKernel_zero'`

English:
lemma preservesKernel_zero'
  given: (f : X ⟶ Y) (hf : f = 0)
  proof: by
  rw [hf]
  infer_instance

中文:
引理 preservesKernel_zero'
  条件: (f : X ⟶ Y) (hf : f = 0)
  证明: by
  rw [hf]
  infer_instance

Depends on / 依赖: infer_instance
-/
lemma preservesKernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesLimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

/--
lemma `preservesCokernel_zero'` / 引理 `preservesCokernel_zero'`

English:
lemma preservesCokernel_zero'
  given: (f : X ⟶ Y) (hf : f = 0)
  proof: by
  rw [hf]
  infer_instance

中文:
引理 preservesCokernel_zero'
  条件: (f : X ⟶ Y) (hf : f = 0)
  证明: by
  rw [hf]
  infer_instance

Depends on / 依赖: infer_instance
-/
lemma preservesCokernel_zero' (f : X ⟶ Y) (hf : f = 0) :
    PreservesColimit (parallelPair f 0) G := by
  rw [hf]
  infer_instance

section ZeroObject

variable [HasZeroObject C] [HasZeroObject D]

variable {X Y : C} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `mapZeroKernelFork` / `mapZeroKernelFork` 的定义

English:
definition mapZeroKernelFork
  signature: :
  body: Fork.ext G.mapZeroObject

中文:
定义 mapZeroKernelFork
  签名: :
  定义体: Fork.ext G.mapZeroObject

Depends on / 依赖: Fork.ext, G.mapZeroObject, mapZeroObject
-/
def mapZeroKernelFork :
    (kernel.zeroKernelFork f).map G ≅ (kernel.zeroKernelFork (G.map f)) :=
  Fork.ext G.mapZeroObject

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapZeroCokernelCofork` / `mapZeroCokernelCofork` 的定义

English:
definition mapZeroCokernelCofork
  signature: :
  body: Cofork.ext G.mapZeroObject

中文:
定义 mapZeroCokernelCofork
  签名: :
  定义体: Cofork.ext G.mapZeroObject

Depends on / 依赖: Cofork, Cofork.ext, G.mapZeroObject, mapZeroObject
-/
def mapZeroCokernelCofork :
    (cokernel.zeroCokernelCofork f).map G ≅ (cokernel.zeroCokernelCofork (G.map f)) :=
  Cofork.ext G.mapZeroObject

end ZeroObject

end CategoryTheory.Limits
