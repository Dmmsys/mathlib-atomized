/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Functors which preserves homology

If `F : C ⥤ D` is a functor between categories with zero morphisms, we shall
say that `F` preserves homology when `F` preserves both kernels and cokernels.
This typeclass is named `[F.PreservesHomology]`, and is automatically
satisfied when `F` preserves both finite limits and finite colimits.

If `S : ShortComplex C` and `[F.PreservesHomology]`, then there is an
isomorphism `S.mapHomologyIso F : (S.map F).homology ≅ F.obj S.homology`, which
is part of the natural isomorphism `homologyFunctorIso F` between the functors
`F.mapShortComplex ⋙ homologyFunctor D` and `homologyFunctor C ⋙ F`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

variable (F : C ⥤ D)

/--
Definition of `PreservesHomology` / `PreservesHomology` 的定义

English:
class PreservesHomology
  parameters: (F : C ⥤ D) [PreservesZeroMorphisms F]
  axioms and operations (2):
    - preservesKernels(⦃X Y) : C⦄ (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F  [default: by infer_instance]
    - preservesCokernels(⦃X Y) : C⦄ (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) F  [default: by infer_instance]

中文:
类 保持同调
  参数: (F : C ⥤ D) [保持ZeroMorphisms F]
  公理与运算 (2 个):
    - preservesKernels(⦃X Y) : C⦄ (f : X ⟶ Y) : 保持极限 (parallelPair f 0) F  [默认: by infer_instance]
    - preservesCokernels(⦃X Y) : C⦄ (f : X ⟶ Y) : 保持余极限 (parallelPair f 0) F  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class PreservesHomology (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  /-- the functor preserves kernels -/
  preservesKernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F := by
    infer_instance
  /-- the functor preserves cokernels -/
  preservesCokernels ⦃X Y : C⦄ (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) F := by
    infer_instance

variable [PreservesZeroMorphisms F]

/--
lemma `PreservesHomology.preservesKernel` / 引理 `PreservesHomology.preservesKernel`

English:
lemma PreservesHomology.preservesKernel
  given: [F.PreservesHomology] {X Y : C} (f : X ⟶ Y)
  proof: PreservesHomology.preservesKernels _

中文:
引理 保持同调.preservesKernel
  条件: [F.保持同调] {X Y : C} (f : X ⟶ Y)
  证明: PreservesHomology.preservesKernels _

Depends on / 依赖: PreservesHomology, PreservesHomology.preservesKernels, preservesKernels
-/
lemma PreservesHomology.preservesKernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesLimit (parallelPair f 0) F :=
  PreservesHomology.preservesKernels _

/--
lemma `PreservesHomology.preservesCokernel` / 引理 `PreservesHomology.preservesCokernel`

English:
lemma PreservesHomology.preservesCokernel
  given: [F.PreservesHomology] {X Y : C} (f : X ⟶ Y)
  proof: PreservesHomology.preservesCokernels _

中文:
引理 保持同调.preservesCokernel
  条件: [F.保持同调] {X Y : C} (f : X ⟶ Y)
  证明: PreservesHomology.preservesCokernels _

Depends on / 依赖: PreservesHomology, PreservesHomology.preservesCokernels, preservesCokernels
-/
lemma PreservesHomology.preservesCokernel [F.PreservesHomology] {X Y : C} (f : X ⟶ Y) :
    PreservesColimit (parallelPair f 0) F :=
  PreservesHomology.preservesCokernels _

/--
Instance `preservesHomologyOfExact` / 实例 `preservesHomologyOfExact`

English:
instance preservesHomologyOfExact

中文:
实例 preservesHomologyOfExact
-/
noncomputable instance preservesHomologyOfExact
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] : F.PreservesHomology where

end Functor

namespace ShortComplex

variable {S S₁ S₂ : ShortComplex C}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) (F : C ⥤ D)

/--
Definition of `IsPreservedBy` / `IsPreservedBy` 的定义

English:
class IsPreservedBy
  parameters: [F.PreservesZeroMorphisms]
  axioms and operations (2):
    - g : PreservesLimit (parallelPair S.g 0) F
    - f' : PreservesColimit (parallelPair h.f' 0) F

中文:
类 是PreservedBy
  参数: [F.保持ZeroMorphisms]
  公理与运算 (2 个):
    - g : 保持极限 (parallelPair S.g 0) F
    - f' : 保持余极限 (parallelPair h.f' 0) F
-/
class IsPreservedBy [F.PreservesZeroMorphisms] : Prop where
  /-- the functor preserves the kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
  g : PreservesLimit (parallelPair S.g 0) F
  /-- the functor preserves the cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
  f' : PreservesColimit (parallelPair h.f' 0) F

variable [F.PreservesZeroMorphisms]

/--
Instance `isPreservedBy_of_preservesHomology` / 实例 `isPreservedBy_of_preservesHomology`

English:
instance isPreservedBy_of_preservesHomology
  signature: [F.PreservesHomology]
  body: Functor.PreservesHomology.preservesKernel _ _
  f' := Functor.PreservesHomology.preservesCokernel _ _

中文:
实例 isPreservedBy_of_preservesHomology
  签名: [F.保持同调]
  定义体: Functor.PreservesHomology.preservesKernel _ _
  f' := Functor.PreservesHomology.preservesCokernel _ _

Depends on / 依赖: Functor, Functor.PreservesHomology.preservesKernel, PreservesHomology, leibniz_lie, preservesKernel, x.val
-/
noncomputable instance isPreservedBy_of_preservesHomology [F.PreservesHomology] :
    h.IsPreservedBy F where
  g := Functor.PreservesHomology.preservesKernel _ _
  f' := Functor.PreservesHomology.preservesCokernel _ _

variable [h.IsPreservedBy F]

include h in
/--
lemma `IsPreservedBy.hg` / 引理 `IsPreservedBy.hg`

English:
lemma IsPreservedBy.hg
  statement: PreservesLimit (parallelPair S.g 0) F
  proof: @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

中文:
引理 是PreservedBy.hg
  结论: 保持极限 (parallelPair S.g 0) F
  证明: @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

Depends on / 依赖: IsPreservedBy, IsPreservedBy.g, leibniz_lie, y.val
-/
lemma IsPreservedBy.hg : PreservesLimit (parallelPair S.g 0) F :=
  @IsPreservedBy.g _ _ _ _ _ _ _ h F _ _

/--
lemma `IsPreservedBy.hf'` / 引理 `IsPreservedBy.hf'`

English:
lemma IsPreservedBy.hf'
  statement: PreservesColimit (parallelPair h.f' 0) F
  proof: IsPreservedBy.f'

中文:
引理 是PreservedBy.hf'
  结论: 保持余极限 (parallelPair h.f' 0) F
  证明: IsPreservedBy.f'

Depends on / 依赖: IsPreservedBy, IsPreservedBy.f
-/
lemma IsPreservedBy.hf' : PreservesColimit (parallelPair h.f' 0) F := IsPreservedBy.f'

set_option backward.isDefEq.respectTransparency false in
/-- When a left homology data `h` of a short complex `S` is preserved by a functor `F`,
this is the induced left homology data `h.map F` for the short complex `S.map F`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (S.map F).LeftHomologyData
  body: by
  have := IsPreservedBy.hg h F
  have := IsPreservedBy.hf' h F
  have wi : F.map h.i ≫ F.map S.g = 0 := by rw [← F.map_comp, h.wi, F.map_zero]
  have hi := KernelFork.mapIsLimit _ h.hi F
  let f' : F.obj S.X₁ ⟶ F.obj h.K := hi.lift (KernelFork.ofι (S.map F).f (S.map F).zero)
  have hf' : f' = F.map h.f' := Fork.IsLimit.hom_ext hi (by
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, map_f, ← F.map_comp, f'_i])
  have wπ : f' ≫ F.map h.π = 0 := by rw [hf', ← F.map_comp, f'_π, F.map_zero]
  have hπ : IsColimit (CokernelCofork.ofπ (F.map h.π) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair (F.map h.f') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf') (by simp)
    refine IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ h.hπ' F) ?_)
    exact Cofork.ext (Iso.refl _) (by simp [e])
  exact
    { K := F.obj h.K
      H := F.obj h.H
      i := F.map h.i
      π := F.map h.π
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

中文:
定义 map
  签名: : (S.map F).LeftHomologyData
  定义体: by
  have := IsPreservedBy.hg h F
  have := IsPreservedBy.hf' h F
  have wi : F.map h.i ≫ F.map S.g = 0 := by rw [← F.map_comp, h.wi, F.map_zero]
  have hi := KernelFork.mapIsLimit _ h.hi F
  let f' : F.obj S.X₁ ⟶ F.obj h.K := hi.lift (KernelFork.ofι (S.map F).f (S.map F).zero)
  have hf' : f' = F.map h.f' := Fork.IsLimit.hom_ext hi (by
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, map_f, ← F.map_comp, f'_i])
  have wπ : f' ≫ F.map h.π = 0 := by rw [hf', ← F.map_comp, f'_π, F.map_zero]
  have hπ : IsColimit (CokernelCofork.ofπ (F.map h.π) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair (F.map h.f') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf') (by simp)
    refine IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ h.hπ' F) ?_)
    exact Cofork.ext (Iso.refl _) (by simp [e])
  exact
    { K := F.obj h.K
      H := F.obj h.H
      i := F.map h.i
      π := F.map h.π
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

Depends on / 依赖: F.map, F.map_comp, F.map_zero, F.obj, Fork.IsLimit.hom_ext, Fork.IsLimit.lift_, IsLimit, IsPreservedBy, IsPreservedBy.hf, IsPreservedBy.hg, KernelFork, KernelFork.mapIsLimit, KernelFork.map_, KernelFork.of, S.map, h.hi, h.wi, hi.lift, hom_ext, mapIsLimit
-/
noncomputable def map : (S.map F).LeftHomologyData := by
  have := IsPreservedBy.hg h F
  have := IsPreservedBy.hf' h F
  have wi : F.map h.i ≫ F.map S.g = 0 := by rw [← F.map_comp, h.wi, F.map_zero]
  have hi := KernelFork.mapIsLimit _ h.hi F
  let f' : F.obj S.X₁ ⟶ F.obj h.K := hi.lift (KernelFork.ofι (S.map F).f (S.map F).zero)
  have hf' : f' = F.map h.f' := Fork.IsLimit.hom_ext hi (by
    rw [Fork.IsLimit.lift_ι hi]
    simp only [KernelFork.map_ι, Fork.ι_ofι, map_f, ← F.map_comp, f'_i])
  have wπ : f' ≫ F.map h.π = 0 := by rw [hf', ← F.map_comp, f'_π, F.map_zero]
  have hπ : IsColimit (CokernelCofork.ofπ (F.map h.π) wπ) := by
    let e : parallelPair f' 0 ≅ parallelPair (F.map h.f') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hf') (by simp)
    refine IsColimit.precomposeInvEquiv e _
      (IsColimit.ofIsoColimit (CokernelCofork.mapIsColimit _ h.hπ' F) ?_)
    exact Cofork.ext (Iso.refl _) (by simp [e])
  exact
    { K := F.obj h.K
      H := F.obj h.H
      i := F.map h.i
      π := F.map h.π
      wi := wi
      hi := hi
      wπ := wπ
      hπ := hπ }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_f'` / 引理 `map_f'`

English:
lemma map_f'
  statement: (h.map F).f' = F.map h.f'
  proof: by
  rw [← cancel_mono (h.map F).i]; rw [f'_i]; rw [map_f]; rw [map_i]; rw [← F.map_comp]; rw [f'_i]

中文:
引理 map_f'
  结论: (h.map F).f' = F.map h.f'
  证明: by
  rw [← cancel_mono (h.map F).i]; rw [f'_i]; rw [map_f]; rw [map_i]; rw [← F.map_comp]; rw [f'_i]

Depends on / 依赖: F.map_comp, cancel_mono, h.map, map_comp, map_f, map_i
-/
lemma map_f' : (h.map F).f' = F.map h.f' := by
  rw [← cancel_mono (h.map F).i]; rw [f'_i]; rw [map_f]; rw [map_i]; rw [← F.map_comp]; rw [f'_i]

end LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- Given a left homology map data `ψ : LeftHomologyMapData φ h₁ h₂` such that
both left homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced left homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
/--
Definition of `LeftHomologyMapData.map` / `LeftHomologyMapData.map` 的定义

English:
definition LeftHomologyMapData.map
  signature: {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
  body: F.map ψ.φK
  φH := F.map ψ.φH
  commi := by simpa only [F.map_comp] using! F.congr_map ψ.commi
  commf' := by simpa only [LeftHomologyData.map_f', F.map_comp] using! F.congr_map ψ.commf'
  commπ := by simpa only [F.map_comp] using! F.congr_map ψ.commπ

中文:
定义 LeftHomologyMapData.map
  签名: {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
  定义体: F.map ψ.φK
  φH := F.map ψ.φH
  commi := by simpa only [F.map_comp] using! F.congr_map ψ.commi
  commf' := by simpa only [LeftHomologyData.map_f', F.map_comp] using! F.congr_map ψ.commf'
  commπ := by simpa only [F.map_comp] using! F.congr_map ψ.commπ

Depends on / 依赖: F.map
-/
noncomputable def LeftHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData}
    {h₂ : S₂.LeftHomologyData} (ψ : LeftHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    LeftHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φK := F.map ψ.φK
  φH := F.map ψ.φH
  commi := by simpa only [F.map_comp] using! F.congr_map ψ.commi
  commf' := by simpa only [LeftHomologyData.map_f', F.map_comp] using! F.congr_map ψ.commf'
  commπ := by simpa only [F.map_comp] using! F.congr_map ψ.commπ

namespace RightHomologyData

variable (h : S.RightHomologyData) (F : C ⥤ D)

/--
Definition of `IsPreservedBy` / `IsPreservedBy` 的定义

English:
class IsPreservedBy
  parameters: [F.PreservesZeroMorphisms]
  axioms and operations (2):
    - f : PreservesColimit (parallelPair S.f 0) F
    - g' : PreservesLimit (parallelPair h.g' 0) F

中文:
类 是PreservedBy
  参数: [F.保持ZeroMorphisms]
  公理与运算 (2 个):
    - f : 保持余极限 (parallelPair S.f 0) F
    - g' : 保持极限 (parallelPair h.g' 0) F
-/
class IsPreservedBy [F.PreservesZeroMorphisms] : Prop where
  /-- the functor preserves the cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
  f : PreservesColimit (parallelPair S.f 0) F
  /-- the functor preserves the kernel of `h.g' : h.Q ⟶ S.X₃`. -/
  g' : PreservesLimit (parallelPair h.g' 0) F

variable [F.PreservesZeroMorphisms]

/--
Instance `isPreservedBy_of_preservesHomology` / 实例 `isPreservedBy_of_preservesHomology`

English:
instance isPreservedBy_of_preservesHomology
  signature: [F.PreservesHomology]
  body: Functor.PreservesHomology.preservesCokernel F _
  g' := Functor.PreservesHomology.preservesKernel F _

中文:
实例 isPreservedBy_of_preservesHomology
  签名: [F.保持同调]
  定义体: Functor.PreservesHomology.preservesCokernel F _
  g' := Functor.PreservesHomology.preservesKernel F _

Depends on / 依赖: Functor, Functor.PreservesHomology.preservesCokernel, PreservesHomology, preservesCokernel
-/
noncomputable instance isPreservedBy_of_preservesHomology [F.PreservesHomology] :
    h.IsPreservedBy F where
  f := Functor.PreservesHomology.preservesCokernel F _
  g' := Functor.PreservesHomology.preservesKernel F _

variable [h.IsPreservedBy F]

include h in
/--
lemma `IsPreservedBy.hf` / 引理 `IsPreservedBy.hf`

English:
lemma IsPreservedBy.hf
  statement: PreservesColimit (parallelPair S.f 0) F
  proof: @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

中文:
引理 是PreservedBy.hf
  结论: 保持余极限 (parallelPair S.f 0) F
  证明: @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

Depends on / 依赖: IsPreservedBy, IsPreservedBy.f
-/
lemma IsPreservedBy.hf : PreservesColimit (parallelPair S.f 0) F :=
  @IsPreservedBy.f _ _ _ _ _ _ _ h F _ _

/--
lemma `IsPreservedBy.hg'` / 引理 `IsPreservedBy.hg'`

English:
lemma IsPreservedBy.hg'
  statement: PreservesLimit (parallelPair h.g' 0) F
  proof: @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

中文:
引理 是PreservedBy.hg'
  结论: 保持极限 (parallelPair h.g' 0) F
  证明: @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

Depends on / 依赖: IsPreservedBy, IsPreservedBy.g
-/
lemma IsPreservedBy.hg' : PreservesLimit (parallelPair h.g' 0) F :=
  @IsPreservedBy.g' _ _ _ _ _ _ _ h F _ _

set_option backward.isDefEq.respectTransparency false in
/-- When a right homology data `h` of a short complex `S` is preserved by a functor `F`,
this is the induced right homology data `h.map F` for the short complex `S.map F`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (S.map F).RightHomologyData
  body: by
  have := IsPreservedBy.hf h F
  have := IsPreservedBy.hg' h F
  have wp : F.map S.f ≫ F.map h.p = 0 := by rw [← F.map_comp, h.wp, F.map_zero]
  have hp := CokernelCofork.mapIsColimit _ h.hp F
  let g' : F.obj h.Q ⟶ F.obj S.X₃ := hp.desc (CokernelCofork.ofπ (S.map F).g (S.map F).zero)
  have hg' : g' = F.map h.g' := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc hp]
    simp only [Cofork.π_ofπ, CokernelCofork.map_π, map_g, ← F.map_comp, p_g']
  have wι : F.map h.ι ≫ g' = 0 := by rw [hg', ← F.map_comp, ι_g', F.map_zero]
  have hι : IsLimit (KernelFork.ofι (F.map h.ι) wι) := by
    let e : parallelPair g' 0 ≅ parallelPair (F.map h.g') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hg') (by simp)
    refine IsLimit.postcomposeHomEquiv e _
      (IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ h.hι' F) ?_)
    exact Fork.ext (Iso.refl _) (by simp [e])
  exact
    { Q := F.obj h.Q
      H := F.obj h.H
      p := F.map h.p
      ι := F.map h.ι
      wp := wp
      hp := hp
      wι := wι
      hι := hι }

中文:
定义 map
  签名: : (S.map F).RightHomologyData
  定义体: by
  have := IsPreservedBy.hf h F
  have := IsPreservedBy.hg' h F
  have wp : F.map S.f ≫ F.map h.p = 0 := by rw [← F.map_comp, h.wp, F.map_zero]
  have hp := CokernelCofork.mapIsColimit _ h.hp F
  let g' : F.obj h.Q ⟶ F.obj S.X₃ := hp.desc (CokernelCofork.ofπ (S.map F).g (S.map F).zero)
  have hg' : g' = F.map h.g' := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc hp]
    simp only [Cofork.π_ofπ, CokernelCofork.map_π, map_g, ← F.map_comp, p_g']
  have wι : F.map h.ι ≫ g' = 0 := by rw [hg', ← F.map_comp, ι_g', F.map_zero]
  have hι : IsLimit (KernelFork.ofι (F.map h.ι) wι) := by
    let e : parallelPair g' 0 ≅ parallelPair (F.map h.g') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hg') (by simp)
    refine IsLimit.postcomposeHomEquiv e _
      (IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ h.hι' F) ?_)
    exact Fork.ext (Iso.refl _) (by simp [e])
  exact
    { Q := F.obj h.Q
      H := F.obj h.H
      p := F.map h.p
      ι := F.map h.ι
      wp := wp
      hp := hp
      wι := wι
      hι := hι }

Depends on / 依赖: Cofork, Cofork.IsColimit, Cofork.IsColimit.hom_ext, CokernelCofork, CokernelCofork.mapIsColimit, CokernelCofork.map_, CokernelCofork.of, F.map, F.map_comp, F.map_zero, F.obj, IsColimit, IsPreservedBy, IsPreservedBy.hf, IsPreservedBy.hg, S.map, h.hp, h.wp, hom_ext, hp.desc
-/
noncomputable def map : (S.map F).RightHomologyData := by
  have := IsPreservedBy.hf h F
  have := IsPreservedBy.hg' h F
  have wp : F.map S.f ≫ F.map h.p = 0 := by rw [← F.map_comp, h.wp, F.map_zero]
  have hp := CokernelCofork.mapIsColimit _ h.hp F
  let g' : F.obj h.Q ⟶ F.obj S.X₃ := hp.desc (CokernelCofork.ofπ (S.map F).g (S.map F).zero)
  have hg' : g' = F.map h.g' := by
    apply Cofork.IsColimit.hom_ext hp
    rw [Cofork.IsColimit.π_desc hp]
    simp only [Cofork.π_ofπ, CokernelCofork.map_π, map_g, ← F.map_comp, p_g']
  have wι : F.map h.ι ≫ g' = 0 := by rw [hg', ← F.map_comp, ι_g', F.map_zero]
  have hι : IsLimit (KernelFork.ofι (F.map h.ι) wι) := by
    let e : parallelPair g' 0 ≅ parallelPair (F.map h.g') 0 :=
      parallelPair.ext (Iso.refl _) (Iso.refl _) (by simpa using hg') (by simp)
    refine IsLimit.postcomposeHomEquiv e _
      (IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ h.hι' F) ?_)
    exact Fork.ext (Iso.refl _) (by simp [e])
  exact
    { Q := F.obj h.Q
      H := F.obj h.H
      p := F.map h.p
      ι := F.map h.ι
      wp := wp
      hp := hp
      wι := wι
      hι := hι }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_g'` / 引理 `map_g'`

English:
lemma map_g'
  statement: (h.map F).g' = F.map h.g'
  proof: by
  rw [← cancel_epi (h.map F).p]; rw [p_g']; rw [map_g]; rw [map_p]; rw [← F.map_comp]; rw [p_g']

中文:
引理 map_g'
  结论: (h.map F).g' = F.map h.g'
  证明: by
  rw [← cancel_epi (h.map F).p]; rw [p_g']; rw [map_g]; rw [map_p]; rw [← F.map_comp]; rw [p_g']

Depends on / 依赖: F.map_comp, cancel_epi, h.map, map_comp, map_g, map_p
-/
lemma map_g' : (h.map F).g' = F.map h.g' := by
  rw [← cancel_epi (h.map F).p]; rw [p_g']; rw [map_g]; rw [map_p]; rw [← F.map_comp]; rw [p_g']

end RightHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- Given a right homology map data `ψ : RightHomologyMapData φ h₁ h₂` such that
both right homology data `h₁` and `h₂` are preserved by a functor `F`, this is
the induced right homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
/--
Definition of `RightHomologyMapData.map` / `RightHomologyMapData.map` 的定义

English:
definition RightHomologyMapData.map
  signature: {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
  body: F.map ψ.φQ
  φH := F.map ψ.φH
  commp := by simpa only [F.map_comp] using! F.congr_map ψ.commp
  commg' := by simpa only [RightHomologyData.map_g', F.map_comp] using! F.congr_map ψ.commg'
  commι := by simpa only [F.map_comp] using! F.congr_map ψ.commι

中文:
定义 RightHomologyMapData.map
  签名: {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
  定义体: F.map ψ.φQ
  φH := F.map ψ.φH
  commp := by simpa only [F.map_comp] using! F.congr_map ψ.commp
  commg' := by simpa only [RightHomologyData.map_g', F.map_comp] using! F.congr_map ψ.commg'
  commι := by simpa only [F.map_comp] using! F.congr_map ψ.commι

Depends on / 依赖: F.map
-/
noncomputable def RightHomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} (ψ : RightHomologyMapData φ h₁ h₂) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [h₁.IsPreservedBy F] [h₂.IsPreservedBy F] :
    RightHomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  φQ := F.map ψ.φQ
  φH := F.map ψ.φH
  commp := by simpa only [F.map_comp] using! F.congr_map ψ.commp
  commg' := by simpa only [RightHomologyData.map_g', F.map_comp] using! F.congr_map ψ.commg'
  commι := by simpa only [F.map_comp] using! F.congr_map ψ.commι

/-- When a homology data `h` of a short complex `S` is such that both `h.left` and
`h.right` are preserved by a functor `F`, this is the induced homology data
`h.map F` for the short complex `S.map F`. -/
@[simps]
/--
Definition of `HomologyData.map` / `HomologyData.map` 的定义

English:
definition HomologyData.map
  signature: (h : S.HomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
  body: h.left.map F
  right := h.right.map F
  iso := F.mapIso h.iso
  comm := by simpa only [F.map_comp] using! F.congr_map h.comm

中文:
定义 同调数据.map
  签名: (h : S.同调数据) (F : C ⥤ D) [F.保持ZeroMorphisms]
  定义体: h.left.map F
  right := h.right.map F
  iso := F.mapIso h.iso
  comm := by simpa only [F.map_comp] using! F.congr_map h.comm

Depends on / 依赖: h.left.map
-/
noncomputable def HomologyData.map (h : S.HomologyData) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h.left.IsPreservedBy F] [h.right.IsPreservedBy F] :
    (S.map F).HomologyData where
  left := h.left.map F
  right := h.right.map F
  iso := F.mapIso h.iso
  comm := by simpa only [F.map_comp] using! F.congr_map h.comm

/-- Given a homology map data `ψ : HomologyMapData φ h₁ h₂` such that
`h₁.left`, `h₁.right`, `h₂.left` and `h₂.right` are all preserved by a functor `F`, this is
the induced homology map data for the morphism `F.mapShortComplex.map φ`. -/
@[simps]
/--
Definition of `HomologyMapData.map` / `HomologyMapData.map` 的定义

English:
definition HomologyMapData.map
  signature: {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
  body: ψ.left.map F
  right := ψ.right.map F

中文:
定义 同调映射数据.map
  签名: {φ : S₁ ⟶ S₂} {h₁ : S₁.同调数据} {h₂ : S₂.同调数据}
  定义体: ψ.left.map F
  right := ψ.right.map F

Depends on / 依赖: left.map
-/
noncomputable def HomologyMapData.map {φ : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}
    (ψ : HomologyMapData φ h₁ h₂) (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    HomologyMapData (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) where
  left := ψ.left.map F
  right := ψ.right.map F

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_leftRightHomologyComparison'` / 引理 `map_leftRightHomologyComparison'`

English:
lemma map_leftRightHomologyComparison'
  statement: (F : C ⥤ D) [F.PreservesZeroMorphisms]
  proof: by
  apply Cofork.IsColimit.hom_ext (hₗ.map F).hπ
  apply Fork.IsLimit.hom_ext (hᵣ.map F).hι
  trans F.map (hₗ.i ≫ hᵣ.p)
  · simp [← Functor.map_comp]
  trans (hₗ.map F).π ≫ ShortComplex.leftRightHomologyComparison'
    (hₗ.map F) (hᵣ.map F) ≫ (hᵣ.map F).ι
  · rw [ShortComplex.π_leftRightHomologyComparison'_ι]; simp
  · simp

中文:
引理 map_leftRightHomologyComparison'
  结论: (F : C ⥤ D) [F.保持ZeroMorphisms]
  证明: by
  apply Cofork.IsColimit.hom_ext (hₗ.map F).hπ
  apply Fork.IsLimit.hom_ext (hᵣ.map F).hι
  trans F.map (hₗ.i ≫ hᵣ.p)
  · simp [← Functor.map_comp]
  trans (hₗ.map F).π ≫ ShortComplex.leftRightHomologyComparison'
    (hₗ.map F) (hᵣ.map F) ≫ (hᵣ.map F).ι
  · rw [ShortComplex.π_leftRightHomologyComparison'_ι]; simp
  · simp

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, F.map, Fork.IsLimit.hom_ext, Functor, Functor.map_comp, IsColimit, IsLimit, ShortComplex, ShortComplex.leftRightHomologyComparison, hom_ext, leftRightHomologyComparison, map_comp
-/
lemma map_leftRightHomologyComparison' (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hₗ : S.LeftHomologyData) (hᵣ : S.RightHomologyData) [hₗ.IsPreservedBy F] [hᵣ.IsPreservedBy F] :
    F.map (leftRightHomologyComparison' hₗ hᵣ) =
      leftRightHomologyComparison' (hₗ.map F) (hᵣ.map F) := by
  apply Cofork.IsColimit.hom_ext (hₗ.map F).hπ
  apply Fork.IsLimit.hom_ext (hᵣ.map F).hι
  trans F.map (hₗ.i ≫ hᵣ.p)
  · simp [← Functor.map_comp]
  trans (hₗ.map F).π ≫ ShortComplex.leftRightHomologyComparison'
    (hₗ.map F) (hᵣ.map F) ≫ (hᵣ.map F).ι
  · rw [ShortComplex.π_leftRightHomologyComparison'_ι]; simp
  · simp

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [PreservesZeroMorphisms F] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

/--
Definition of `PreservesLeftHomologyOf` / `PreservesLeftHomologyOf` 的定义

English:
class PreservesLeftHomologyOf
  parameters: : Prop where
  axioms and operations (1):
    - isPreservedBy : forall (h : S.LeftHomologyData), h.IsPreservedBy F

中文:
类 保持LeftHomologyOf
  参数: : 命题 where
  公理与运算 (1 个):
    - isPreservedBy : 对任意 (h : S.LeftHomologyData), h.是PreservedBy F
-/
class PreservesLeftHomologyOf : Prop where
  /-- the functor preserves all the left homology data of the short complex -/
  isPreservedBy : forall (h : S.LeftHomologyData), h.IsPreservedBy F

/--
Definition of `PreservesRightHomologyOf` / `PreservesRightHomologyOf` 的定义

English:
class PreservesRightHomologyOf
  parameters: : Prop where
  axioms and operations (1):
    - isPreservedBy : forall (h : S.RightHomologyData), h.IsPreservedBy F

中文:
类 保持RightHomologyOf
  参数: : 命题 where
  公理与运算 (1 个):
    - isPreservedBy : 对任意 (h : S.RightHomologyData), h.是PreservedBy F
-/
class PreservesRightHomologyOf : Prop where
  /-- the functor preserves all the right homology data of the short complex -/
  isPreservedBy : forall (h : S.RightHomologyData), h.IsPreservedBy F

/--
Instance `PreservesHomology.preservesLeftHomologyOf` / 实例 `PreservesHomology.preservesLeftHomologyOf`

English:
instance PreservesHomology.preservesLeftHomologyOf
  signature: [F.PreservesHomology]
  body: ⟨inferInstance⟩

中文:
实例 保持同调.preservesLeftHomologyOf
  签名: [F.保持同调]
  定义体: ⟨inferInstance⟩
-/
instance PreservesHomology.preservesLeftHomologyOf [F.PreservesHomology] :
    F.PreservesLeftHomologyOf S := ⟨inferInstance⟩

/--
Instance `PreservesHomology.preservesRightHomologyOf` / 实例 `PreservesHomology.preservesRightHomologyOf`

English:
instance PreservesHomology.preservesRightHomologyOf
  signature: [F.PreservesHomology]
  body: ⟨inferInstance⟩

中文:
实例 保持同调.preservesRightHomologyOf
  签名: [F.保持同调]
  定义体: ⟨inferInstance⟩
-/
instance PreservesHomology.preservesRightHomologyOf [F.PreservesHomology] :
    F.PreservesRightHomologyOf S := ⟨inferInstance⟩

variable {S}

/--
lemma `PreservesLeftHomologyOf.mk'` / 引理 `PreservesLeftHomologyOf.mk'`

English:
lemma PreservesLeftHomologyOf.mk'
  given: (h : S.LeftHomologyData) [h.IsPreservedBy F]
  proof: { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
      f' := by
        have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
        let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
          parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
            (by simp) (by simp)
        exact preservesColimit_of_iso_diagram F e }

中文:
引理 保持LeftHomologyOf.mk'
  条件: (h : S.LeftHomologyData) [h.是PreservedBy F]
  证明: { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
      f' := by
        have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
        let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
          parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
            (by simp) (by simp)
        exact preservesColimit_of_iso_diagram F e }

Depends on / 依赖: IsPreservedBy, Iso.refl, LeftHomologyData, ShortComplex, ShortComplex.LeftHomologyData.IsPreservedBy.hf, ShortComplex.LeftHomologyData.IsPreservedBy.hg, ShortComplex.cyclesMapIso, cyclesMapIso, parallelPair, parallelPair.ext, preservesColimit_of_iso_diagram
-/
lemma PreservesLeftHomologyOf.mk' (h : S.LeftHomologyData) [h.IsPreservedBy F] :
    F.PreservesLeftHomologyOf S where
  isPreservedBy h' :=
    { g := ShortComplex.LeftHomologyData.IsPreservedBy.hg h F
      f' := by
        have := ShortComplex.LeftHomologyData.IsPreservedBy.hf' h F
        let e : parallelPair h.f' 0 ≅ parallelPair h'.f' 0 :=
          parallelPair.ext (Iso.refl _) (ShortComplex.cyclesMapIso' (Iso.refl S) h h')
            (by simp) (by simp)
        exact preservesColimit_of_iso_diagram F e }

/--
lemma `PreservesRightHomologyOf.mk'` / 引理 `PreservesRightHomologyOf.mk'`

English:
lemma PreservesRightHomologyOf.mk'
  given: (h : S.RightHomologyData) [h.IsPreservedBy F]
  proof: { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
      g' := by
        have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
        let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
          parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
            (by simp) (by simp)
        exact preservesLimit_of_iso_diagram F e }

中文:
引理 保持RightHomologyOf.mk'
  条件: (h : S.RightHomologyData) [h.是PreservedBy F]
  证明: { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
      g' := by
        have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
        let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
          parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
            (by simp) (by simp)
        exact preservesLimit_of_iso_diagram F e }

Depends on / 依赖: IsPreservedBy, Iso.refl, RightHomologyData, ShortComplex, ShortComplex.RightHomologyData.IsPreservedBy.hf, ShortComplex.RightHomologyData.IsPreservedBy.hg, ShortComplex.opcyclesMapIso, opcyclesMapIso, parallelPair, parallelPair.ext, preservesLimit_of_iso_diagram
-/
lemma PreservesRightHomologyOf.mk' (h : S.RightHomologyData) [h.IsPreservedBy F] :
    F.PreservesRightHomologyOf S where
  isPreservedBy h' :=
    { f := ShortComplex.RightHomologyData.IsPreservedBy.hf h F
      g' := by
        have := ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
        let e : parallelPair h.g' 0 ≅ parallelPair h'.g' 0 :=
          parallelPair.ext (ShortComplex.opcyclesMapIso' (Iso.refl S) h h') (Iso.refl _)
            (by simp) (by simp)
        exact preservesLimit_of_iso_diagram F e }

end Functor

namespace ShortComplex

variable {S : ShortComplex C} (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

/--
Instance `LeftHomologyData.isPreservedBy_of_preserves` / 实例 `LeftHomologyData.isPreservedBy_of_preserves`

English:
instance LeftHomologyData.isPreservedBy_of_preserves
  signature: [F.PreservesLeftHomologyOf S]
  body: Functor.PreservesLeftHomologyOf.isPreservedBy _

中文:
实例 LeftHomologyData.isPreservedBy_of_preserves
  签名: [F.保持LeftHomologyOf S]
  定义体: Functor.PreservesLeftHomologyOf.isPreservedBy _

Depends on / 依赖: Functor, Functor.PreservesLeftHomologyOf.isPreservedBy, PreservesLeftHomologyOf, isPreservedBy
-/
instance LeftHomologyData.isPreservedBy_of_preserves [F.PreservesLeftHomologyOf S] :
    h₁.IsPreservedBy F :=
  Functor.PreservesLeftHomologyOf.isPreservedBy _

/--
Instance `RightHomologyData.isPreservedBy_of_preserves` / 实例 `RightHomologyData.isPreservedBy_of_preserves`

English:
instance RightHomologyData.isPreservedBy_of_preserves
  signature: [F.PreservesRightHomologyOf S]
  body: Functor.PreservesRightHomologyOf.isPreservedBy _

中文:
实例 RightHomologyData.isPreservedBy_of_preserves
  签名: [F.保持RightHomologyOf S]
  定义体: Functor.PreservesRightHomologyOf.isPreservedBy _

Depends on / 依赖: Functor, Functor.PreservesRightHomologyOf.isPreservedBy, PreservesRightHomologyOf, isPreservedBy
-/
instance RightHomologyData.isPreservedBy_of_preserves [F.PreservesRightHomologyOf S] :
    h₂.IsPreservedBy F :=
  Functor.PreservesRightHomologyOf.isPreservedBy _

variable (S)

/--
Instance `hasLeftHomology_of_preserves` / 实例 `hasLeftHomology_of_preserves`

English:
instance hasLeftHomology_of_preserves
  signature: [S.HasLeftHomology] [F.PreservesLeftHomologyOf S]
  body: HasLeftHomology.mk' (S.leftHomologyData.map F)

中文:
实例 hasLeftHomology_of_preserves
  签名: [S.有LeftHomology] [F.保持LeftHomologyOf S]
  定义体: HasLeftHomology.mk' (S.leftHomologyData.map F)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, S.leftHomologyData.map, leftHomologyData
-/
instance hasLeftHomology_of_preserves [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).HasLeftHomology :=
  HasLeftHomology.mk' (S.leftHomologyData.map F)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `hasLeftHomology_of_preserves'` / 实例 `hasLeftHomology_of_preserves'`

English:
instance hasLeftHomology_of_preserves'
  signature: [S.HasLeftHomology] [F.PreservesLeftHomologyOf S]
  body: by
  dsimp; infer_instance

中文:
实例 hasLeftHomology_of_preserves'
  签名: [S.有LeftHomology] [F.保持LeftHomologyOf S]
  定义体: by
  dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance hasLeftHomology_of_preserves' [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (F.mapShortComplex.obj S).HasLeftHomology := by
  dsimp; infer_instance

/--
Instance `hasRightHomology_of_preserves` / 实例 `hasRightHomology_of_preserves`

English:
instance hasRightHomology_of_preserves
  signature: [S.HasRightHomology] [F.PreservesRightHomologyOf S]
  body: HasRightHomology.mk' (S.rightHomologyData.map F)

中文:
实例 hasRightHomology_of_preserves
  签名: [S.有RightHomology] [F.保持RightHomologyOf S]
  定义体: HasRightHomology.mk' (S.rightHomologyData.map F)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, S.rightHomologyData.map, rightHomologyData
-/
instance hasRightHomology_of_preserves [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).HasRightHomology :=
  HasRightHomology.mk' (S.rightHomologyData.map F)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `hasRightHomology_of_preserves'` / 实例 `hasRightHomology_of_preserves'`

English:
instance hasRightHomology_of_preserves'
  signature: [S.HasRightHomology] [F.PreservesRightHomologyOf S]
  body: by
  dsimp; infer_instance

中文:
实例 hasRightHomology_of_preserves'
  签名: [S.有RightHomology] [F.保持RightHomologyOf S]
  定义体: by
  dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance hasRightHomology_of_preserves' [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasRightHomology := by
  dsimp; infer_instance

/--
Instance `hasHomology_of_preserves` / 实例 `hasHomology_of_preserves`

English:
instance hasHomology_of_preserves
  signature: [S.HasHomology] [F.PreservesLeftHomologyOf S]
  body: HasHomology.mk' (S.homologyData.map F)

中文:
实例 hasHomology_of_preserves
  签名: [S.有同调] [F.保持LeftHomologyOf S]
  定义体: HasHomology.mk' (S.homologyData.map F)

Depends on / 依赖: HasHomology, HasHomology.mk, S.homologyData.map, homologyData
-/
instance hasHomology_of_preserves [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    (S.map F).HasHomology :=
  HasHomology.mk' (S.homologyData.map F)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `hasHomology_of_preserves'` / 实例 `hasHomology_of_preserves'`

English:
instance hasHomology_of_preserves'
  signature: [S.HasHomology] [F.PreservesLeftHomologyOf S]
  body: by
  dsimp; infer_instance

中文:
实例 hasHomology_of_preserves'
  签名: [S.有同调] [F.保持LeftHomologyOf S]
  定义体: by
  dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance hasHomology_of_preserves' [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    (F.mapShortComplex.obj S).HasHomology := by
  dsimp; infer_instance

section

variable
  (hl : S.LeftHomologyData) (hr : S.RightHomologyData)
  {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂)
  (hl₁ : S₁.LeftHomologyData) (hr₁ : S₁.RightHomologyData)
  (hl₂ : S₂.LeftHomologyData) (hr₂ : S₂.RightHomologyData)
  (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData)
  (F : C ⥤ D) [F.PreservesZeroMorphisms]

namespace LeftHomologyData

variable [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F]

/--
lemma `map_cyclesMap'` / 引理 `map_cyclesMap'`

English:
lemma map_cyclesMap'
  statement: F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) =
  proof: by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.cyclesMap'_eq]; rw [(γ.map F).cyclesMap'_eq]; rw [ShortComplex.LeftHomologyMapData.map_φK]

中文:
引理 map_cyclesMap'
  结论: F.map (短复形.cyclesMap' φ hl₁ hl₂) =
  证明: by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.cyclesMap'_eq]; rw [(γ.map F).cyclesMap'_eq]; rw [ShortComplex.LeftHomologyMapData.map_φK]

Depends on / 依赖: LeftHomologyMapData, ShortComplex, ShortComplex.LeftHomologyMapData, ShortComplex.LeftHomologyMapData.map_, cyclesMap
-/
lemma map_cyclesMap' : F.map (ShortComplex.cyclesMap' φ hl₁ hl₂) =
    ShortComplex.cyclesMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F) := by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.cyclesMap'_eq]; rw [(γ.map F).cyclesMap'_eq]; rw [ShortComplex.LeftHomologyMapData.map_φK]

/--
lemma `map_leftHomologyMap'` / 引理 `map_leftHomologyMap'`

English:
lemma map_leftHomologyMap'
  statement: F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) =
  proof: by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.leftHomologyMap'_eq]; rw [(γ.map F).leftHomologyMap'_eq]; rw [ShortComplex.LeftHomologyMapData.map_φH]

中文:
引理 map_leftHomologyMap'
  结论: F.map (短复形.leftHomologyMap' φ hl₁ hl₂) =
  证明: by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.leftHomologyMap'_eq]; rw [(γ.map F).leftHomologyMap'_eq]; rw [ShortComplex.LeftHomologyMapData.map_φH]

Depends on / 依赖: LeftHomologyMapData, ShortComplex, ShortComplex.LeftHomologyMapData, ShortComplex.LeftHomologyMapData.map_, leftHomologyMap
-/
lemma map_leftHomologyMap' : F.map (ShortComplex.leftHomologyMap' φ hl₁ hl₂) =
    ShortComplex.leftHomologyMap' (F.mapShortComplex.map φ) (hl₁.map F) (hl₂.map F) := by
  have γ : ShortComplex.LeftHomologyMapData φ hl₁ hl₂ := default
  rw [γ.leftHomologyMap'_eq]; rw [(γ.map F).leftHomologyMap'_eq]; rw [ShortComplex.LeftHomologyMapData.map_φH]

end LeftHomologyData

namespace RightHomologyData

variable [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F]

/--
lemma `map_opcyclesMap'` / 引理 `map_opcyclesMap'`

English:
lemma map_opcyclesMap'
  statement: F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) =
  proof: by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.opcyclesMap'_eq]; rw [(γ.map F).opcyclesMap'_eq]; rw [ShortComplex.RightHomologyMapData.map_φQ]

中文:
引理 map_opcyclesMap'
  结论: F.map (短复形.opcyclesMap' φ hr₁ hr₂) =
  证明: by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.opcyclesMap'_eq]; rw [(γ.map F).opcyclesMap'_eq]; rw [ShortComplex.RightHomologyMapData.map_φQ]

Depends on / 依赖: RightHomologyMapData, ShortComplex, ShortComplex.RightHomologyMapData, ShortComplex.RightHomologyMapData.map_, opcyclesMap
-/
lemma map_opcyclesMap' : F.map (ShortComplex.opcyclesMap' φ hr₁ hr₂) =
    ShortComplex.opcyclesMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F) := by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.opcyclesMap'_eq]; rw [(γ.map F).opcyclesMap'_eq]; rw [ShortComplex.RightHomologyMapData.map_φQ]

/--
lemma `map_rightHomologyMap'` / 引理 `map_rightHomologyMap'`

English:
lemma map_rightHomologyMap'
  statement: F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) =
  proof: by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.rightHomologyMap'_eq]; rw [(γ.map F).rightHomologyMap'_eq]; rw [ShortComplex.RightHomologyMapData.map_φH]

中文:
引理 map_rightHomologyMap'
  结论: F.map (短复形.rightHomologyMap' φ hr₁ hr₂) =
  证明: by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.rightHomologyMap'_eq]; rw [(γ.map F).rightHomologyMap'_eq]; rw [ShortComplex.RightHomologyMapData.map_φH]

Depends on / 依赖: RightHomologyMapData, ShortComplex, ShortComplex.RightHomologyMapData, ShortComplex.RightHomologyMapData.map_, rightHomologyMap
-/
lemma map_rightHomologyMap' : F.map (ShortComplex.rightHomologyMap' φ hr₁ hr₂) =
    ShortComplex.rightHomologyMap' (F.mapShortComplex.map φ) (hr₁.map F) (hr₂.map F) := by
  have γ : ShortComplex.RightHomologyMapData φ hr₁ hr₂ := default
  rw [γ.rightHomologyMap'_eq]; rw [(γ.map F).rightHomologyMap'_eq]; rw [ShortComplex.RightHomologyMapData.map_φH]

end RightHomologyData

/--
lemma `HomologyData.map_homologyMap'` / 引理 `HomologyData.map_homologyMap'`

English:
lemma HomologyData.map_homologyMap'
  proof: LeftHomologyData.map_leftHomologyMap' _ _ _ _

中文:
引理 同调数据.map_homologyMap'
  证明: LeftHomologyData.map_leftHomologyMap' _ _ _ _

Depends on / 依赖: LeftHomologyData, LeftHomologyData.map_leftHomologyMap, map_leftHomologyMap
-/
lemma HomologyData.map_homologyMap'
    [h₁.left.IsPreservedBy F] [h₁.right.IsPreservedBy F]
    [h₂.left.IsPreservedBy F] [h₂.right.IsPreservedBy F] :
    F.map (ShortComplex.homologyMap' φ h₁ h₂) =
      ShortComplex.homologyMap' (F.mapShortComplex.map φ) (h₁.map F) (h₂.map F) :=
  LeftHomologyData.map_leftHomologyMap' _ _ _ _

/--
Definition of `mapCyclesIso` / `mapCyclesIso` 的定义

English:
definition mapCyclesIso
  signature: [S.HasLeftHomology] [F.PreservesLeftHomologyOf S]
  body: (S.leftHomologyData.map F).cyclesIso

@[reassoc (attr := simp)]

中文:
定义 mapCyclesIso
  签名: [S.有LeftHomology] [F.保持LeftHomologyOf S]
  定义体: (S.leftHomologyData.map F).cyclesIso

@[reassoc (attr := simp)]

Depends on / 依赖: S.leftHomologyData.map, cyclesIso, leftHomologyData
-/
noncomputable def mapCyclesIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).cycles ≅ F.obj S.cycles :=
  (S.leftHomologyData.map F).cyclesIso

@[reassoc (attr := simp)]
/--
lemma `mapCyclesIso_hom_iCycles` / 引理 `mapCyclesIso_hom_iCycles`

English:
lemma mapCyclesIso_hom_iCycles
  given: [S.HasLeftHomology] [F.PreservesLeftHomologyOf S]
  proof: by
  apply LeftHomologyData.cyclesIso_hom_comp_i

中文:
引理 mapCyclesIso_hom_iCycles
  条件: [S.有LeftHomology] [F.保持LeftHomologyOf S]
  证明: by
  apply LeftHomologyData.cyclesIso_hom_comp_i

Depends on / 依赖: LeftHomologyData, LeftHomologyData.cyclesIso_hom_comp_i, cyclesIso_hom_comp_i
-/
lemma mapCyclesIso_hom_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).hom ≫ F.map S.iCycles = (S.map F).iCycles := by
  apply LeftHomologyData.cyclesIso_hom_comp_i

/--
Definition of `mapLeftHomologyIso` / `mapLeftHomologyIso` 的定义

English:
definition mapLeftHomologyIso
  signature: [S.HasLeftHomology] [F.PreservesLeftHomologyOf S]
  body: (S.leftHomologyData.map F).leftHomologyIso

中文:
定义 mapLeftHomologyIso
  签名: [S.有LeftHomology] [F.保持LeftHomologyOf S]
  定义体: (S.leftHomologyData.map F).leftHomologyIso

Depends on / 依赖: S.leftHomologyData.map, leftHomologyData, leftHomologyIso
-/
noncomputable def mapLeftHomologyIso [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.map F).leftHomology ≅ F.obj S.leftHomology :=
  (S.leftHomologyData.map F).leftHomologyIso

/--
Definition of `mapOpcyclesIso` / `mapOpcyclesIso` 的定义

English:
definition mapOpcyclesIso
  signature: [S.HasRightHomology] [F.PreservesRightHomologyOf S]
  body: (S.rightHomologyData.map F).opcyclesIso

中文:
定义 mapOpcyclesIso
  签名: [S.有RightHomology] [F.保持RightHomologyOf S]
  定义体: (S.rightHomologyData.map F).opcyclesIso

Depends on / 依赖: S.rightHomologyData.map, opcyclesIso, rightHomologyData
-/
noncomputable def mapOpcyclesIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).opcycles ≅ F.obj S.opcycles :=
  (S.rightHomologyData.map F).opcyclesIso

/--
Definition of `mapRightHomologyIso` / `mapRightHomologyIso` 的定义

English:
definition mapRightHomologyIso
  signature: [S.HasRightHomology] [F.PreservesRightHomologyOf S]
  body: (S.rightHomologyData.map F).rightHomologyIso

中文:
定义 mapRightHomologyIso
  签名: [S.有RightHomology] [F.保持RightHomologyOf S]
  定义体: (S.rightHomologyData.map F).rightHomologyIso

Depends on / 依赖: S.rightHomologyData.map, rightHomologyData, rightHomologyIso
-/
noncomputable def mapRightHomologyIso [S.HasRightHomology] [F.PreservesRightHomologyOf S] :
    (S.map F).rightHomology ≅ F.obj S.rightHomology :=
  (S.rightHomologyData.map F).rightHomologyIso

/--
Definition of `mapHomologyIso` / `mapHomologyIso` 的定义

English:
definition mapHomologyIso
  signature: [S.HasHomology] [(S.map F).HasHomology]
  body: (S.homologyData.left.map F).homologyIso

中文:
定义 mapHomologyIso
  签名: [S.有同调] [(S.map F).有同调]
  定义体: (S.homologyData.left.map F).homologyIso

Depends on / 依赖: S.homologyData.left.map, homologyData, homologyIso
-/
noncomputable def mapHomologyIso [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology :=
  (S.homologyData.left.map F).homologyIso

/--
Definition of `mapHomologyIso'` / `mapHomologyIso'` 的定义

English:
definition mapHomologyIso'
  signature: [S.HasHomology] [(S.map F).HasHomology]
  body: (S.homologyData.right.map F).homologyIso ≪≫ F.mapIso S.homologyData.right.homologyIso.symm

中文:
定义 mapHomologyIso'
  签名: [S.有同调] [(S.map F).有同调]
  定义体: (S.homologyData.right.map F).homologyIso ≪≫ F.mapIso S.homologyData.right.homologyIso.symm

Depends on / 依赖: F.mapIso, S.homologyData.right.homologyIso.symm, S.homologyData.right.map, homologyData, homologyIso, mapIso
-/
noncomputable def mapHomologyIso' [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesRightHomologyOf S] :
    (S.map F).homology ≅ F.obj S.homology :=
  (S.homologyData.right.map F).homologyIso ≪≫ F.mapIso S.homologyData.right.homologyIso.symm

variable {S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `LeftHomologyData.mapCyclesIso_eq` / 引理 `LeftHomologyData.mapCyclesIso_eq`

English:
lemma LeftHomologyData.mapCyclesIso_eq
  statement: [S.HasLeftHomology]
  proof: by
  ext
  dsimp [mapCyclesIso, cyclesIso]
  simp only [map_cyclesMap', ← cyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

中文:
引理 LeftHomologyData.mapCyclesIso_eq
  结论: [S.有LeftHomology]
  证明: by
  ext
  dsimp [mapCyclesIso, cyclesIso]
  simp only [map_cyclesMap', ← cyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Functor.map_id, _comp, comp_id, cyclesIso, cyclesMap, mapCyclesIso, mapShortComplex_obj, map_cyclesMap, map_id
-/
lemma LeftHomologyData.mapCyclesIso_eq [S.HasLeftHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapCyclesIso F = (hl.map F).cyclesIso ≪≫ F.mapIso hl.cyclesIso.symm := by
  ext
  dsimp [mapCyclesIso, cyclesIso]
  simp only [map_cyclesMap', ← cyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `LeftHomologyData.mapLeftHomologyIso_eq` / 引理 `LeftHomologyData.mapLeftHomologyIso_eq`

English:
lemma LeftHomologyData.mapLeftHomologyIso_eq
  statement: [S.HasLeftHomology]
  proof: by
  ext
  dsimp [mapLeftHomologyIso, leftHomologyIso]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

中文:
引理 LeftHomologyData.mapLeftHomologyIso_eq
  结论: [S.有LeftHomology]
  证明: by
  ext
  dsimp [mapLeftHomologyIso, leftHomologyIso]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Functor.map_id, _comp, comp_id, leftHomologyIso, leftHomologyMap, mapLeftHomologyIso, mapShortComplex_obj, map_id, map_leftHomologyMap
-/
lemma LeftHomologyData.mapLeftHomologyIso_eq [S.HasLeftHomology]
    [F.PreservesLeftHomologyOf S] :
    S.mapLeftHomologyIso F = (hl.map F).leftHomologyIso ≪≫ F.mapIso hl.leftHomologyIso.symm := by
  ext
  dsimp [mapLeftHomologyIso, leftHomologyIso]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `RightHomologyData.mapOpcyclesIso_eq` / 引理 `RightHomologyData.mapOpcyclesIso_eq`

English:
lemma RightHomologyData.mapOpcyclesIso_eq
  statement: [S.HasRightHomology]
  proof: by
  ext
  dsimp [mapOpcyclesIso, opcyclesIso]
  simp only [map_opcyclesMap', ← opcyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

中文:
引理 RightHomologyData.mapOpcyclesIso_eq
  结论: [S.有RightHomology]
  证明: by
  ext
  dsimp [mapOpcyclesIso, opcyclesIso]
  simp only [map_opcyclesMap', ← opcyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Functor.map_id, _comp, comp_id, mapOpcyclesIso, mapShortComplex_obj, map_id, map_opcyclesMap, opcyclesIso, opcyclesMap
-/
lemma RightHomologyData.mapOpcyclesIso_eq [S.HasRightHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapOpcyclesIso F = (hr.map F).opcyclesIso ≪≫ F.mapIso hr.opcyclesIso.symm := by
  ext
  dsimp [mapOpcyclesIso, opcyclesIso]
  simp only [map_opcyclesMap', ← opcyclesMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `RightHomologyData.mapRightHomologyIso_eq` / 引理 `RightHomologyData.mapRightHomologyIso_eq`

English:
lemma RightHomologyData.mapRightHomologyIso_eq
  statement: [S.HasRightHomology]
  proof: by
  ext
  dsimp [mapRightHomologyIso, rightHomologyIso]
  simp only [map_rightHomologyMap', ← rightHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

中文:
引理 RightHomologyData.mapRightHomologyIso_eq
  结论: [S.有RightHomology]
  证明: by
  ext
  dsimp [mapRightHomologyIso, rightHomologyIso]
  simp only [map_rightHomologyMap', ← rightHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Functor.map_id, _comp, comp_id, mapRightHomologyIso, mapShortComplex_obj, map_id, map_rightHomologyMap, rightHomologyIso, rightHomologyMap
-/
lemma RightHomologyData.mapRightHomologyIso_eq [S.HasRightHomology]
    [F.PreservesRightHomologyOf S] :
    S.mapRightHomologyIso F = (hr.map F).rightHomologyIso ≪≫
      F.mapIso hr.rightHomologyIso.symm := by
  ext
  dsimp [mapRightHomologyIso, rightHomologyIso]
  simp only [map_rightHomologyMap', ← rightHomologyMap'_comp, Functor.map_id, comp_id,
    Functor.mapShortComplex_obj]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `LeftHomologyData.mapHomologyIso_eq` / 引理 `LeftHomologyData.mapHomologyIso_eq`

English:
lemma LeftHomologyData.mapHomologyIso_eq
  statement: [S.HasHomology]
  proof: by
  ext
  dsimp only [mapHomologyIso, homologyIso, ShortComplex.leftHomologyIso,
    leftHomologyMapIso', leftHomologyIso, Functor.mapIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, Functor.map_id,
    Functor.mapShortComplex_obj]

中文:
引理 LeftHomologyData.mapHomologyIso_eq
  结论: [S.有同调]
  证明: by
  ext
  dsimp only [mapHomologyIso, homologyIso, ShortComplex.leftHomologyIso,
    leftHomologyMapIso', leftHomologyIso, Functor.mapIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, Functor.map_id,
    Functor.mapShortComplex_obj]

Depends on / 依赖: Functor, Functor.mapIso, Functor.mapShortComplex_obj, Functor.map_id, Iso.refl, Iso.symm, Iso.trans, ShortComplex, ShortComplex.leftHomologyIso, _comp, comp_id, homologyIso, leftHomologyIso, leftHomologyMap, leftHomologyMapIso, mapHomologyIso, mapIso, mapShortComplex_obj, map_id, map_leftHomologyMap
-/
lemma LeftHomologyData.mapHomologyIso_eq [S.HasHomology]
    [(S.map F).HasHomology] [F.PreservesLeftHomologyOf S] :
    S.mapHomologyIso F = (hl.map F).homologyIso ≪≫ F.mapIso hl.homologyIso.symm := by
  ext
  dsimp only [mapHomologyIso, homologyIso, ShortComplex.leftHomologyIso,
    leftHomologyMapIso', leftHomologyIso, Functor.mapIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, Functor.map_id,
    Functor.mapShortComplex_obj]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `RightHomologyData.mapHomologyIso'_eq` / 引理 `RightHomologyData.mapHomologyIso'_eq`

English:
lemma RightHomologyData.mapHomologyIso'_eq
  statement: [S.HasHomology]
  proof: by
  ext
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, mapHomologyIso', homologyIso,
    rightHomologyIso, rightHomologyMapIso', ShortComplex.rightHomologyIso]
  simp only [assoc, F.map_comp, map_rightHomologyMap', ← rightHomologyMap'_comp_assoc]

中文:
引理 RightHomologyData.mapHomologyIso'_eq
  结论: [S.有同调]
  证明: by
  ext
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, mapHomologyIso', homologyIso,
    rightHomologyIso, rightHomologyMapIso', ShortComplex.rightHomologyIso]
  simp only [assoc, F.map_comp, map_rightHomologyMap', ← rightHomologyMap'_comp_assoc]

Depends on / 依赖: F.map_comp, Functor, Functor.mapIso, Iso.refl, Iso.symm, Iso.trans, ShortComplex, ShortComplex.rightHomologyIso, _comp_assoc, homologyIso, mapHomologyIso, mapIso, map_comp, map_rightHomologyMap, rightHomologyIso, rightHomologyMap, rightHomologyMapIso
-/
lemma RightHomologyData.mapHomologyIso'_eq [S.HasHomology]
    [(S.map F).HasHomology] [F.PreservesRightHomologyOf S] :
    S.mapHomologyIso' F = (hr.map F).homologyIso ≪≫ F.mapIso hr.homologyIso.symm := by
  ext
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, mapHomologyIso', homologyIso,
    rightHomologyIso, rightHomologyMapIso', ShortComplex.rightHomologyIso]
  simp only [assoc, F.map_comp, map_rightHomologyMap', ← rightHomologyMap'_comp_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapCyclesIso_hom_naturality` / 引理 `mapCyclesIso_hom_naturality`

English:
lemma mapCyclesIso_hom_naturality
  statement: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  dsimp only [cyclesMap, mapCyclesIso, LeftHomologyData.cyclesIso, cyclesMapIso', Iso.refl]
  simp only [LeftHomologyData.map_cyclesMap', Functor.mapShortComplex_obj, ← cyclesMap'_comp,
    comp_id, id_comp]

中文:
引理 mapCyclesIso_hom_naturality
  结论: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  dsimp only [cyclesMap, mapCyclesIso, LeftHomologyData.cyclesIso, cyclesMapIso', Iso.refl]
  simp only [LeftHomologyData.map_cyclesMap', Functor.mapShortComplex_obj, ← cyclesMap'_comp,
    comp_id, id_comp]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Iso.refl, LeftHomologyData, LeftHomologyData.cyclesIso, LeftHomologyData.map_cyclesMap, _comp, comp_id, cyclesIso, cyclesMap, cyclesMapIso, id_comp, mapCyclesIso, mapShortComplex_obj, map_cyclesMap
-/
lemma mapCyclesIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    cyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapCyclesIso F).hom =
      (S₁.mapCyclesIso F).hom ≫ F.map (cyclesMap φ) := by
  dsimp only [cyclesMap, mapCyclesIso, LeftHomologyData.cyclesIso, cyclesMapIso', Iso.refl]
  simp only [LeftHomologyData.map_cyclesMap', Functor.mapShortComplex_obj, ← cyclesMap'_comp,
    comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapCyclesIso_inv_naturality` / 引理 `mapCyclesIso_inv_naturality`

English:
lemma mapCyclesIso_inv_naturality
  statement: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  rw [← cancel_epi (S₁.mapCyclesIso F).hom]; rw [← mapCyclesIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapCyclesIso_inv_naturality
  结论: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  rw [← cancel_epi (S₁.mapCyclesIso F).hom]; rw [← mapCyclesIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, mapCyclesIso, mapCyclesIso_hom_naturality_assoc
-/
lemma mapCyclesIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (cyclesMap φ) ≫ (S₂.mapCyclesIso F).inv =
      (S₁.mapCyclesIso F).inv ≫ cyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapCyclesIso F).hom]; rw [← mapCyclesIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapLeftHomologyIso_hom_naturality` / 引理 `mapLeftHomologyIso_hom_naturality`

English:
lemma mapLeftHomologyIso_hom_naturality
  statement: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  dsimp only [leftHomologyMap, mapLeftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', Functor.mapShortComplex_obj,
    ← leftHomologyMap'_comp, comp_id, id_comp]

中文:
引理 mapLeftHomologyIso_hom_naturality
  结论: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  dsimp only [leftHomologyMap, mapLeftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', Functor.mapShortComplex_obj,
    ← leftHomologyMap'_comp, comp_id, id_comp]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Iso.refl, LeftHomologyData, LeftHomologyData.leftHomologyIso, LeftHomologyData.map_leftHomologyMap, _comp, comp_id, id_comp, leftHomologyIso, leftHomologyMap, leftHomologyMapIso, mapLeftHomologyIso, mapShortComplex_obj, map_leftHomologyMap
-/
lemma mapLeftHomologyIso_hom_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    leftHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapLeftHomologyIso F).hom =
      (S₁.mapLeftHomologyIso F).hom ≫ F.map (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap, mapLeftHomologyIso, LeftHomologyData.leftHomologyIso,
    leftHomologyMapIso', Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', Functor.mapShortComplex_obj,
    ← leftHomologyMap'_comp, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapLeftHomologyIso_inv_naturality` / 引理 `mapLeftHomologyIso_inv_naturality`

English:
lemma mapLeftHomologyIso_inv_naturality
  statement: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  rw [← cancel_epi (S₁.mapLeftHomologyIso F).hom]; rw [← mapLeftHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapLeftHomologyIso_inv_naturality
  结论: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  rw [← cancel_epi (S₁.mapLeftHomologyIso F).hom]; rw [← mapLeftHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, mapLeftHomologyIso, mapLeftHomologyIso_hom_naturality_assoc
-/
lemma mapLeftHomologyIso_inv_naturality [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (leftHomologyMap φ) ≫ (S₂.mapLeftHomologyIso F).inv =
      (S₁.mapLeftHomologyIso F).inv ≫ leftHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapLeftHomologyIso F).hom]; rw [← mapLeftHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapOpcyclesIso_hom_naturality` / 引理 `mapOpcyclesIso_hom_naturality`

English:
lemma mapOpcyclesIso_hom_naturality
  statement: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  dsimp only [opcyclesMap, mapOpcyclesIso, RightHomologyData.opcyclesIso,
    opcyclesMapIso', Iso.refl]
  simp only [RightHomologyData.map_opcyclesMap', Functor.mapShortComplex_obj, ← opcyclesMap'_comp,
    comp_id, id_comp]

中文:
引理 mapOpcyclesIso_hom_naturality
  结论: [S₁.有RightHomology] [S₂.有RightHomology]
  证明: by
  dsimp only [opcyclesMap, mapOpcyclesIso, RightHomologyData.opcyclesIso,
    opcyclesMapIso', Iso.refl]
  simp only [RightHomologyData.map_opcyclesMap', Functor.mapShortComplex_obj, ← opcyclesMap'_comp,
    comp_id, id_comp]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Iso.refl, RightHomologyData, RightHomologyData.map_opcyclesMap, RightHomologyData.opcyclesIso, _comp, comp_id, id_comp, mapOpcyclesIso, mapShortComplex_obj, map_opcyclesMap, opcyclesIso, opcyclesMap, opcyclesMapIso
-/
lemma mapOpcyclesIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    opcyclesMap (F.mapShortComplex.map φ) ≫ (S₂.mapOpcyclesIso F).hom =
      (S₁.mapOpcyclesIso F).hom ≫ F.map (opcyclesMap φ) := by
  dsimp only [opcyclesMap, mapOpcyclesIso, RightHomologyData.opcyclesIso,
    opcyclesMapIso', Iso.refl]
  simp only [RightHomologyData.map_opcyclesMap', Functor.mapShortComplex_obj, ← opcyclesMap'_comp,
    comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapOpcyclesIso_inv_naturality` / 引理 `mapOpcyclesIso_inv_naturality`

English:
lemma mapOpcyclesIso_inv_naturality
  statement: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  rw [← cancel_epi (S₁.mapOpcyclesIso F).hom]; rw [← mapOpcyclesIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapOpcyclesIso_inv_naturality
  结论: [S₁.有RightHomology] [S₂.有RightHomology]
  证明: by
  rw [← cancel_epi (S₁.mapOpcyclesIso F).hom]; rw [← mapOpcyclesIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, mapOpcyclesIso, mapOpcyclesIso_hom_naturality_assoc
-/
lemma mapOpcyclesIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (opcyclesMap φ) ≫ (S₂.mapOpcyclesIso F).inv =
      (S₁.mapOpcyclesIso F).inv ≫ opcyclesMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapOpcyclesIso F).hom]; rw [← mapOpcyclesIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapRightHomologyIso_hom_naturality` / 引理 `mapRightHomologyIso_hom_naturality`

English:
lemma mapRightHomologyIso_hom_naturality
  statement: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  dsimp only [rightHomologyMap, mapRightHomologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', Iso.refl]
  simp only [RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    ← rightHomologyMap'_comp, comp_id, id_comp]

中文:
引理 mapRightHomologyIso_hom_naturality
  结论: [S₁.有RightHomology] [S₂.有RightHomology]
  证明: by
  dsimp only [rightHomologyMap, mapRightHomologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', Iso.refl]
  simp only [RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    ← rightHomologyMap'_comp, comp_id, id_comp]

Depends on / 依赖: Functor, Functor.mapShortComplex_obj, Iso.refl, RightHomologyData, RightHomologyData.map_rightHomologyMap, RightHomologyData.rightHomologyIso, _comp, comp_id, id_comp, mapRightHomologyIso, mapShortComplex_obj, map_rightHomologyMap, rightHomologyIso, rightHomologyMap, rightHomologyMapIso
-/
lemma mapRightHomologyIso_hom_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    rightHomologyMap (F.mapShortComplex.map φ) ≫ (S₂.mapRightHomologyIso F).hom =
      (S₁.mapRightHomologyIso F).hom ≫ F.map (rightHomologyMap φ) := by
  dsimp only [rightHomologyMap, mapRightHomologyIso, RightHomologyData.rightHomologyIso,
    rightHomologyMapIso', Iso.refl]
  simp only [RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    ← rightHomologyMap'_comp, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapRightHomologyIso_inv_naturality` / 引理 `mapRightHomologyIso_inv_naturality`

English:
lemma mapRightHomologyIso_inv_naturality
  statement: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  rw [← cancel_epi (S₁.mapRightHomologyIso F).hom]; rw [← mapRightHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapRightHomologyIso_inv_naturality
  结论: [S₁.有RightHomology] [S₂.有RightHomology]
  证明: by
  rw [← cancel_epi (S₁.mapRightHomologyIso F).hom]; rw [← mapRightHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, mapRightHomologyIso, mapRightHomologyIso_hom_naturality_assoc
-/
lemma mapRightHomologyIso_inv_naturality [S₁.HasRightHomology] [S₂.HasRightHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (rightHomologyMap φ) ≫ (S₂.mapRightHomologyIso F).inv =
      (S₁.mapRightHomologyIso F).inv ≫ rightHomologyMap (F.mapShortComplex.map φ) := by
  rw [← cancel_epi (S₁.mapRightHomologyIso F).hom]; rw [← mapRightHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapHomologyIso_hom_naturality` / 引理 `mapHomologyIso_hom_naturality`

English:
lemma mapHomologyIso_hom_naturality
  statement: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  dsimp only [homologyMap, homologyMap', mapHomologyIso, LeftHomologyData.homologyIso,
    LeftHomologyData.leftHomologyIso, leftHomologyMapIso', leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, id_comp]

@[reassoc]

中文:
引理 mapHomologyIso_hom_naturality
  结论: [S₁.有同调] [S₂.有同调]
  证明: by
  dsimp only [homologyMap, homologyMap', mapHomologyIso, LeftHomologyData.homologyIso,
    LeftHomologyData.leftHomologyIso, leftHomologyMapIso', leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, id_comp]

@[reassoc]

Depends on / 依赖: Iso.refl, Iso.symm, Iso.trans, LeftHomologyData, LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso, LeftHomologyData.map_leftHomologyMap, _comp, comp_id, homologyIso, homologyMap, id_comp, leftHomologyIso, leftHomologyMap, leftHomologyMapIso, mapHomologyIso, map_leftHomologyMap
-/
lemma mapHomologyIso_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ ≫
      (S₂.mapHomologyIso F).hom = (S₁.mapHomologyIso F).hom ≫ F.map (homologyMap φ) := by
  dsimp only [homologyMap, homologyMap', mapHomologyIso, LeftHomologyData.homologyIso,
    LeftHomologyData.leftHomologyIso, leftHomologyMapIso', leftHomologyIso,
    Iso.symm, Iso.trans, Iso.refl]
  simp only [LeftHomologyData.map_leftHomologyMap', ← leftHomologyMap'_comp, comp_id, id_comp]

@[reassoc]
/--
lemma `mapHomologyIso_inv_naturality` / 引理 `mapHomologyIso_inv_naturality`

English:
lemma mapHomologyIso_inv_naturality
  statement: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  rw [← cancel_epi (S₁.mapHomologyIso F).hom]; rw [← mapHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapHomologyIso_inv_naturality
  结论: [S₁.有同调] [S₂.有同调]
  证明: by
  rw [← cancel_epi (S₁.mapHomologyIso F).hom]; rw [← mapHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, mapHomologyIso, mapHomologyIso_hom_naturality_assoc
-/
lemma mapHomologyIso_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂] :
    F.map (homologyMap φ) ≫ (S₂.mapHomologyIso F).inv =
      (S₁.mapHomologyIso F).inv ≫
      @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ := by
  rw [← cancel_epi (S₁.mapHomologyIso F).hom]; rw [← mapHomologyIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `mapHomologyIso'_hom_naturality` / 引理 `mapHomologyIso'_hom_naturality`

English:
lemma mapHomologyIso'_hom_naturality
  statement: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, mapHomologyIso']
  simp only [← RightHomologyData.rightHomologyIso_hom_naturality_assoc _
    ((homologyData S₁).right.map F) ((homologyData S₂).right.map F), assoc,
    ← RightHomologyData.map_rightHomologyMap', ← F.map_comp,
    RightHomologyData.rightHomologyIso_inv_naturality _
      (homologyData S₁).right (homologyData S₂).right]

@[reassoc]

中文:
引理 mapHomologyIso'_hom_naturality
  结论: [S₁.有同调] [S₂.有同调]
  证明: by
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, mapHomologyIso']
  simp only [← RightHomologyData.rightHomologyIso_hom_naturality_assoc _
    ((homologyData S₁).right.map F) ((homologyData S₂).right.map F), assoc,
    ← RightHomologyData.map_rightHomologyMap', ← F.map_comp,
    RightHomologyData.rightHomologyIso_inv_naturality _
      (homologyData S₁).right (homologyData S₂).right]

@[reassoc]
-/
lemma mapHomologyIso'_hom_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ ≫
      (S₂.mapHomologyIso' F).hom = (S₁.mapHomologyIso' F).hom ≫ F.map (homologyMap φ) := by
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, mapHomologyIso']
  simp only [← RightHomologyData.rightHomologyIso_hom_naturality_assoc _
    ((homologyData S₁).right.map F) ((homologyData S₂).right.map F), assoc,
    ← RightHomologyData.map_rightHomologyMap', ← F.map_comp,
    RightHomologyData.rightHomologyIso_inv_naturality _
      (homologyData S₁).right (homologyData S₂).right]

@[reassoc]
/--
lemma `mapHomologyIso'_inv_naturality` / 引理 `mapHomologyIso'_inv_naturality`

English:
lemma mapHomologyIso'_inv_naturality
  statement: [S₁.HasHomology] [S₂.HasHomology]
  proof: by
  rw [← cancel_epi (S₁.mapHomologyIso' F).hom]; rw [← mapHomologyIso'_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

中文:
引理 mapHomologyIso'_inv_naturality
  结论: [S₁.有同调] [S₂.有同调]
  证明: by
  rw [← cancel_epi (S₁.mapHomologyIso' F).hom]; rw [← mapHomologyIso'_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]
-/
lemma mapHomologyIso'_inv_naturality [S₁.HasHomology] [S₂.HasHomology]
    [(S₁.map F).HasHomology] [(S₂.map F).HasHomology]
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂] :
    F.map (homologyMap φ) ≫ (S₂.mapHomologyIso' F).inv = (S₁.mapHomologyIso' F).inv ≫
      @homologyMap _ _ _ (S₁.map F) (S₂.map F) (F.mapShortComplex.map φ) _ _ := by
  rw [← cancel_epi (S₁.mapHomologyIso' F).hom]; rw [← mapHomologyIso'_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [Iso.hom_inv_id_assoc]

variable (S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mapHomologyIso'_eq_mapHomologyIso` / 引理 `mapHomologyIso'_eq_mapHomologyIso`

English:
lemma mapHomologyIso'_eq_mapHomologyIso
  statement: [S.HasHomology] [F.PreservesLeftHomologyOf S]
  proof: by
  ext
  rw [S.homologyData.left.mapHomologyIso_eq F]; rw [S.homologyData.right.mapHomologyIso'_eq F]
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso, LeftHomologyData.homologyIso,
    leftHomologyIso, LeftHomologyData.leftHomologyIso]
  simp only [RightHomologyData.map_H, rightHomologyMapIso'_inv, rightHomologyMapIso'_hom, assoc,
    Functor.map_comp, RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    Functor.map_id, LeftHomologyData.map_H, leftHomologyMapIso'_inv, leftHomologyMapIso'_hom,
    LeftHomologyData.map_leftHomologyMap', ← rightHomologyMap'_comp_assoc, ← leftHomologyMap'_comp,
    id_comp]
  have γ : HomologyMapData (𝟙 (S.map F)) (map S F).homologyData (S.homologyData.map F) := default
  have eq := γ.comm
  rw [← γ.left.leftHomologyMap'_eq]; rw [← γ.right.rightHomologyMap'_eq] at eq
  dsimp at eq
  simp only [← reassoc_of% eq, ← F.map_comp, Iso.hom_inv_id, F.map_id, comp_id]

中文:
引理 mapHomologyIso'_eq_mapHomologyIso
  结论: [S.有同调] [F.保持LeftHomologyOf S]
  证明: by
  ext
  rw [S.homologyData.left.mapHomologyIso_eq F]; rw [S.homologyData.right.mapHomologyIso'_eq F]
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso, LeftHomologyData.homologyIso,
    leftHomologyIso, LeftHomologyData.leftHomologyIso]
  simp only [RightHomologyData.map_H, rightHomologyMapIso'_inv, rightHomologyMapIso'_hom, assoc,
    Functor.map_comp, RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    Functor.map_id, LeftHomologyData.map_H, leftHomologyMapIso'_inv, leftHomologyMapIso'_hom,
    LeftHomologyData.map_leftHomologyMap', ← rightHomologyMap'_comp_assoc, ← leftHomologyMap'_comp,
    id_comp]
  have γ : HomologyMapData (𝟙 (S.map F)) (map S F).homologyData (S.homologyData.map F) := default
  have eq := γ.comm
  rw [← γ.left.leftHomologyMap'_eq]; rw [← γ.right.rightHomologyMap'_eq] at eq
  dsimp at eq
  simp only [← reassoc_of% eq, ← F.map_comp, Iso.hom_inv_id, F.map_id, comp_id]
-/
lemma mapHomologyIso'_eq_mapHomologyIso [S.HasHomology] [F.PreservesLeftHomologyOf S]
    [F.PreservesRightHomologyOf S] :
    S.mapHomologyIso' F = S.mapHomologyIso F := by
  ext
  rw [S.homologyData.left.mapHomologyIso_eq F]; rw [S.homologyData.right.mapHomologyIso'_eq F]
  dsimp only [Iso.trans, Iso.symm, Iso.refl, Functor.mapIso, RightHomologyData.homologyIso,
    rightHomologyIso, RightHomologyData.rightHomologyIso, LeftHomologyData.homologyIso,
    leftHomologyIso, LeftHomologyData.leftHomologyIso]
  simp only [RightHomologyData.map_H, rightHomologyMapIso'_inv, rightHomologyMapIso'_hom, assoc,
    Functor.map_comp, RightHomologyData.map_rightHomologyMap', Functor.mapShortComplex_obj,
    Functor.map_id, LeftHomologyData.map_H, leftHomologyMapIso'_inv, leftHomologyMapIso'_hom,
    LeftHomologyData.map_leftHomologyMap', ← rightHomologyMap'_comp_assoc, ← leftHomologyMap'_comp,
    id_comp]
  have γ : HomologyMapData (𝟙 (S.map F)) (map S F).homologyData (S.homologyData.map F) := default
  have eq := γ.comm
  rw [← γ.left.leftHomologyMap'_eq]; rw [← γ.right.rightHomologyMap'_eq] at eq
  dsimp at eq
  simp only [← reassoc_of% eq, ← F.map_comp, Iso.hom_inv_id, F.map_id, comp_id]

end

section

variable {S}
  {F G : C ⥤ D} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S]
  [F.PreservesRightHomologyOf S] [G.PreservesRightHomologyOf S]

set_option backward.defeqAttrib.useBackward true in
/-- Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preserve
the left homology of a short complex `S`, and a left homology data for `S`,
this is the left homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`. -/
@[simps]
/--
Definition of `LeftHomologyMapData.natTransApp` / `LeftHomologyMapData.natTransApp` 的定义

English:
definition LeftHomologyMapData.natTransApp
  signature: (h : LeftHomologyData S) (τ : F ⟶ G)
  body: τ.app h.K
  φH := τ.app h.H

中文:
定义 LeftHomologyMapData.natTransApp
  签名: (h : LeftHomologyData S) (τ : F ⟶ G)
  定义体: τ.app h.K
  φH := τ.app h.H
-/
noncomputable def LeftHomologyMapData.natTransApp (h : LeftHomologyData S) (τ : F ⟶ G) :
    LeftHomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  φK := τ.app h.K
  φH := τ.app h.H

set_option backward.defeqAttrib.useBackward true in
/-- Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preserve
the right homology of a short complex `S`, and a right homology data for `S`,
this is the right homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`. -/
@[simps]
/--
Definition of `RightHomologyMapData.natTransApp` / `RightHomologyMapData.natTransApp` 的定义

English:
definition RightHomologyMapData.natTransApp
  signature: (h : RightHomologyData S) (τ : F ⟶ G)
  body: τ.app h.Q
  φH := τ.app h.H

中文:
定义 RightHomologyMapData.natTransApp
  签名: (h : RightHomologyData S) (τ : F ⟶ G)
  定义体: τ.app h.Q
  φH := τ.app h.H
-/
noncomputable def RightHomologyMapData.natTransApp (h : RightHomologyData S) (τ : F ⟶ G) :
    RightHomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  φQ := τ.app h.Q
  φH := τ.app h.H

/-- Given a natural transformation `τ : F ⟶ G` between functors `C ⥤ D` which preserve
the homology of a short complex `S`, and a homology data for `S`,
this is the homology map data for the morphism `S.mapNatTrans τ`
obtained by evaluating `τ`. -/
@[simps]
/--
Definition of `HomologyMapData.natTransApp` / `HomologyMapData.natTransApp` 的定义

English:
definition HomologyMapData.natTransApp
  signature: (h : HomologyData S) (τ : F ⟶ G)
  body: LeftHomologyMapData.natTransApp h.left τ
  right := RightHomologyMapData.natTransApp h.right τ

中文:
定义 同调映射数据.natTransApp
  签名: (h : 同调数据 S) (τ : F ⟶ G)
  定义体: LeftHomologyMapData.natTransApp h.left τ
  right := RightHomologyMapData.natTransApp h.right τ

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.natTransApp, h.left, natTransApp
-/
noncomputable def HomologyMapData.natTransApp (h : HomologyData S) (τ : F ⟶ G) :
    HomologyMapData (S.mapNatTrans τ) (h.map F) (h.map G) where
  left := LeftHomologyMapData.natTransApp h.left τ
  right := RightHomologyMapData.natTransApp h.right τ

variable (S)

/--
lemma `homologyMap_mapNatTrans` / 引理 `homologyMap_mapNatTrans`

English:
lemma homologyMap_mapNatTrans
  given: [S.HasHomology] (τ : F ⟶ G)
  proof: (LeftHomologyMapData.natTransApp S.homologyData.left τ).homologyMap_eq

中文:
引理 homologyMap_map自然数Trans
  条件: [S.有同调] (τ : F ⟶ G)
  证明: (LeftHomologyMapData.natTransApp S.homologyData.left τ).homologyMap_eq

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.natTransApp, S.homologyData.left, homologyData, homologyMap_eq, natTransApp
-/
lemma homologyMap_mapNatTrans [S.HasHomology] (τ : F ⟶ G) :
    homologyMap (S.mapNatTrans τ) =
      (S.mapHomologyIso F).hom ≫ τ.app S.homology ≫ (S.mapHomologyIso G).inv :=
  (LeftHomologyMapData.natTransApp S.homologyData.left τ).homologyMap_eq

end

section

variable [HasKernels C] [HasCokernels C] [HasKernels D] [HasCokernels D]

/--
Definition of `cyclesFunctorIso` / `cyclesFunctorIso` 的定义

English:
definition cyclesFunctorIso
  signature: [F.PreservesHomology]
  body: NatIso.ofComponents (fun S => S.mapCyclesIso F)
    (fun f => ShortComplex.mapCyclesIso_hom_naturality f F)

中文:
定义 cyclesFunctorIso
  签名: [F.保持同调]
  定义体: NatIso.ofComponents (fun S => S.mapCyclesIso F)
    (fun f => ShortComplex.mapCyclesIso_hom_naturality f F)

Depends on / 依赖: NatIso, NatIso.ofComponents, S.mapCyclesIso, ShortComplex, ShortComplex.mapCyclesIso_hom_naturality, mapCyclesIso, mapCyclesIso_hom_naturality, ofComponents
-/
noncomputable def cyclesFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.cyclesFunctor D ≅
      ShortComplex.cyclesFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapCyclesIso F)
    (fun f => ShortComplex.mapCyclesIso_hom_naturality f F)

/--
Definition of `leftHomologyFunctorIso` / `leftHomologyFunctorIso` 的定义

English:
definition leftHomologyFunctorIso
  signature: [F.PreservesHomology]
  body: NatIso.ofComponents (fun S => S.mapLeftHomologyIso F)
    (fun f => ShortComplex.mapLeftHomologyIso_hom_naturality f F)

中文:
定义 leftHomologyFunctorIso
  签名: [F.保持同调]
  定义体: NatIso.ofComponents (fun S => S.mapLeftHomologyIso F)
    (fun f => ShortComplex.mapLeftHomologyIso_hom_naturality f F)

Depends on / 依赖: NatIso, NatIso.ofComponents, S.mapLeftHomologyIso, ShortComplex, ShortComplex.mapLeftHomologyIso_hom_naturality, mapLeftHomologyIso, mapLeftHomologyIso_hom_naturality, ofComponents
-/
noncomputable def leftHomologyFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.leftHomologyFunctor D ≅
      ShortComplex.leftHomologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapLeftHomologyIso F)
    (fun f => ShortComplex.mapLeftHomologyIso_hom_naturality f F)

/--
Definition of `opcyclesFunctorIso` / `opcyclesFunctorIso` 的定义

English:
definition opcyclesFunctorIso
  signature: [F.PreservesHomology]
  body: NatIso.ofComponents (fun S => S.mapOpcyclesIso F)
    (fun f => ShortComplex.mapOpcyclesIso_hom_naturality f F)

中文:
定义 opcyclesFunctorIso
  签名: [F.保持同调]
  定义体: NatIso.ofComponents (fun S => S.mapOpcyclesIso F)
    (fun f => ShortComplex.mapOpcyclesIso_hom_naturality f F)

Depends on / 依赖: NatIso, NatIso.ofComponents, S.mapOpcyclesIso, ShortComplex, ShortComplex.mapOpcyclesIso_hom_naturality, mapOpcyclesIso, mapOpcyclesIso_hom_naturality, ofComponents
-/
noncomputable def opcyclesFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.opcyclesFunctor D ≅
      ShortComplex.opcyclesFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapOpcyclesIso F)
    (fun f => ShortComplex.mapOpcyclesIso_hom_naturality f F)

/--
Definition of `rightHomologyFunctorIso` / `rightHomologyFunctorIso` 的定义

English:
definition rightHomologyFunctorIso
  signature: [F.PreservesHomology]
  body: NatIso.ofComponents (fun S => S.mapRightHomologyIso F)
    (fun f => ShortComplex.mapRightHomologyIso_hom_naturality f F)

中文:
定义 rightHomologyFunctorIso
  签名: [F.保持同调]
  定义体: NatIso.ofComponents (fun S => S.mapRightHomologyIso F)
    (fun f => ShortComplex.mapRightHomologyIso_hom_naturality f F)

Depends on / 依赖: NatIso, NatIso.ofComponents, S.mapRightHomologyIso, ShortComplex, ShortComplex.mapRightHomologyIso_hom_naturality, mapRightHomologyIso, mapRightHomologyIso_hom_naturality, ofComponents
-/
noncomputable def rightHomologyFunctorIso [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.rightHomologyFunctor D ≅
      ShortComplex.rightHomologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapRightHomologyIso F)
    (fun f => ShortComplex.mapRightHomologyIso_hom_naturality f F)

end

/--
Definition of `homologyFunctorIso` / `homologyFunctorIso` 的定义

English:
definition homologyFunctorIso
  body: NatIso.ofComponents (fun S => S.mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality f F)

中文:
定义 homologyFunctorIso
  定义体: NatIso.ofComponents (fun S => S.mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality f F)

Depends on / 依赖: NatIso, NatIso.ofComponents, S.mapHomologyIso, ShortComplex, ShortComplex.mapHomologyIso_hom_naturality, mapHomologyIso, mapHomologyIso_hom_naturality, ofComponents
-/
noncomputable def homologyFunctorIso
    [CategoryWithHomology C] [CategoryWithHomology D] [F.PreservesHomology] :
    F.mapShortComplex ⋙ ShortComplex.homologyFunctor D ≅
      ShortComplex.homologyFunctor C ⋙ F :=
  NatIso.ofComponents (fun S => S.mapHomologyIso F)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality f F)

section

variable
  {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
  {hl₁ : S₁.LeftHomologyData} {hr₁ : S₁.RightHomologyData}
  {hl₂ : S₂.LeftHomologyData} {hr₂ : S₂.RightHomologyData}
  (ψl : LeftHomologyMapData φ hl₁ hl₂)
  (ψr : RightHomologyMapData φ hr₁ hr₂)

/--
lemma `LeftHomologyMapData.quasiIso_map_iff` / 引理 `LeftHomologyMapData.quasiIso_map_iff`

English:
lemma LeftHomologyMapData.quasiIso_map_iff
  proof: (ψl.map F).quasiIso_iff

中文:
引理 LeftHomologyMapData.quasiIso_map_iff
  证明: (ψl.map F).quasiIso_iff

Depends on / 依赖: l.map, quasiIso_iff
-/
lemma LeftHomologyMapData.quasiIso_map_iff
    [(F.mapShortComplex.obj S₁).HasHomology]
    [(F.mapShortComplex.obj S₂).HasHomology]
    [hl₁.IsPreservedBy F] [hl₂.IsPreservedBy F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ IsIso (F.map ψl.φH) :=
  (ψl.map F).quasiIso_iff

/--
lemma `RightHomologyMapData.quasiIso_map_iff` / 引理 `RightHomologyMapData.quasiIso_map_iff`

English:
lemma RightHomologyMapData.quasiIso_map_iff
  proof: (ψr.map F).quasiIso_iff

中文:
引理 RightHomologyMapData.quasiIso_map_iff
  证明: (ψr.map F).quasiIso_iff

Depends on / 依赖: quasiIso_iff, r.map
-/
lemma RightHomologyMapData.quasiIso_map_iff
    [(F.mapShortComplex.obj S₁).HasHomology]
    [(F.mapShortComplex.obj S₂).HasHomology]
    [hr₁.IsPreservedBy F] [hr₂.IsPreservedBy F] :
    QuasiIso (F.mapShortComplex.map φ) ↔ IsIso (F.map ψr.φH) :=
  (ψr.map F).quasiIso_iff

variable (φ) [S₁.HasHomology] [S₂.HasHomology]
    [(F.mapShortComplex.obj S₁).HasHomology] [(F.mapShortComplex.obj S₂).HasHomology]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `quasiIso_map_of_preservesLeftHomology` / 实例 `quasiIso_map_of_preservesLeftHomology`

English:
instance quasiIso_map_of_preservesLeftHomology
  body: by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff]; rw [LeftHomologyMapData.map_φH]
  infer_instance

中文:
实例 quasiIso_map_of_preservesLeftHomology
  定义体: by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff]; rw [LeftHomologyMapData.map_φH]
  infer_instance

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.map_, infer_instance, leftHomologyData, quasiIso_iff
-/
instance quasiIso_map_of_preservesLeftHomology
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ) := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff]; rw [LeftHomologyMapData.map_φH]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_map_iff_of_preservesLeftHomology` / 引理 `quasiIso_map_iff_of_preservesLeftHomology`

English:
lemma quasiIso_map_iff_of_preservesLeftHomology
  proof: by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  rw [γ.quasiIso_iff]; rw [(γ.map F).quasiIso_iff]; rw [LeftHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

中文:
引理 quasiIso_map_iff_of_preservesLeftHomology
  证明: by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  rw [γ.quasiIso_iff]; rw [(γ.map F).quasiIso_iff]; rw [LeftHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.map_, infer_instance, isIso_of_reflects_iso, leftHomologyData, quasiIso_iff
-/
lemma quasiIso_map_iff_of_preservesLeftHomology
    [F.PreservesLeftHomologyOf S₁] [F.PreservesLeftHomologyOf S₂]
    [F.ReflectsIsomorphisms] :
    QuasiIso (F.mapShortComplex.map φ) ↔ QuasiIso φ := by
  have γ : LeftHomologyMapData φ S₁.leftHomologyData S₂.leftHomologyData := default
  rw [γ.quasiIso_iff]; rw [(γ.map F).quasiIso_iff]; rw [LeftHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `quasiIso_map_of_preservesRightHomology` / 实例 `quasiIso_map_of_preservesRightHomology`

English:
instance quasiIso_map_of_preservesRightHomology
  body: by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff]; rw [RightHomologyMapData.map_φH]
  infer_instance

中文:
实例 quasiIso_map_of_preservesRightHomology
  定义体: by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff]; rw [RightHomologyMapData.map_φH]
  infer_instance

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.map_, infer_instance, quasiIso_iff, rightHomologyData
-/
instance quasiIso_map_of_preservesRightHomology
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂]
    [QuasiIso φ] : QuasiIso (F.mapShortComplex.map φ) := by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  have : IsIso γ.φH := by
    rw [← γ.quasiIso_iff]
    infer_instance
  rw [(γ.map F).quasiIso_iff]; rw [RightHomologyMapData.map_φH]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_map_iff_of_preservesRightHomology` / 引理 `quasiIso_map_iff_of_preservesRightHomology`

English:
lemma quasiIso_map_iff_of_preservesRightHomology
  proof: by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  rw [γ.quasiIso_iff]; rw [(γ.map F).quasiIso_iff]; rw [RightHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

中文:
引理 quasiIso_map_iff_of_preservesRightHomology
  证明: by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  rw [γ.quasiIso_iff]; rw [(γ.map F).quasiIso_iff]; rw [RightHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.map_, infer_instance, isIso_of_reflects_iso, quasiIso_iff, rightHomologyData
-/
lemma quasiIso_map_iff_of_preservesRightHomology
    [F.PreservesRightHomologyOf S₁] [F.PreservesRightHomologyOf S₂]
    [F.ReflectsIsomorphisms] :
    QuasiIso (F.mapShortComplex.map φ) ↔ QuasiIso φ := by
  have γ : RightHomologyMapData φ S₁.rightHomologyData S₂.rightHomologyData := default
  rw [γ.quasiIso_iff]; rw [(γ.map F).quasiIso_iff]; rw [RightHomologyMapData.map_φH]
  constructor
  · intro
    exact isIso_of_reflects_iso _ F
  · intro
    infer_instance

end

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [F.PreservesZeroMorphisms] (S : ShortComplex C)

/--
lemma `preservesLeftHomology_of_zero_f` / 引理 `preservesLeftHomology_of_zero_f`

English:
lemma preservesLeftHomology_of_zero_f
  statement: (hf : S.f = 0)
  proof: ⟨fun h =>
  { g := by infer_instance
    f' := Limits.preservesCokernel_zero' _ _
      (by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]) }⟩

中文:
引理 preservesLeftHomology_of_zero_f
  结论: (hf : S.f = 0)
  证明: ⟨fun h =>
  { g := by infer_instance
    f' := Limits.preservesCokernel_zero' _ _
      (by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]) }⟩
-/
lemma preservesLeftHomology_of_zero_f (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by infer_instance
    f' := Limits.preservesCokernel_zero' _ _
      (by rw [← cancel_mono h.i, h.f'_i, zero_comp, hf]) }⟩

/--
lemma `preservesRightHomology_of_zero_g` / 引理 `preservesRightHomology_of_zero_g`

English:
lemma preservesRightHomology_of_zero_g
  statement: (hg : S.g = 0)
  proof: ⟨fun h =>
  { f := by infer_instance
    g' := Limits.preservesKernel_zero' _ _
      (by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]) }⟩

中文:
引理 preservesRightHomology_of_zero_g
  结论: (hg : S.g = 0)
  证明: ⟨fun h =>
  { f := by infer_instance
    g' := Limits.preservesKernel_zero' _ _
      (by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]) }⟩
-/
lemma preservesRightHomology_of_zero_g (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by infer_instance
    g' := Limits.preservesKernel_zero' _ _
      (by rw [← cancel_epi h.p, h.p_g', comp_zero, hg]) }⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesLeftHomology_of_zero_g` / 引理 `preservesLeftHomology_of_zero_g`

English:
lemma preservesLeftHomology_of_zero_g
  statement: (hg : S.g = 0)
  proof: ⟨fun h =>
  { g := by
      rw [hg]
      infer_instance
    f' := by
      have := h.isIso_i hg
      let e : parallelPair h.f' 0 ≅ parallelPair S.f 0 :=
        parallelPair.ext (Iso.refl _) (asIso h.i) (by simp) (by simp)
      exact Limits.preservesColimit_of_iso_diagram F e.symm}⟩

中文:
引理 preservesLeftHomology_of_zero_g
  结论: (hg : S.g = 0)
  证明: ⟨fun h =>
  { g := by
      rw [hg]
      infer_instance
    f' := by
      have := h.isIso_i hg
      let e : parallelPair h.f' 0 ≅ parallelPair S.f 0 :=
        parallelPair.ext (Iso.refl _) (asIso h.i) (by simp) (by simp)
      exact Limits.preservesColimit_of_iso_diagram F e.symm}⟩
-/
lemma preservesLeftHomology_of_zero_g (hg : S.g = 0)
    [PreservesColimit (parallelPair S.f 0) F] :
    F.PreservesLeftHomologyOf S := ⟨fun h =>
  { g := by
      rw [hg]
      infer_instance
    f' := by
      have := h.isIso_i hg
      let e : parallelPair h.f' 0 ≅ parallelPair S.f 0 :=
        parallelPair.ext (Iso.refl _) (asIso h.i) (by simp) (by simp)
      exact Limits.preservesColimit_of_iso_diagram F e.symm}⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesRightHomology_of_zero_f` / 引理 `preservesRightHomology_of_zero_f`

English:
lemma preservesRightHomology_of_zero_f
  statement: (hf : S.f = 0)
  proof: ⟨fun h =>
  { f := by
      rw [hf]
      infer_instance
    g' := by
      have := h.isIso_p hf
      let e : parallelPair S.g 0 ≅ parallelPair h.g' 0 :=
        parallelPair.ext (asIso h.p) (Iso.refl _) (by simp) (by simp)
      exact Limits.preservesLimit_of_iso_diagram F e }⟩

中文:
引理 preservesRightHomology_of_zero_f
  结论: (hf : S.f = 0)
  证明: ⟨fun h =>
  { f := by
      rw [hf]
      infer_instance
    g' := by
      have := h.isIso_p hf
      let e : parallelPair S.g 0 ≅ parallelPair h.g' 0 :=
        parallelPair.ext (asIso h.p) (Iso.refl _) (by simp) (by simp)
      exact Limits.preservesLimit_of_iso_diagram F e }⟩
-/
lemma preservesRightHomology_of_zero_f (hf : S.f = 0)
    [PreservesLimit (parallelPair S.g 0) F] :
    F.PreservesRightHomologyOf S := ⟨fun h =>
  { f := by
      rw [hf]
      infer_instance
    g' := by
      have := h.isIso_p hf
      let e : parallelPair S.g 0 ≅ parallelPair h.g' 0 :=
        parallelPair.ext (asIso h.p) (Iso.refl _) (by simp) (by simp)
      exact Limits.preservesLimit_of_iso_diagram F e }⟩

end Functor

/--
lemma `NatTrans.app_homology` / 引理 `NatTrans.app_homology`

English:
lemma NatTrans.app_homology
  statement: {F G : C ⥤ D} (τ : F ⟶ G)
  proof: by
  rw [ShortComplex.homologyMap_mapNatTrans]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [Iso.inv_hom_id_assoc]

中文:
引理 自然变换.app_homology
  结论: {F G : C ⥤ D} (τ : F ⟶ G)
  证明: by
  rw [ShortComplex.homologyMap_mapNatTrans]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id, Iso.inv_hom_id_assoc, ShortComplex, ShortComplex.homologyMap_mapNatTrans, comp_id, homologyMap_mapNatTrans, inv_hom_id, inv_hom_id_assoc
-/
lemma NatTrans.app_homology {F G : C ⥤ D} (τ : F ⟶ G)
    (S : ShortComplex C) [S.HasHomology] [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf S] [F.PreservesRightHomologyOf S]
    [G.PreservesRightHomologyOf S] :
    τ.app S.homology = (S.mapHomologyIso F).inv ≫
      ShortComplex.homologyMap (S.mapNatTrans τ) ≫ (S.mapHomologyIso G).hom := by
  rw [ShortComplex.homologyMap_mapNatTrans]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [Iso.inv_hom_id_assoc]

end CategoryTheory
