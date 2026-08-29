/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.OfObjectProperty
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono

/-!
# Objects that are (co)kernels of morphisms

Given a morphism property `W` on a category, we introduce two object properties
`kernels W` and `cokernels W`, consisting of all (co)kernels of morphisms
satisfying `W`.

Given an object property `P`, we also introduce two predicates
`P.IsClosedUnderKernels` and `P.IsClosedUnderCokernels`, stating that all
(co)kernels of morphisms between objects in `P` remain in `P`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace MorphismProperty

variable (W : MorphismProperty C)

/--
Inductive type `kernels` / 归纳类型 `kernels`

English:
inductive kernels
  parameters: : ObjectProperty C
  constructors (1):
    - of_isLimit: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : KernelFork f) (hk : IsLimit k) (hf : W f) : kernels k.pt

中文:
归纳类型 kernels
  参数: : ObjectProperty C
  构造子 (1 个):
    - of_isLimit: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : 核叉 f) (hk : 是极限 k) (hf : W f) : kernels k.pt
-/
inductive kernels : ObjectProperty C
  | of_isLimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : KernelFork f) (hk : IsLimit k)
    (hf : W f) : kernels k.pt

/--
lemma `nonempty_kernels` / 引理 `nonempty_kernels`

English:
lemma nonempty_kernels
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f]
  proof: ObjectProperty.nonempty_of_prop (kernels.of_isLimit f _ (kernelIsKernel f) hf)

中文:
引理 nonempty_kernels
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f]
  证明: ObjectProperty.nonempty_of_prop (kernels.of_isLimit f _ (kernelIsKernel f) hf)

Depends on / 依赖: ObjectProperty, ObjectProperty.nonempty_of_prop, kernelIsKernel, kernels, kernels.of_isLimit, nonempty_of_prop, of_isLimit
-/
lemma nonempty_kernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasKernel f] :
    W.kernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (kernels.of_isLimit f _ (kernelIsKernel f) hf)

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.kernels.IsClosedUnderIsomorphisms
  body: by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isLimit f (KernelFork.ofι (i.inv ≫ k.ι) (by simp))
      (IsLimit.ofIsoLimit hk (Fork.ext i)) hf

中文:
实例 :
  签名: W.kernels.在同构下封闭
  定义体: by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isLimit f (KernelFork.ofι (i.inv ≫ k.ι) (by simp))
      (IsLimit.ofIsoLimit hk (Fork.ext i)) hf

Depends on / 依赖: Fork.ext, IsLimit, IsLimit.ofIsoLimit, KernelFork, KernelFork.of, i.inv, ofIsoLimit, of_isLimit
-/
instance : W.kernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isLimit f (KernelFork.ofι (i.inv ≫ k.ι) (by simp))
      (IsLimit.ofIsoLimit hk (Fork.ext i)) hf

/--
Inductive type `cokernels` / 归纳类型 `cokernels`

English:
inductive cokernels
  parameters: : ObjectProperty C
  constructors (1):
    - of_isColimit: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : CokernelCofork f) (hk : IsColimit k) (hf : W f) : cokernels k.pt

中文:
归纳类型 cokernels
  参数: : ObjectProperty C
  构造子 (1 个):
    - of_isColimit: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : 余核余叉 f) (hk : 是余极限 k) (hf : W f) : cokernels k.pt
-/
inductive cokernels : ObjectProperty C
  | of_isColimit {X₁ X₂ : C} (f : X₁ ⟶ X₂) (k : CokernelCofork f) (hk : IsColimit k)
    (hf : W f) : cokernels k.pt

/--
lemma `nonempty_cokernels` / 引理 `nonempty_cokernels`

English:
lemma nonempty_cokernels
  given: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f]
  proof: ObjectProperty.nonempty_of_prop (cokernels.of_isColimit f _ (cokernelIsCokernel f) hf)

中文:
引理 nonempty_cokernels
  条件: {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f]
  证明: ObjectProperty.nonempty_of_prop (cokernels.of_isColimit f _ (cokernelIsCokernel f) hf)

Depends on / 依赖: ObjectProperty, ObjectProperty.nonempty_of_prop, cokernelIsCokernel, cokernels, cokernels.of_isColimit, nonempty_of_prop, of_isColimit
-/
lemma nonempty_cokernels {X₁ X₂ : C} (f : X₁ ⟶ X₂) (hf : W f) [HasCokernel f] :
    W.cokernels.Nonempty :=
  ObjectProperty.nonempty_of_prop (cokernels.of_isColimit f _ (cokernelIsCokernel f) hf)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: W.cokernels.IsClosedUnderIsomorphisms
  body: by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isColimit f (CokernelCofork.ofπ (k.π ≫ i.hom) (by simp))
      (IsColimit.ofIsoColimit hk (Cofork.ext i)) hf

中文:
实例 :
  签名: W.cokernels.在同构下封闭
  定义体: by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isColimit f (CokernelCofork.ofπ (k.π ≫ i.hom) (by simp))
      (IsColimit.ofIsoColimit hk (Cofork.ext i)) hf

Depends on / 依赖: Cofork, Cofork.ext, CokernelCofork, CokernelCofork.of, IsColimit, IsColimit.ofIsoColimit, i.hom, ofIsoColimit, of_isColimit
-/
instance : W.cokernels.IsClosedUnderIsomorphisms where
  of_iso := by
    rintro _ _ i ⟨f, k, hk, hf⟩
    exact .of_isColimit f (CokernelCofork.ofπ (k.π ≫ i.hom) (by simp))
      (IsColimit.ofIsoColimit hk (Cofork.ext i)) hf

end MorphismProperty

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- A property of objects satisfies `P.IsClosedUnderKernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
/--
Definition of `IsClosedUnderKernels` / `IsClosedUnderKernels` 的定义

English:
class IsClosedUnderKernels
  parameters: : Prop where
  axioms and operations (1):
    - kernels_le : (MorphismProperty.ofObjectProperty P P).kernels <= P

中文:
类 是ClosedUnderKernels
  参数: : 命题 where
  公理与运算 (1 个):
    - kernels_le : (MorphismProperty.ofObjectProperty P P).kernels <= P
-/
class IsClosedUnderKernels : Prop where
  kernels_le : (MorphismProperty.ofObjectProperty P P).kernels <= P

/--
lemma `prop_of_isLimit_kernelFork` / 引理 `prop_of_isLimit_kernelFork`

English:
lemma prop_of_isLimit_kernelFork
  statement: [P.IsClosedUnderKernels] {X Y : C} {f : X ⟶ Y} {k : KernelFork f}
  proof: IsClosedUnderKernels.kernels_le _ (.of_isLimit _ k hk ⟨hX, hY⟩)

中文:
引理 prop_of_isLimit_kernelFork
  结论: [P.是ClosedUnderKernels] {X Y : C} {f : X ⟶ Y} {k : 核叉 f}
  证明: IsClosedUnderKernels.kernels_le _ (.of_isLimit _ k hk ⟨hX, hY⟩)

Depends on / 依赖: IsClosedUnderKernels, IsClosedUnderKernels.kernels_le, kernels_le, of_isLimit
-/
lemma prop_of_isLimit_kernelFork [P.IsClosedUnderKernels] {X Y : C} {f : X ⟶ Y} {k : KernelFork f}
    (hk : IsLimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderKernels.kernels_le _ (.of_isLimit _ k hk ⟨hX, hY⟩)

/--
lemma `prop_kernel` / 引理 `prop_kernel`

English:
lemma prop_kernel
  statement: [P.IsClosedUnderKernels] {X Y : C} (f : X ⟶ Y) [HasKernel f] (hX : P X)
  proof: (P.prop_of_isLimit_kernelFork (kernelIsKernel f) hX hY :)

中文:
引理 prop_kernel
  结论: [P.是ClosedUnderKernels] {X Y : C} (f : X ⟶ Y) [HasKernel f] (hX : P X)
  证明: (P.prop_of_isLimit_kernelFork (kernelIsKernel f) hX hY :)

Depends on / 依赖: P.prop_of_isLimit_kernelFork, kernelIsKernel, prop_of_isLimit_kernelFork
-/
lemma prop_kernel [P.IsClosedUnderKernels] {X Y : C} (f : X ⟶ Y) [HasKernel f] (hX : P X)
    (hY : P Y) : P (kernel f) :=
  (P.prop_of_isLimit_kernelFork (kernelIsKernel f) hX hY :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderSubobjects]
  signature: : P.IsClosedUnderKernels where
  body: by
    intro _ ⟨_, k, hk, hf⟩
    let := Fork.IsLimit.mono hk
    exact P.prop_of_mono k.ι hf.1

中文:
实例 [P.是ClosedUnderSubobjects]
  签名: : P.是ClosedUnderKernels where
  定义体: by
    intro _ ⟨_, k, hk, hf⟩
    let := Fork.IsLimit.mono hk
    exact P.prop_of_mono k.ι hf.1

Depends on / 依赖: Fork.IsLimit.mono, IsLimit, P.prop_of_mono, PUnit.unit, cat_disch, prop_of_mono
-/
instance [P.IsClosedUnderSubobjects] : P.IsClosedUnderKernels where
  kernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    let := Fork.IsLimit.mono hk
    exact P.prop_of_mono k.ι hf.1

/--
lemma `hasLimit_parallelPair_comp_ι` / 引理 `hasLimit_parallelPair_comp_ι`

English:
lemma hasLimit_parallelPair_comp_ι
  given: {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasKernel f.hom]
  proof: hasLimit_of_iso (F := parallelPair f.hom 0) (Iso.symm (diagramIsoParallelPair _))

中文:
引理 hasLimit_parallelPair_comp_ι
  条件: {X Y : P.满子范畴} (f : X ⟶ Y) [HasKernel f.hom]
  证明: hasLimit_of_iso (F := parallelPair f.hom 0) (Iso.symm (diagramIsoParallelPair _))

Depends on / 依赖: Iso.symm, diagramIsoParallelPair, f.hom, hasLimit_of_iso, parallelPair
-/
lemma hasLimit_parallelPair_comp_ι {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasKernel f.hom] :
    HasLimit (parallelPair f 0 ⋙ P.ι) :=
  hasLimit_of_iso (F := parallelPair f.hom 0) (Iso.symm (diagramIsoParallelPair _))

set_option backward.defeqAttrib.useBackward true in
/-- If an object property `P` is closed under kernels, then `P.ι` creates kernels.
In particular, this implies `P.ι` preserves kernels. -/
@[reducible]
/--
Definition of `createsKernels` / `createsKernels` 的定义

English:
definition createsKernels
  signature: [P.IsClosedUnderKernels] {X Y : P.FullSubcategory}
  body: by
  fapply createsLimitFullSubcategoryInclusion'
  · exact (Cone.postcompose (Iso.symm (diagramIsoParallelPair _)).hom).obj
      (Fork.ofι (kernel.ι f.hom) (by simp))
  · exact (IsLimit.postcomposeInvEquiv _ _).symm (kernelIsKernel f.hom)
  · exact P.prop_kernel f.hom X.property Y.property

中文:
定义 createsKernels
  签名: [P.是ClosedUnderKernels] {X Y : P.满子范畴}
  定义体: by
  fapply createsLimitFullSubcategoryInclusion'
  · exact (Cone.postcompose (Iso.symm (diagramIsoParallelPair _)).hom).obj
      (Fork.ofι (kernel.ι f.hom) (by simp))
  · exact (IsLimit.postcomposeInvEquiv _ _).symm (kernelIsKernel f.hom)
  · exact P.prop_kernel f.hom X.property Y.property

Depends on / 依赖: Cone.postcompose, Fork.of, IsLimit, IsLimit.postcomposeInvEquiv, Iso.symm, P.prop_kernel, X.property, Y.property, createsLimitFullSubcategoryInclusion, diagramIsoParallelPair, f.hom, fapply, kernel, kernelIsKernel, postcompose, postcomposeInvEquiv, prop_kernel, property
-/
noncomputable def createsKernels [P.IsClosedUnderKernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasKernel f.hom] : CreatesLimit (parallelPair f 0) P.ι := by
  fapply createsLimitFullSubcategoryInclusion'
  · exact (Cone.postcompose (Iso.symm (diagramIsoParallelPair _)).hom).obj
      (Fork.ofι (kernel.ι f.hom) (by simp))
  · exact (IsLimit.postcomposeInvEquiv _ _).symm (kernelIsKernel f.hom)
  · exact P.prop_kernel f.hom X.property Y.property

/--
lemma `preservesKernels_ι` / 引理 `preservesKernels_ι`

English:
lemma preservesKernels_ι
  given: [HasKernels C] [P.IsClosedUnderKernels] ⦃X Y
  statement: P.FullSubcategory⦄
  proof: by
  have := P.createsKernels f
  have := P.hasLimit_parallelPair_comp_ι f
  exact preservesLimit_of_createsLimit_and_hasLimit _ _

中文:
引理 preservesKernels_ι
  条件: [有Kernels C] [P.是ClosedUnderKernels] ⦃X Y
  结论: P.满子范畴⦄
  证明: by
  have := P.createsKernels f
  have := P.hasLimit_parallelPair_comp_ι f
  exact preservesLimit_of_createsLimit_and_hasLimit _ _

Depends on / 依赖: P.createsKernels, P.hasLimit_parallelPair_comp_, createsKernels, preservesLimit_of_createsLimit_and_hasLimit
-/
lemma preservesKernels_ι [HasKernels C] [P.IsClosedUnderKernels] ⦃X Y : P.FullSubcategory⦄
    (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) P.ι := by
  have := P.createsKernels f
  have := P.hasLimit_parallelPair_comp_ι f
  exact preservesLimit_of_createsLimit_and_hasLimit _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderKernels]
  signature: [HasKernels C]
  body: letI := P.createsKernels f
    letI := P.hasLimit_parallelPair_comp_ι f
    hasLimit_of_created _ P.ι

中文:
实例 [P.是ClosedUnderKernels]
  签名: [有Kernels C]
  定义体: letI := P.createsKernels f
    letI := P.hasLimit_parallelPair_comp_ι f
    hasLimit_of_created _ P.ι

Depends on / 依赖: P.createsKernels, P.hasLimit_parallelPair_comp_, createsKernels, hasLimit_of_created
-/
instance [P.IsClosedUnderKernels] [HasKernels C] : HasKernels P.FullSubcategory where
  has_limit f :=
    letI := P.createsKernels f
    letI := P.hasLimit_parallelPair_comp_ι f
    hasLimit_of_created _ P.ι

/-- A property of objects satisfies `P.IsClosedUnderCokernels` if whenever `X` and `Y`
satisfy `P`, all kernels of morphisms from `X` to `Y` satisfy `P`. -/
@[mk_iff]
/--
Definition of `IsClosedUnderCokernels` / `IsClosedUnderCokernels` 的定义

English:
class IsClosedUnderCokernels
  parameters: : Prop where
  axioms and operations (1):
    - cokernels_le : (MorphismProperty.ofObjectProperty P P).cokernels <= P

中文:
类 是ClosedUnderCokernels
  参数: : 命题 where
  公理与运算 (1 个):
    - cokernels_le : (MorphismProperty.ofObjectProperty P P).cokernels <= P
-/
class IsClosedUnderCokernels : Prop where
  cokernels_le : (MorphismProperty.ofObjectProperty P P).cokernels <= P

/--
lemma `prop_of_isColimit_cokernelCofork` / 引理 `prop_of_isColimit_cokernelCofork`

English:
lemma prop_of_isColimit_cokernelCofork
  statement: [P.IsClosedUnderCokernels] {X Y : C} {f : X ⟶ Y}
  proof: IsClosedUnderCokernels.cokernels_le _ (.of_isColimit _ k hk ⟨hX, hY⟩)

中文:
引理 prop_of_isColimit_cokernelCofork
  结论: [P.是ClosedUnderCokernels] {X Y : C} {f : X ⟶ Y}
  证明: IsClosedUnderCokernels.cokernels_le _ (.of_isColimit _ k hk ⟨hX, hY⟩)

Depends on / 依赖: IsClosedUnderCokernels, IsClosedUnderCokernels.cokernels_le, cokernels_le, of_isColimit
-/
lemma prop_of_isColimit_cokernelCofork [P.IsClosedUnderCokernels] {X Y : C} {f : X ⟶ Y}
    {k : CokernelCofork f} (hk : IsColimit k) (hX : P X) (hY : P Y) : P k.pt :=
  IsClosedUnderCokernels.cokernels_le _ (.of_isColimit _ k hk ⟨hX, hY⟩)

/--
lemma `prop_cokernel` / 引理 `prop_cokernel`

English:
lemma prop_cokernel
  statement: [P.IsClosedUnderCokernels] {X Y : C} (f : X ⟶ Y) [HasCokernel f] (hX : P X)
  proof: (P.prop_of_isColimit_cokernelCofork (cokernelIsCokernel f) hX hY :)

中文:
引理 prop_cokernel
  结论: [P.是ClosedUnderCokernels] {X Y : C} (f : X ⟶ Y) [HasCokernel f] (hX : P X)
  证明: (P.prop_of_isColimit_cokernelCofork (cokernelIsCokernel f) hX hY :)

Depends on / 依赖: P.prop_of_isColimit_cokernelCofork, cokernelIsCokernel, prop_of_isColimit_cokernelCofork
-/
lemma prop_cokernel [P.IsClosedUnderCokernels] {X Y : C} (f : X ⟶ Y) [HasCokernel f] (hX : P X)
    (hY : P Y) : P (cokernel f) :=
  (P.prop_of_isColimit_cokernelCofork (cokernelIsCokernel f) hX hY :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderQuotients]
  signature: : P.IsClosedUnderCokernels where
  body: by
    intro _ ⟨_, k, hk, hf⟩
    let := Cofork.IsColimit.epi hk
    exact P.prop_of_epi k.π hf.2

中文:
实例 [P.是ClosedUnderQuotients]
  签名: : P.是ClosedUnderCokernels where
  定义体: by
    intro _ ⟨_, k, hk, hf⟩
    let := Cofork.IsColimit.epi hk
    exact P.prop_of_epi k.π hf.2

Depends on / 依赖: Cofork, Cofork.IsColimit.epi, IsColimit, P.prop_of_epi, prop_of_epi
-/
instance [P.IsClosedUnderQuotients] : P.IsClosedUnderCokernels where
  cokernels_le := by
    intro _ ⟨_, k, hk, hf⟩
    let := Cofork.IsColimit.epi hk
    exact P.prop_of_epi k.π hf.2

/--
lemma `hasColimit_parallelPair_comp_ι` / 引理 `hasColimit_parallelPair_comp_ι`

English:
lemma hasColimit_parallelPair_comp_ι
  given: {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom]
  proof: hasColimit_of_iso (F := parallelPair f.hom 0) (diagramIsoParallelPair _)

中文:
引理 hasColimit_parallelPair_comp_ι
  条件: {X Y : P.满子范畴} (f : X ⟶ Y) [HasCokernel f.hom]
  证明: hasColimit_of_iso (F := parallelPair f.hom 0) (diagramIsoParallelPair _)

Depends on / 依赖: diagramIsoParallelPair, f.hom, hasColimit_of_iso, parallelPair
-/
lemma hasColimit_parallelPair_comp_ι {X Y : P.FullSubcategory} (f : X ⟶ Y) [HasCokernel f.hom] :
    HasColimit (parallelPair f 0 ⋙ P.ι) :=
  hasColimit_of_iso (F := parallelPair f.hom 0) (diagramIsoParallelPair _)

set_option backward.defeqAttrib.useBackward true in
/-- If an object property `P` is closed under cokernels, then `P.ι` creates cokernels.
In particular, this implies `P.ι` preserves cokernels. -/
@[reducible]
/--
Definition of `createsCokernels` / `createsCokernels` 的定义

English:
definition createsCokernels
  signature: [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory}
  body: by
  fapply createsColimitFullSubcategoryInclusion'
  · exact (Cocone.precompose (diagramIsoParallelPair _).hom).obj
      (Cofork.ofπ (cokernel.π f.hom) (by simp))
  · exact (IsColimit.precomposeHomEquiv _ _).symm (cokernelIsCokernel f.hom)
  · exact P.prop_cokernel f.hom X.property Y.property

中文:
定义 createsCokernels
  签名: [P.是ClosedUnderCokernels] {X Y : P.满子范畴}
  定义体: by
  fapply createsColimitFullSubcategoryInclusion'
  · exact (Cocone.precompose (diagramIsoParallelPair _).hom).obj
      (Cofork.ofπ (cokernel.π f.hom) (by simp))
  · exact (IsColimit.precomposeHomEquiv _ _).symm (cokernelIsCokernel f.hom)
  · exact P.prop_cokernel f.hom X.property Y.property

Depends on / 依赖: Cocone, Cocone.precompose, Cofork, Cofork.of, IsColimit, IsColimit.precomposeHomEquiv, P.prop_cokernel, X.property, Y.property, cokernel, cokernelIsCokernel, createsColimitFullSubcategoryInclusion, diagramIsoParallelPair, f.hom, fapply, precompose, precomposeHomEquiv, prop_cokernel, property
-/
noncomputable def createsCokernels [P.IsClosedUnderCokernels] {X Y : P.FullSubcategory}
    (f : X ⟶ Y) [HasCokernel f.hom] : CreatesColimit (parallelPair f 0) P.ι := by
  fapply createsColimitFullSubcategoryInclusion'
  · exact (Cocone.precompose (diagramIsoParallelPair _).hom).obj
      (Cofork.ofπ (cokernel.π f.hom) (by simp))
  · exact (IsColimit.precomposeHomEquiv _ _).symm (cokernelIsCokernel f.hom)
  · exact P.prop_cokernel f.hom X.property Y.property

/--
lemma `preservesCokernels_ι` / 引理 `preservesCokernels_ι`

English:
lemma preservesCokernels_ι
  given: [HasCokernels C] [P.IsClosedUnderCokernels] ⦃X Y
  statement: P.FullSubcategory⦄
  proof: by
  have := P.createsCokernels f
  have := P.hasColimit_parallelPair_comp_ι f
  exact preservesColimit_of_createsColimit_and_hasColimit _ _

中文:
引理 preservesCokernels_ι
  条件: [有余kernels C] [P.是ClosedUnderCokernels] ⦃X Y
  结论: P.满子范畴⦄
  证明: by
  have := P.createsCokernels f
  have := P.hasColimit_parallelPair_comp_ι f
  exact preservesColimit_of_createsColimit_and_hasColimit _ _

Depends on / 依赖: P.createsCokernels, P.hasColimit_parallelPair_comp_, createsCokernels, preservesColimit_of_createsColimit_and_hasColimit
-/
lemma preservesCokernels_ι [HasCokernels C] [P.IsClosedUnderCokernels] ⦃X Y : P.FullSubcategory⦄
    (f : X ⟶ Y) : PreservesColimit (parallelPair f 0) P.ι := by
  have := P.createsCokernels f
  have := P.hasColimit_parallelPair_comp_ι f
  exact preservesColimit_of_createsColimit_and_hasColimit _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderCokernels]
  signature: [HasCokernels C]
  body: letI := P.createsCokernels f
    letI := P.hasColimit_parallelPair_comp_ι f
    hasColimit_of_created _ P.ι

中文:
实例 [P.是ClosedUnderCokernels]
  签名: [有余kernels C]
  定义体: letI := P.createsCokernels f
    letI := P.hasColimit_parallelPair_comp_ι f
    hasColimit_of_created _ P.ι

Depends on / 依赖: P.createsCokernels, P.hasColimit_parallelPair_comp_, createsCokernels, hasColimit_of_created
-/
instance [P.IsClosedUnderCokernels] [HasCokernels C] : HasCokernels P.FullSubcategory where
  has_colimit f :=
    letI := P.createsCokernels f
    letI := P.hasColimit_parallelPair_comp_ι f
    hasColimit_of_created _ P.ι

end ObjectProperty

end CategoryTheory
