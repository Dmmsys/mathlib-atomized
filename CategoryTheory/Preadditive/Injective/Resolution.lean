/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Injective resolutions

An injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a quasi-isomorphism `I.ι` from the cochain complex consisting just of `Z`
in degree zero to `I.cocomplex`.
```
Z ----> 0 ----> ... ----> 0 ----> ...
| | |
| | |
v v v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/

@[expose] public section


noncomputable section

universe v u

namespace CategoryTheory

open Limits HomologicalComplex CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]
/--
Definition of `InjectiveResolution` / `InjectiveResolution` 的定义

English:
structure InjectiveResolution
  parameters: (Z : C)
  axioms and operations (5):
    - cocomplex : CochainComplex C Nat
    - injective : forall n, Injective (cocomplex.X n)  [default: by infer_instance]
    - [hasHomology : forall i, cocomplex.HasHomology i]
    - ι : (single₀ C).obj Z ⟶ cocomplex
    - quasiIso : QuasiIso ι  [default: by infer_instance]

中文:
结构 单射消解
  参数: (Z : C)
  公理与运算 (5 个):
    - cocomplex : 上链复形 C 自然数
    - injective : 对任意 n, 单射 (cocomplex.X n)  [默认: by infer_instance]
    - [hasHomology : 对任意 i, cocomplex.有同调 i]
    - ι : (single₀ C).obj Z ⟶ cocomplex
    - quasiIso : 拟同构 ι  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure InjectiveResolution (Z : C) where
  /-- the cochain complex involved in the resolution -/
  cocomplex : CochainComplex C Nat
  /-- the cochain complex must be degreewise injective -/
  injective : forall n, Injective (cocomplex.X n) := by infer_instance
  /-- the cochain complex must have homology -/
  [hasHomology : forall i, cocomplex.HasHomology i]
  /-- the morphism from the single cochain complex with `Z` in degree `0` -/
  ι : (single₀ C).obj Z ⟶ cocomplex
  /-- the morphism from the single cochain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso ι := by infer_instance

open InjectiveResolution in
attribute [instance] injective hasHomology InjectiveResolution.quasiIso

/--
Definition of `HasInjectiveResolution` / `HasInjectiveResolution` 的定义

English:
class HasInjectiveResolution
  parameters: (Z : C)
  axioms and operations (1):
    - out : Nonempty (InjectiveResolution Z)

中文:
类 有单射消解
  参数: (Z : C)
  公理与运算 (1 个):
    - out : 非空 (单射消解 Z)
-/
class HasInjectiveResolution (Z : C) : Prop where
  out : Nonempty (InjectiveResolution Z)

attribute [inherit_doc HasInjectiveResolution] HasInjectiveResolution.out

section

variable (C)

/--
Definition of `HasInjectiveResolutions` / `HasInjectiveResolutions` 的定义

English:
class HasInjectiveResolutions
  parameters: : Prop where
  axioms and operations (1):
    - out : forall Z : C, HasInjectiveResolution Z

中文:
类 有InjectiveResolutions
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 对任意 Z : C, 有单射消解 Z
-/
class HasInjectiveResolutions : Prop where
  out : forall Z : C, HasInjectiveResolution Z

attribute [instance 100] HasInjectiveResolutions.out

end

namespace InjectiveResolution

variable {Z : C} (I : InjectiveResolution Z)

/--
lemma `cocomplex_exactAt_succ` / 引理 `cocomplex_exactAt_succ`

English:
lemma cocomplex_exactAt_succ
  given: (n : Nat)
  proof: by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

中文:
引理 cocomplex_exactAt_succ
  条件: (n : 自然数)
  证明: by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

Depends on / 依赖: exactAt_succ_single_obj, infer_instance, quasiIsoAt_iff_exactAt
-/
lemma cocomplex_exactAt_succ (n : Nat) :
    I.cocomplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

/--
lemma `exact_succ` / 引理 `exact_succ`

English:
lemma exact_succ
  given: (n : Nat)
  proof: (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)

@[simp]

中文:
引理 exact_succ
  条件: (n : 自然数)
  证明: (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)

@[simp]

Depends on / 依赖: CochainComplex, CochainComplex.next, HomologicalComplex, HomologicalComplex.exactAt_iff, I.cocomplex_exactAt_succ, cocomplex_exactAt_succ, exactAt_iff
-/
lemma exact_succ (n : Nat) :
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)

@[simp]
/--
theorem `ι_f_succ` / 定理 `ι_f_succ`

English:
theorem ι_f_succ
  given: (n : Nat)
  statement: I.ι.f (n + 1) = 0
  proof: (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

中文:
定理 ι_f_succ
  条件: (n : 自然数)
  结论: I.ι.f (n + 1) = 0
  证明: (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

Depends on / 依赖: eq_of_src, isZero_single_obj_X
-/
theorem ι_f_succ (n : Nat) : I.ι.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `ι_f_zero_comp_complex_d` / 定理 `ι_f_zero_comp_complex_d`

English:
theorem ι_f_zero_comp_complex_d
  proof: by
  simp

中文:
定理 ι_f_zero_comp_complex_d
  证明: by
  simp
-/
theorem ι_f_zero_comp_complex_d :
    I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 := by
  simp

/--
theorem `complex_d_comp` / 定理 `complex_d_comp`

English:
theorem complex_d_comp
  given: (n : Nat)
  proof: by
  simp

中文:
定理 complex_d_comp
  条件: (n : 自然数)
  证明: by
  simp
-/
theorem complex_d_comp (n : Nat) :
    I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := by
  simp

/-- The (limit) kernel fork given by the composition
`Z ⟶ I.cocomplex.X 0 ⟶ I.cocomplex.X 1` when `I : InjectiveResolution Z`. -/
@[simp]
/--
Definition of `kernelFork` / `kernelFork` 的定义

English:
definition kernelFork
  signature: : KernelFork (I.cocomplex.d 0 1)
  body: KernelFork.ofι _ I.ι_f_zero_comp_complex_d

中文:
定义 kernelFork
  签名: : 核叉 (I.cocomplex.d 0 1)
  定义体: KernelFork.ofι _ I.ι_f_zero_comp_complex_d

Depends on / 依赖: KernelFork, KernelFork.of
-/
def kernelFork : KernelFork (I.cocomplex.d 0 1) :=
  KernelFork.ofι _ I.ι_f_zero_comp_complex_d

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: : IsLimit (I.kernelFork)
  body: by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up Nat) _ _).hom]; rw [← cancel_epi (isoHomologyπ₀ _).hom]; rw [← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up Nat) _ _).inv]
  simp

中文:
定义 isLimitKernelFork
  签名: : 是极限 (I.kernelFork)
  定义体: by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up Nat) _ _).hom]; rw [← cancel_epi (isoHomologyπ₀ _).hom]; rw [← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up Nat) _ _).inv]
  simp

Depends on / 依赖: ComplexShape, ComplexShape.up, Fork.ext, I.cocomplex.cyclesIsKernel, I.cocomplex.isoHomology, IsLimit, IsLimit.ofIsoLimit, Iso.symm, cancel_epi, cocomplex, cyclesIsKernel, isoOfQuasiIsoAt, ofIsoLimit, singleObjCyclesSelfIso, singleObjHomologySelfIso
-/
def isLimitKernelFork : IsLimit (I.kernelFork) := by
  refine IsLimit.ofIsoLimit (I.cocomplex.cyclesIsKernel 0 1 (by simp)) (Iso.symm ?_)
  refine Fork.ext ((singleObjHomologySelfIso _ _ _).symm ≪≫
    isoOfQuasiIsoAt I.ι 0 ≪≫ I.cocomplex.isoHomologyπ₀.symm) ?_
  rw [← cancel_epi (singleObjHomologySelfIso (ComplexShape.up Nat) _ _).hom]; rw [← cancel_epi (isoHomologyπ₀ _).hom]; rw [← cancel_epi (singleObjCyclesSelfIso (ComplexShape.up Nat) _ _).inv]
  simp

set_option backward.isDefEq.respectTransparency false in
instance (n : Nat) : Mono (I.ι.f n) := by
  cases n
  · exact mono_of_isLimit_fork I.isLimitKernelFork
  · rw [ι_f_succ]; infer_instance

variable (Z)

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
@[simps]
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: [Injective Z]
  body: (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
    cases n
    · simpa
    · apply IsZero.injective
      apply HomologicalComplex.isZero_single_obj_X
      simp

中文:
定义 self
  签名: [单射 Z]
  定义体: (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
    cases n
    · simpa
    · apply IsZero.injective
      apply HomologicalComplex.isZero_single_obj_X
      simp

Depends on / 依赖: CochainComplex, CochainComplex.single
-/
def self [Injective Z] : InjectiveResolution Z where
  cocomplex := (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  injective n := by
    cases n
    · simpa
    · apply IsZero.injective
      apply HomologicalComplex.isZero_single_obj_X
      simp

variable {Z} {Z' : C} (I' : InjectiveResolution Z')

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (f : Z ⟶ Z')
  axioms and operations (2):
    - hom : I.cocomplex ⟶ I'.cocomplex
    - ι_f_zero_comp_hom_f_zero : I.ι.f 0 ≫ hom.f 0 = ((single₀ C).map f).f 0 ≫ I'.ι.f 0

中文:
结构 态射
  参数: (f : Z ⟶ Z')
  公理与运算 (2 个):
    - hom : I.cocomplex ⟶ I'.cocomplex
    - ι_f_zero_comp_hom_f_zero : I.ι.f 0 ≫ hom.f 0 = ((single₀ C).map f).f 0 ≫ I'.ι.f 0
-/
structure Hom (f : Z ⟶ Z') where
  /-- A morphism between the cocomplexes -/
  hom : I.cocomplex ⟶ I'.cocomplex
  ι_f_zero_comp_hom_f_zero : I.ι.f 0 ≫ hom.f 0 = ((single₀ C).map f).f 0 ≫ I'.ι.f 0

namespace Hom

attribute [reassoc (attr := simp)] ι_f_zero_comp_hom_f_zero

set_option backward.isDefEq.respectTransparency false in
variable {I I'} in
@[reassoc (attr := simp)]
/--
lemma `ι_comp_hom` / 引理 `ι_comp_hom`

English:
lemma ι_comp_hom
  given: {f : Z ⟶ Z'} (φ : Hom I I' f)
  proof: by cat_disch

中文:
引理 ι_comp_hom
  条件: {f : Z ⟶ Z'} (φ : 态射 I I' f)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma ι_comp_hom {f : Z ⟶ Z'} (φ : Hom I I' f) :
    I.ι ≫ φ.hom = (single₀ C).map f ≫ I'.ι := by cat_disch

end Hom

end InjectiveResolution

end CategoryTheory
