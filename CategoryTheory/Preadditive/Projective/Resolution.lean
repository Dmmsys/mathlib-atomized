/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

-/

@[expose] public section


universe v u v' u'

namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex

variable {C : Type u} [Category.{v} C]

open Projective

variable [HasZeroObject C] [HasZeroMorphisms C]

/--
Definition of `ProjectiveResolution` / `ProjectiveResolution` 的定义

English:
structure ProjectiveResolution
  parameters: (Z : C)
  axioms and operations (5):
    - complex : ChainComplex C Nat
    - projective : forall n, Projective (complex.X n)  [default: by infer_instance]
    - [hasHomology : forall i, complex.HasHomology i]
    - π : complex ⟶ (ChainComplex.single₀ C).obj Z
    - quasiIso : QuasiIso π  [default: by infer_instance]

中文:
结构 投射消解
  参数: (Z : C)
  公理与运算 (5 个):
    - complex : 链复形 C 自然数
    - projective : 对任意 n, 投射 (complex.X n)  [默认: by infer_instance]
    - [hasHomology : 对任意 i, complex.有同调 i]
    - π : complex ⟶ (链复形.single₀ C).obj Z
    - quasiIso : 拟同构 π  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure ProjectiveResolution (Z : C) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex C Nat
  /-- the chain complex must be degreewise projective -/
  projective : forall n, Projective (complex.X n) := by infer_instance
  /-- the chain complex must have homology -/
  [hasHomology : forall i, complex.HasHomology i]
  /-- the morphism to the single chain complex with `Z` in degree `0` -/
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso π := by infer_instance

open ProjectiveResolution in
attribute [instance] projective hasHomology ProjectiveResolution.quasiIso

/--
Definition of `HasProjectiveResolution` / `HasProjectiveResolution` 的定义

English:
class HasProjectiveResolution
  parameters: (Z : C)
  axioms and operations (1):
    - out : Nonempty (ProjectiveResolution Z)

中文:
类 有投射消解
  参数: (Z : C)
  公理与运算 (1 个):
    - out : 非空 (投射消解 Z)
-/
class HasProjectiveResolution (Z : C) : Prop where
  out : Nonempty (ProjectiveResolution Z)

variable (C)

/--
Definition of `HasProjectiveResolutions` / `HasProjectiveResolutions` 的定义

English:
class HasProjectiveResolutions
  parameters: : Prop where
  axioms and operations (1):
    - out : forall Z : C, HasProjectiveResolution Z

中文:
类 有ProjectiveResolutions
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 对任意 Z : C, 有投射消解 Z

Depends on / 依赖: Fintype, Fintype.ofSurjective, ofComposition, ofComposition_surj, ofSurjective
-/
class HasProjectiveResolutions : Prop where
  out : forall Z : C, HasProjectiveResolution Z

attribute [instance 100] HasProjectiveResolutions.out

namespace ProjectiveResolution

variable {C}
variable {Z : C} (P : ProjectiveResolution Z)

/--
lemma `complex_exactAt_succ` / 引理 `complex_exactAt_succ`

English:
lemma complex_exactAt_succ
  given: (n : Nat)
  proof: by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

中文:
引理 complex_exactAt_succ
  条件: (n : 自然数)
  证明: by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

Depends on / 依赖: exactAt_succ_single_obj, infer_instance, quasiIsoAt_iff_exactAt
-/
lemma complex_exactAt_succ (n : Nat) :
    P.complex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

/--
lemma `exact_succ` / 引理 `exact_succ`

English:
lemma exact_succ
  given: (n : Nat)
  proof: ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)

@[simp]

中文:
引理 exact_succ
  条件: (n : 自然数)
  证明: ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)

@[simp]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.exactAt_iff, P.complex_exactAt_succ, complex_exactAt_succ, exactAt_iff
-/
lemma exact_succ (n : Nat) :
    (ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)

@[simp]
/--
theorem `π_f_succ` / 定理 `π_f_succ`

English:
theorem π_f_succ
  given: (n : Nat)
  statement: P.π.f (n + 1) = 0
  proof: (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]

中文:
定理 π_f_succ
  条件: (n : 自然数)
  结论: P.π.f (n + 1) = 0
  证明: (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]

Depends on / 依赖: eq_of_tgt, isZero_single_obj_X
-/
theorem π_f_succ (n : Nat) : P.π.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]
/--
theorem `complex_d_comp_π_f_zero` / 定理 `complex_d_comp_π_f_zero`

English:
theorem complex_d_comp_π_f_zero
  proof: by
  rw [← P.π.comm 1 0]; rw [single_obj_d]; rw [comp_zero]

中文:
定理 complex_d_comp_π_f_zero
  证明: by
  rw [← P.π.comm 1 0]; rw [single_obj_d]; rw [comp_zero]

Depends on / 依赖: comp_zero, single_obj_d
-/
theorem complex_d_comp_π_f_zero :
    P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  rw [← P.π.comm 1 0]; rw [single_obj_d]; rw [comp_zero]

/--
theorem `complex_d_succ_comp` / 定理 `complex_d_succ_comp`

English:
theorem complex_d_succ_comp
  given: (n : Nat)
  proof: by
  simp

中文:
定理 complex_d_succ_comp
  条件: (n : 自然数)
  证明: by
  simp
-/
theorem complex_d_succ_comp (n : Nat) :
    P.complex.d n (n + 1) ≫ P.complex.d (n + 1) (n + 2) = 0 := by
  simp

/-- The (limit) cokernel cofork given by the composition
`P.complex.X 1 ⟶ P.complex.X 0 ⟶ Z` when `P : ProjectiveResolution Z`. -/
@[simp]
/--
Definition of `cokernelCofork` / `cokernelCofork` 的定义

English:
definition cokernelCofork
  signature: : CokernelCofork (P.complex.d 1 0)
  body: CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

中文:
定义 cokernelCofork
  签名: : 余核余叉 (P.complex.d 1 0)
  定义体: CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

Depends on / 依赖: CokernelCofork, CokernelCofork.of, P.complex_d_comp_
-/
noncomputable def cokernelCofork : CokernelCofork (P.complex.d 1 0) :=
  CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: : IsColimit (P.cokernelCofork)
  body: by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down Nat) 0 _).inv]; rw [← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

中文:
定义 isColimitCokernelCofork
  签名: : 是余极限 (P.cokernelCofork)
  定义体: by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down Nat) 0 _).inv]; rw [← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

Depends on / 依赖: Cofork, Cofork.ext, ComplexShape, ComplexShape.down, IsColimit, IsColimit.ofIsoColimit, Iso.hom_inv_id, P.complex.isoHomology, P.complex.opcyclesIsCokernel, cancel_mono, comp_id, complex, hom_inv_id, isoOfQuasiIsoAt, ofIsoColimit, opcyclesIsCokernel, p_opcyclesMap_assoc, singleObjHomologySelfIso
-/
noncomputable def isColimitCokernelCofork : IsColimit (P.cokernelCofork) := by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down Nat) 0 _).inv]; rw [← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

set_option backward.isDefEq.respectTransparency false in
instance (n : Nat) : Epi (P.π.f n) := by
  cases n
  · exact epi_of_isColimit_cofork P.isColimitCokernelCofork
  · rw [π_f_succ]; infer_instance

variable (Z)

/-- A projective object admits a trivial projective resolution: itself in degree 0. -/
@[simps]
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: [Projective Z]
  body: (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · simpa
    · apply IsZero.projective
      apply HomologicalComplex.isZero_single_obj_X
      simp

中文:
定义 self
  签名: [投射 Z]
  定义体: (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · simpa
    · apply IsZero.projective
      apply HomologicalComplex.isZero_single_obj_X
      simp

Depends on / 依赖: ChainComplex, ChainComplex.single
-/
noncomputable def self [Projective Z] : ProjectiveResolution Z where
  complex := (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · simpa
    · apply IsZero.projective
      apply HomologicalComplex.isZero_single_obj_X
      simp

variable {Z} {Z' : C} (P' : ProjectiveResolution Z')

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (f : Z ⟶ Z')
  axioms and operations (2):
    - hom : P.complex ⟶ P'.complex
    - hom_f_zero_comp_π_f_zero : hom.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ ((single₀ C).map f).f 0

中文:
结构 态射
  参数: (f : Z ⟶ Z')
  公理与运算 (2 个):
    - hom : P.complex ⟶ P'.complex
    - hom_f_zero_comp_π_f_zero : hom.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ ((single₀ C).map f).f 0
-/
structure Hom (f : Z ⟶ Z') where
  /-- A morphism between the cocomplexes -/
  hom : P.complex ⟶ P'.complex
  hom_f_zero_comp_π_f_zero : hom.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ ((single₀ C).map f).f 0

namespace Hom

attribute [reassoc (attr := simp)] hom_f_zero_comp_π_f_zero

set_option backward.isDefEq.respectTransparency false in
variable {I I'} in
@[reassoc (attr := simp)]
/--
lemma `hom_comp_π` / 引理 `hom_comp_π`

English:
lemma hom_comp_π
  given: {f : Z ⟶ Z'} (φ : Hom P P' f)
  proof: by cat_disch

中文:
引理 hom_comp_π
  条件: {f : Z ⟶ Z'} (φ : 态射 P P' f)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma hom_comp_π {f : Z ⟶ Z'} (φ : Hom P P' f) :
    φ.hom ≫ P'.π = P.π ≫ (single₀ C).map f := by cat_disch

end Hom

end ProjectiveResolution

namespace Functor

open Limits

variable {C : Type u} [Category* C] [HasZeroObject C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [CategoryWithHomology D]

/-- An additive functor `F` which preserves homology and sends projective objects to projective
objects sends a projective resolution of `Z` to a projective resolution of `F.obj Z`. -/
@[simps complex π]
/--
Definition of `mapProjectiveResolution` / `mapProjectiveResolution` 的定义

English:
definition mapProjectiveResolution
  signature: (F : C ⥤ D) [F.Additive]
  body: (F.mapHomologicalComplex _).obj P.complex
  projective n := PreservesProjectiveObjects.projective_obj (P.projective n)
  π := (F.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

中文:
定义 mapProjectiveResolution
  签名: (F : C ⥤ D) [F.加性]
  定义体: (F.mapHomologicalComplex _).obj P.complex
  projective n := PreservesProjectiveObjects.projective_obj (P.projective n)
  π := (F.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

Depends on / 依赖: F.mapHomologicalComplex, P.complex, complex, mapHomologicalComplex
-/
noncomputable def mapProjectiveResolution (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] [F.PreservesHomology] {Z : C} (P : ProjectiveResolution Z) :
    ProjectiveResolution (F.obj Z) where
  complex := (F.mapHomologicalComplex _).obj P.complex
  projective n := PreservesProjectiveObjects.projective_obj (P.projective n)
  π := (F.mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

end CategoryTheory.Functor
