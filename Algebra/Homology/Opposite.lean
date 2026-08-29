/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Amelia Livingston, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Opposite categories of complexes

Given a preadditive category `V`, the opposite of its category of chain complexes is equivalent to
the category of cochain complexes of objects in `Vᵒᵖ`. We define this equivalence, and another
analogous equivalence (for a general category of homological complexes with a general
complex shape).

We then show that when `V` is abelian, if `C` is a homological complex, then the homology of
`op(C)` is isomorphic to `op` of the homology of `C` (and the analogous result for `unop`).

## Implementation notes
It is convenient to define both `op` and `opSymm`; this is because given a complex shape `c`,
`c.symm.symm` is not defeq to `c`.

## Tags
opposite, chain complex, cochain complex, homology, cohomology, homological complex
-/

@[expose] public section


noncomputable section

open Opposite CategoryTheory CategoryTheory.Limits

section

variable {V : Type*} [Category* V] [Abelian V]

/--
theorem `imageToKernel_op` / 定理 `imageToKernel_op`

English:
theorem imageToKernel_op
  given: {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  proof: by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelOpOp_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc,
    ← imageSubobject_arrow, ← imageUnopOp_inv_comp_op_factorThruImage g.op]
  rfl

中文:
定理 imageToKernel_op
  条件: {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  证明: by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelOpOp_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc,
    ← imageSubobject_arrow, ← imageUnopOp_inv_comp_op_factorThruImage g.op]
  rfl

Depends on / 依赖: Category, Category.assoc, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, cokernel, g.op, imageSubobject_arrow, imageToKernel_arrow, imageUnopOp_inv_comp_op_factorThruImage, kernel, kernel.lift_, kernelOpOp_inv, kernelSubobject_arrow, op_comp, symm_hom, trans_hom, trans_inv
-/
theorem imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.op f.op (by rw [← op_comp, w, op_zero]) =
      (imageSubobjectIso _ ≪≫ (imageOpOp _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).op ≫
          (kernelSubobjectIso _ ≪≫ kernelOpOp _).inv := by
  ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelOpOp_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, ← op_comp, cokernel.π_desc,
    ← imageSubobject_arrow, ← imageUnopOp_inv_comp_op_factorThruImage g.op]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `imageToKernel_unop` / 定理 `imageToKernel_unop`

English:
theorem imageToKernel_unop
  given: {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  proof: by
  ext
  dsimp only [imageUnopUnop]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelUnopUnop_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, cokernel.π_desc, Iso.unop_inv,
    ← unop_comp, factorThruImage_comp_imageUnopOp_inv, Quiver.Hom.unop_op, imageSubobject_arrow]

中文:
定理 imageToKernel_unop
  条件: {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0)
  证明: by
  ext
  dsimp only [imageUnopUnop]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelUnopUnop_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, cokernel.π_desc, Iso.unop_inv,
    ← unop_comp, factorThruImage_comp_imageUnopOp_inv, Quiver.Hom.unop_op, imageSubobject_arrow]

Depends on / 依赖: Category, Category.assoc, Iso.symm_hom, Iso.trans_hom, Iso.trans_inv, Iso.unop_inv, Quiver, Quiver.Hom.unop_op, cokernel, factorThruImage_comp_imageUnopOp_inv, imageSubobject_arrow, imageToKernel_arrow, imageUnopUnop, kernel, kernel.lift_, kernelSubobject_arrow, kernelUnopUnop_inv, symm_hom, trans_hom, trans_inv
-/
theorem imageToKernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    imageToKernel g.unop f.unop (by rw [← unop_comp, w, unop_zero]) =
      (imageSubobjectIso _ ≪≫ (imageUnopUnop _).symm).hom ≫
        (cokernel.desc f (factorThruImage g)
              (by rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).unop ≫
          (kernelSubobjectIso _ ≪≫ kernelUnopUnop _).inv := by
  ext
  dsimp only [imageUnopUnop]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, kernelUnopUnop_inv, Category.assoc,
    imageToKernel_arrow, kernelSubobject_arrow', kernel.lift_ι, cokernel.π_desc, Iso.unop_inv,
    ← unop_comp, factorThruImage_comp_imageUnopOp_inv, Quiver.Hom.unop_op, imageSubobject_arrow]

end

namespace HomologicalComplex

variable {ι V : Type*} [Category* V] {c : ComplexShape ι}

section

variable [HasZeroMorphisms V]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (X : HomologicalComplex V c)
  body: op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

中文:
定义 op
  签名: (X : 同调复形 V c)
  定义体: op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]
-/
protected def op (X : HomologicalComplex V c) : HomologicalComplex Vᵒᵖ c.symm where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
/--
Definition of `opSymm` / `opSymm` 的定义

English:
definition opSymm
  signature: (X : HomologicalComplex V c.symm)
  body: op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

中文:
定义 opSymm
  签名: (X : 同调复形 V c.symm)
  定义体: op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]
-/
protected def opSymm (X : HomologicalComplex V c.symm) : HomologicalComplex Vᵒᵖ c where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (X : HomologicalComplex Vᵒᵖ c)
  body: unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

中文:
定义 unop
  签名: (X : 同调复形 Vᵒᵖ c)
  定义体: unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]
-/
protected def unop (X : HomologicalComplex Vᵒᵖ c) : HomologicalComplex V c.symm where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
/--
Definition of `unopSymm` / `unopSymm` 的定义

English:
definition unopSymm
  signature: (X : HomologicalComplex Vᵒᵖ c.symm)
  body: unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

中文:
定义 unopSymm
  签名: (X : 同调复形 Vᵒᵖ c.symm)
  定义体: unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]
-/
protected def unopSymm (X : HomologicalComplex Vᵒᵖ c.symm) : HomologicalComplex V c where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

variable (V c)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
/--
Definition of `opFunctor` / `opFunctor` 的定义

English:
definition opFunctor
  signature: : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm where
  body: (unop X).op
  map f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j _ => by simp only [op_d, ← op_comp, f.unop.comm] }

中文:
定义 opFunctor
  签名: : (同调复形 V c)ᵒᵖ ⥤ 同调复形 Vᵒᵖ c.symm where
  定义体: (unop X).op
  map f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j _ => by simp only [op_d, ← op_comp, f.unop.comm] }
-/
def opFunctor : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm where
  obj X := (unop X).op
  map f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j _ => by simp only [op_d, ← op_comp, f.unop.comm] }

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
/--
Definition of `opInverse` / `opInverse` 的定义

English:
definition opInverse
  signature: : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ where
  body: op X.unopSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).unop
      comm' := fun i j _ => by simp only [unopSymm_d, ← unop_comp, f.comm] }

中文:
定义 opInverse
  签名: : 同调复形 Vᵒᵖ c.symm ⥤ (同调复形 V c)ᵒᵖ where
  定义体: op X.unopSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).unop
      comm' := fun i j _ => by simp only [unopSymm_d, ← unop_comp, f.comm] }

Depends on / 依赖: X.unopSymm, unopSymm
-/
def opInverse : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ where
  obj X := op X.unopSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).unop
      comm' := fun i j _ => by simp only [unopSymm_d, ← unop_comp, f.comm] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `opUnitIso` / `opUnitIso` 的定义

English:
definition opUnitIso
  signature: : 𝟭 (HomologicalComplex V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c
  body: NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

中文:
定义 opUnitIso
  签名: : 𝟭 (同调复形 V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c
  定义体: NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, Iso.refl_hom, NatIso, NatIso.ofComponents, Opposite, Opposite.unop, Quiver, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, comp_id, id_comp, isoOfComponents, ofComponents, op.unopSymm, op_d
-/
def opUnitIso : 𝟭 (HomologicalComplex V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `opCounitIso` / `opCounitIso` 的定义

English:
definition opCounitIso
  signature: : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.symm)
  body: NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

中文:
定义 opCounitIso
  签名: : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (同调复形 Vᵒᵖ c.symm)
  定义体: NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, NatIso, NatIso.ofComponents, isoOfComponents, ofComponents
-/
def opCounitIso : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a category of complexes with objects in `V`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `Vᵒᵖ`. -/
@[simps]
/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm where
  body: opFunctor V c
  inverse := opInverse V c
  unitIso := opUnitIso V c
  counitIso := opCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _

中文:
定义 opEquivalence
  签名: : (同调复形 V c)ᵒᵖ ≌ 同调复形 Vᵒᵖ c.symm where
  定义体: opFunctor V c
  inverse := opInverse V c
  unitIso := opUnitIso V c
  counitIso := opCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _

Depends on / 依赖: opFunctor
-/
def opEquivalence : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm where
  functor := opFunctor V c
  inverse := opInverse V c
  unitIso := opUnitIso V c
  counitIso := opCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [opUnitIso, opCounitIso, NatIso.ofComponents_hom_app, Iso.op_hom, comp_f,
      opFunctor_map_f, Hom.isoOfComponents_hom_f]
    exact Category.comp_id _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opFunctor V c).IsEquivalence
  body: (opEquivalence V c).isEquivalence_functor

中文:
实例 :
  签名: (opFunctor V c).是等价
  定义体: (opEquivalence V c).isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, opEquivalence
-/
instance : (opFunctor V c).IsEquivalence := (opEquivalence V c).isEquivalence_functor
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (opInverse V c).IsEquivalence
  body: (opEquivalence V c).isEquivalence_inverse

中文:
实例 :
  签名: (opInverse V c).是等价
  定义体: (opEquivalence V c).isEquivalence_inverse

Depends on / 依赖: isEquivalence_inverse, opEquivalence
-/
instance : (opInverse V c).IsEquivalence := (opEquivalence V c).isEquivalence_inverse

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
/--
Definition of `unopFunctor` / `unopFunctor` 的定义

English:
definition unopFunctor
  signature: : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm where
  body: (unop X).unop
  map f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j _ => by simp only [unop_d, ← unop_comp, f.unop.comm] }

中文:
定义 unopFunctor
  签名: : (同调复形 Vᵒᵖ c)ᵒᵖ ⥤ 同调复形 V c.symm where
  定义体: (unop X).unop
  map f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j _ => by simp only [unop_d, ← unop_comp, f.unop.comm] }
-/
def unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm where
  obj X := (unop X).unop
  map f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j _ => by simp only [unop_d, ← unop_comp, f.unop.comm] }

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
/--
Definition of `unopInverse` / `unopInverse` 的定义

English:
definition unopInverse
  signature: : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ where
  body: op X.opSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).op
      comm' := fun i j _ => by simp only [opSymm_d, ← op_comp, f.comm] }

中文:
定义 unopInverse
  签名: : 同调复形 V c.symm ⥤ (同调复形 Vᵒᵖ c)ᵒᵖ where
  定义体: op X.opSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).op
      comm' := fun i j _ => by simp only [opSymm_d, ← op_comp, f.comm] }

Depends on / 依赖: X.opSymm, opSymm
-/
def unopInverse : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ where
  obj X := op X.opSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).op
      comm' := fun i j _ => by simp only [opSymm_d, ← op_comp, f.comm] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unopUnitIso` / `unopUnitIso` 的定义

English:
definition unopUnitIso
  signature: : 𝟭 (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInverse V c
  body: NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

中文:
定义 unopUnitIso
  签名: : 𝟭 (同调复形 Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInverse V c
  定义体: NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, Iso.refl_hom, NatIso, NatIso.ofComponents, Opposite, Opposite.unop, Quiver, Quiver.Hom.unop_inj, Quiver.Hom.unop_op, comp_id, id_comp, isoOfComponents, ofComponents, op.unopSymm, op_d
-/
def unopUnitIso : 𝟭 (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInverse V c :=
  NatIso.ofComponents
    (fun X =>
      (HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) fun i j _ => by
            simp only [Iso.refl_hom, Category.id_comp, unopSymm_d, op_d, Quiver.Hom.unop_op,
              Category.comp_id] :
          (Opposite.unop X).op.unopSymm ≅ unop X).op)
    (by
      intro X Y f
      refine Quiver.Hom.unop_inj ?_
      ext x
      simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `unopCounitIso` / `unopCounitIso` 的定义

English:
definition unopCounitIso
  signature: : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex V c.symm)
  body: NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

中文:
定义 unopCounitIso
  签名: : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (同调复形 V c.symm)
  定义体: NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

Depends on / 依赖: HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, Iso.refl, NatIso, NatIso.ofComponents, isoOfComponents, ofComponents
-/
def unopCounitIso : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex V c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `V`. -/
@[simps]
/--
Definition of `unopEquivalence` / `unopEquivalence` 的定义

English:
definition unopEquivalence
  signature: : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≌ HomologicalComplex V c.symm where
  body: unopFunctor V c
  inverse := unopInverse V c
  unitIso := unopUnitIso V c
  counitIso := unopCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [comp_f]
    exact Category.comp_id _

中文:
定义 unopEquivalence
  签名: : (同调复形 Vᵒᵖ c)ᵒᵖ ≌ 同调复形 V c.symm where
  定义体: unopFunctor V c
  inverse := unopInverse V c
  unitIso := unopUnitIso V c
  counitIso := unopCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [comp_f]
    exact Category.comp_id _

Depends on / 依赖: unopFunctor
-/
def unopEquivalence : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≌ HomologicalComplex V c.symm where
  functor := unopFunctor V c
  inverse := unopInverse V c
  unitIso := unopUnitIso V c
  counitIso := unopCounitIso V c
  functor_unitIso_comp X := by
    ext
    simp only [comp_f]
    exact Category.comp_id _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unopFunctor V c).IsEquivalence
  body: (unopEquivalence V c).isEquivalence_functor

中文:
实例 :
  签名: (unopFunctor V c).是等价
  定义体: (unopEquivalence V c).isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, unopEquivalence
-/
instance : (unopFunctor V c).IsEquivalence := (unopEquivalence V c).isEquivalence_functor
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (unopInverse V c).IsEquivalence
  body: (unopEquivalence V c).isEquivalence_inverse

中文:
实例 :
  签名: (unopInverse V c).是等价
  定义体: (unopEquivalence V c).isEquivalence_inverse

Depends on / 依赖: isEquivalence_inverse, unopEquivalence
-/
instance : (unopInverse V c).IsEquivalence := (unopEquivalence V c).isEquivalence_inverse

instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.HasHomology i :=
inferInstanceAs (K.sc i).op.HasHomology

instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.HasHomology i :=
inferInstanceAs (K.sc i).unop.HasHomology

set_option backward.defeqAttrib.useBackward true in
instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    ((opFunctor _ _).obj (op K)).HasHomology i := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    ((unopFunctor _ _).obj (op K)).HasHomology i := by
  dsimp
  infer_instance

variable {V c}

@[simp]
/--
lemma `quasiIsoAt_opFunctor_map_iff` / 引理 `quasiIsoAt_opFunctor_map_iff`

English:
lemma quasiIsoAt_opFunctor_map_iff
  proof: by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_opMap_iff ((shortComplexFunctor V c i).map φ)

@[simp]

中文:
引理 quasiIsoAt_opFunctor_map_iff
  证明: by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_opMap_iff ((shortComplexFunctor V c i).map φ)

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.quasiIso_opMap_iff, quasiIsoAt_iff, quasiIso_opMap_iff, shortComplexFunctor
-/
lemma quasiIsoAt_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((opFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_opMap_iff ((shortComplexFunctor V c i).map φ)

@[simp]
/--
lemma `quasiIsoAt_unopFunctor_map_iff` / 引理 `quasiIsoAt_unopFunctor_map_iff`

English:
lemma quasiIsoAt_unopFunctor_map_iff
  proof: by
  rw [← quasiIsoAt_opFunctor_map_iff]
  rfl

中文:
引理 quasiIsoAt_unopFunctor_map_iff
  证明: by
  rw [← quasiIsoAt_opFunctor_map_iff]
  rfl

Depends on / 依赖: quasiIsoAt_opFunctor_map_iff
-/
lemma quasiIsoAt_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((unopFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  rw [← quasiIsoAt_opFunctor_map_iff]
  rfl

instance {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt φ i] :
    QuasiIsoAt ((opFunctor _ _).map φ.op) i := by
  rw [quasiIsoAt_opFunctor_map_iff]
  infer_instance

instance {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt φ i] :
    QuasiIsoAt ((unopFunctor _ _).map φ.op) i := by
  rw [quasiIsoAt_unopFunctor_map_iff]
  infer_instance

@[simp]
/--
lemma `quasiIso_opFunctor_map_iff` / 引理 `quasiIso_opFunctor_map_iff`

English:
lemma quasiIso_opFunctor_map_iff
  proof: by
  simp only [quasiIso_iff, quasiIsoAt_opFunctor_map_iff]

@[simp]

中文:
引理 quasiIso_opFunctor_map_iff
  证明: by
  simp only [quasiIso_iff, quasiIsoAt_opFunctor_map_iff]

@[simp]

Depends on / 依赖: quasiIsoAt_opFunctor_map_iff, quasiIso_iff
-/
lemma quasiIso_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [forall i, K.HasHomology i] [forall i, L.HasHomology i] :
    QuasiIso ((opFunctor _ _).map φ.op) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_opFunctor_map_iff]

@[simp]
/--
lemma `quasiIso_unopFunctor_map_iff` / 引理 `quasiIso_unopFunctor_map_iff`

English:
lemma quasiIso_unopFunctor_map_iff
  proof: by
  simp only [quasiIso_iff, quasiIsoAt_unopFunctor_map_iff]

中文:
引理 quasiIso_unopFunctor_map_iff
  证明: by
  simp only [quasiIso_iff, quasiIsoAt_unopFunctor_map_iff]

Depends on / 依赖: quasiIsoAt_unopFunctor_map_iff, quasiIso_iff
-/
lemma quasiIso_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [forall i, K.HasHomology i] [forall i, L.HasHomology i] :
    QuasiIso ((unopFunctor _ _).map φ.op) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_unopFunctor_map_iff]

instance {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [forall i, K.HasHomology i] [forall i, L.HasHomology i] [QuasiIso φ] :
    QuasiIso ((opFunctor _ _).map φ.op) := by
  rw [quasiIso_opFunctor_map_iff]
  infer_instance

instance {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [forall i, K.HasHomology i] [forall i, L.HasHomology i] [QuasiIso φ] :
    QuasiIso ((unopFunctor _ _).map φ.op) := by
  rw [quasiIso_unopFunctor_map_iff]
  infer_instance

/--
lemma `ExactAt.op` / 引理 `ExactAt.op`

English:
lemma ExactAt.op
  given: {K : HomologicalComplex V c} {i : ι} (h : K.ExactAt i)
  proof: ShortComplex.Exact.op h

中文:
引理 ExactAt.op
  条件: {K : 同调复形 V c} {i : ι} (h : K.ExactAt i)
  证明: ShortComplex.Exact.op h

Depends on / 依赖: ShortComplex, ShortComplex.Exact.op
-/
lemma ExactAt.op {K : HomologicalComplex V c} {i : ι} (h : K.ExactAt i) :
    K.op.ExactAt i :=
  ShortComplex.Exact.op h

/--
lemma `ExactAt.unop` / 引理 `ExactAt.unop`

English:
lemma ExactAt.unop
  given: {K : HomologicalComplex Vᵒᵖ c} {i : ι} (h : K.ExactAt i)
  proof: ShortComplex.Exact.unop h

@[simp]

中文:
引理 ExactAt.unop
  条件: {K : 同调复形 Vᵒᵖ c} {i : ι} (h : K.ExactAt i)
  证明: ShortComplex.Exact.unop h

@[simp]

Depends on / 依赖: ShortComplex, ShortComplex.Exact.unop
-/
lemma ExactAt.unop {K : HomologicalComplex Vᵒᵖ c} {i : ι} (h : K.ExactAt i) :
    K.unop.ExactAt i :=
  ShortComplex.Exact.unop h

@[simp]
/--
lemma `exactAt_op_iff` / 引理 `exactAt_op_iff`

English:
lemma exactAt_op_iff
  given: (K : HomologicalComplex V c) {i : ι}
  proof: ⟨fun h => h.unop, fun h => h.op⟩

中文:
引理 exactAt_op_iff
  条件: (K : 同调复形 V c) {i : ι}
  证明: ⟨fun h => h.unop, fun h => h.op⟩

Depends on / 依赖: h.op, h.unop
-/
lemma exactAt_op_iff (K : HomologicalComplex V c) {i : ι} :
    K.op.ExactAt i ↔ K.ExactAt i :=
  ⟨fun h => h.unop, fun h => h.op⟩

/--
lemma `Acyclic.op` / 引理 `Acyclic.op`

English:
lemma Acyclic.op
  given: {K : HomologicalComplex V c} (h : K.Acyclic)
  proof: fun i => (h i).op

中文:
引理 非循环.op
  条件: {K : 同调复形 V c} (h : K.非循环)
  证明: fun i => (h i).op
-/
lemma Acyclic.op {K : HomologicalComplex V c} (h : K.Acyclic) :
    K.op.Acyclic :=
  fun i => (h i).op

/--
lemma `Acyclic.unop` / 引理 `Acyclic.unop`

English:
lemma Acyclic.unop
  given: {K : HomologicalComplex Vᵒᵖ c} (h : K.Acyclic)
  proof: fun i => (h i).unop

@[simp]

中文:
引理 非循环.unop
  条件: {K : 同调复形 Vᵒᵖ c} (h : K.非循环)
  证明: fun i => (h i).unop

@[simp]
-/
lemma Acyclic.unop {K : HomologicalComplex Vᵒᵖ c} (h : K.Acyclic) :
    K.unop.Acyclic :=
  fun i => (h i).unop

@[simp]
/--
lemma `acyclic_op_iff` / 引理 `acyclic_op_iff`

English:
lemma acyclic_op_iff
  given: (K : HomologicalComplex V c)
  proof: ⟨fun h => h.unop, fun h => h.op⟩

中文:
引理 acyclic_op_iff
  条件: (K : 同调复形 V c)
  证明: ⟨fun h => h.unop, fun h => h.op⟩

Depends on / 依赖: h.op, h.unop
-/
lemma acyclic_op_iff (K : HomologicalComplex V c) :
    K.op.Acyclic ↔ K.Acyclic :=
  ⟨fun h => h.unop, fun h => h.op⟩

/--
Definition of `homologyOp` / `homologyOp` 的定义

English:
definition homologyOp
  signature: (K : HomologicalComplex V c) (i : ι) [K.HasHomology i]
  body: (K.sc i).homologyOpIso

中文:
定义 homologyOp
  签名: (K : 同调复形 V c) (i : ι) [K.有同调 i]
  定义体: (K.sc i).homologyOpIso

Depends on / 依赖: K.sc, homologyOpIso
-/
def homologyOp (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.homology i ≅ op (K.homology i) :=
  (K.sc i).homologyOpIso

/--
Definition of `homologyUnop` / `homologyUnop` 的定义

English:
definition homologyUnop
  signature: (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i]
  body: (K.unop.homologyOp i).unop

中文:
定义 homologyUnop
  签名: (K : 同调复形 Vᵒᵖ c) (i : ι) [K.有同调 i]
  定义体: (K.unop.homologyOp i).unop

Depends on / 依赖: K.unop.homologyOp, homologyOp
-/
def homologyUnop (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.homology i ≅ unop (K.homology i) :=
  (K.unop.homologyOp i).unop

section

variable (K : HomologicalComplex V c) (i : ι) [K.HasHomology i]

/--
Definition of `cyclesOpIso` / `cyclesOpIso` 的定义

English:
definition cyclesOpIso
  signature: : K.op.cycles i ≅ op (K.opcycles i)
  body: (K.sc i).cyclesOpIso

中文:
定义 cyclesOpIso
  签名: : K.op.cycles i ≅ op (K.opcycles i)
  定义体: (K.sc i).cyclesOpIso

Depends on / 依赖: K.sc, cyclesOpIso
-/
def cyclesOpIso : K.op.cycles i ≅ op (K.opcycles i) :=
  (K.sc i).cyclesOpIso

/--
Definition of `opcyclesOpIso` / `opcyclesOpIso` 的定义

English:
definition opcyclesOpIso
  signature: : K.op.opcycles i ≅ op (K.cycles i)
  body: (K.sc i).opcyclesOpIso

中文:
定义 opcyclesOpIso
  签名: : K.op.opcycles i ≅ op (K.cycles i)
  定义体: (K.sc i).opcyclesOpIso

Depends on / 依赖: K.sc, opcyclesOpIso
-/
def opcyclesOpIso : K.op.opcycles i ≅ op (K.cycles i) :=
  (K.sc i).opcyclesOpIso

variable (j : ι)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opcyclesOpIso_hom_toCycles_op` / 引理 `opcyclesOpIso_hom_toCycles_op`

English:
lemma opcyclesOpIso_hom_toCycles_op
  proof: by
  by_cases hij : c.Rel j i
  · obtain rfl := c.prev_eq' hij
    exact (K.sc i).opcyclesOpIso_hom_toCycles_op
  · rw [K.toCycles_eq_zero hij, K.op.fromOpcycles_eq_zero hij, op_zero, comp_zero]

中文:
引理 opcyclesOpIso_hom_toCycles_op
  证明: by
  by_cases hij : c.Rel j i
  · obtain rfl := c.prev_eq' hij
    exact (K.sc i).opcyclesOpIso_hom_toCycles_op
  · rw [K.toCycles_eq_zero hij, K.op.fromOpcycles_eq_zero hij, op_zero, comp_zero]

Depends on / 依赖: K.op.fromOpcycles_eq_zero, K.sc, K.toCycles_eq_zero, c.Rel, c.prev_eq, comp_zero, fromOpcycles_eq_zero, op_zero, opcyclesOpIso_hom_toCycles_op, prev_eq, rightHomologyMapData, toCycles_eq_zero
-/
lemma opcyclesOpIso_hom_toCycles_op :
    (K.opcyclesOpIso i).hom ≫ (K.toCycles j i).op = K.op.fromOpcycles i j := by
  by_cases hij : c.Rel j i
  · obtain rfl := c.prev_eq' hij
    exact (K.sc i).opcyclesOpIso_hom_toCycles_op
  · rw [K.toCycles_eq_zero hij, K.op.fromOpcycles_eq_zero hij, op_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `fromOpcycles_op_cyclesOpIso_inv` / 引理 `fromOpcycles_op_cyclesOpIso_inv`

English:
lemma fromOpcycles_op_cyclesOpIso_inv
  proof: by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).fromOpcycles_op_cyclesOpIso_inv
  · rw [K.op.toCycles_eq_zero hij, K.fromOpcycles_eq_zero hij, op_zero, zero_comp]

中文:
引理 fromOpcycles_op_cyclesOpIso_inv
  证明: by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).fromOpcycles_op_cyclesOpIso_inv
  · rw [K.op.toCycles_eq_zero hij, K.fromOpcycles_eq_zero hij, op_zero, zero_comp]

Depends on / 依赖: K.fromOpcycles_eq_zero, K.op.toCycles_eq_zero, K.sc, c.Rel, c.next_eq, fromOpcycles_eq_zero, fromOpcycles_op_cyclesOpIso_inv, next_eq, op_zero, rightHomologyMapData, toCycles_eq_zero, zero_comp
-/
lemma fromOpcycles_op_cyclesOpIso_inv :
    (K.fromOpcycles i j).op ≫ (K.cyclesOpIso i).inv = K.op.toCycles j i := by
  by_cases hij : c.Rel i j
  · obtain rfl := c.next_eq' hij
    exact (K.sc i).fromOpcycles_op_cyclesOpIso_inv
  · rw [K.op.toCycles_eq_zero hij, K.fromOpcycles_eq_zero hij, op_zero, zero_comp]

end

section

variable {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
  [K.HasHomology i] [L.HasHomology i]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `homologyOp_hom_naturality` / 引理 `homologyOp_hom_naturality`

English:
lemma homologyOp_hom_naturality
  proof: ShortComplex.homologyOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note

中文:
引理 homologyOp_hom_naturality
  证明: ShortComplex.homologyOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note

Depends on / 依赖: ShortComplex, ShortComplex.homologyOpIso_hom_naturality, homologyOpIso_hom_naturality, shortComplexFunctor
-/
lemma homologyOp_hom_naturality :
    homologyMap ((opFunctor _ _).map φ.op) _ ≫ (K.homologyOp i).hom =
      (L.homologyOp i).hom ≫ (homologyMap φ i).op :=
  ShortComplex.homologyOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `opcyclesOpIso_hom_naturality` / 引理 `opcyclesOpIso_hom_naturality`

English:
lemma opcyclesOpIso_hom_naturality
  proof: ShortComplex.opcyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note

中文:
引理 opcyclesOpIso_hom_naturality
  证明: ShortComplex.opcyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note

Depends on / 依赖: RightHomologyData, RightHomologyData.p_g, ShortComplex, ShortComplex.opcyclesOpIso_hom_naturality, _assoc, cancel_epi, opcyclesOpIso_hom_naturality, p_opcyclesMap, shortComplexFunctor
-/
lemma opcyclesOpIso_hom_naturality :
    opcyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.opcyclesOpIso i).hom =
      (L.opcyclesOpIso i).hom ≫ (cyclesMap φ i).op :=
  ShortComplex.opcyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `opcyclesOpIso_inv_naturality` / 引理 `opcyclesOpIso_inv_naturality`

English:
lemma opcyclesOpIso_inv_naturality
  proof: ShortComplex.opcyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note

中文:
引理 opcyclesOpIso_inv_naturality
  证明: ShortComplex.opcyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note

Depends on / 依赖: ShortComplex, ShortComplex.opcyclesOpIso_inv_naturality, opcyclesOpIso_inv_naturality, shortComplexFunctor
-/
lemma opcyclesOpIso_inv_naturality :
    (cyclesMap φ i).op ≫ (K.opcyclesOpIso i).inv =
      (L.opcyclesOpIso i).inv ≫ opcyclesMap ((opFunctor _ _).map φ.op) _ :=
  ShortComplex.opcyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `cyclesOpIso_hom_naturality` / 引理 `cyclesOpIso_hom_naturality`

English:
lemma cyclesOpIso_hom_naturality
  proof: ShortComplex.cyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

@[reassoc]

中文:
引理 cyclesOpIso_hom_naturality
  证明: ShortComplex.cyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

@[reassoc]

Depends on / 依赖: ShortComplex, ShortComplex.cyclesOpIso_hom_naturality, cyclesOpIso_hom_naturality, shortComplexFunctor
-/
lemma cyclesOpIso_hom_naturality :
    cyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.cyclesOpIso i).hom =
      (L.cyclesOpIso i).hom ≫ (opcyclesMap φ i).op :=
  ShortComplex.cyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

@[reassoc]
/--
lemma `cyclesOpIso_inv_naturality` / 引理 `cyclesOpIso_inv_naturality`

English:
lemma cyclesOpIso_inv_naturality
  proof: ShortComplex.cyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

中文:
引理 cyclesOpIso_inv_naturality
  证明: ShortComplex.cyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

Depends on / 依赖: ShortComplex, ShortComplex.cyclesOpIso_inv_naturality, cyclesOpIso_inv_naturality, shortComplexFunctor
-/
lemma cyclesOpIso_inv_naturality :
    (opcyclesMap φ i).op ≫ (K.cyclesOpIso i).inv =
      (L.cyclesOpIso i).inv ≫ cyclesMap ((opFunctor _ _).map φ.op) _ :=
  ShortComplex.cyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

end

section

variable (V c) [CategoryWithHomology V] (i : ι)

/-- The natural isomorphism `K.op.cycles i ≅ op (K.opcycles i)`. -/
@[simps!]
/--
Definition of `cyclesOpNatIso` / `cyclesOpNatIso` 的定义

English:
definition cyclesOpNatIso
  signature: :
  body: NatIso.ofComponents (fun K => (unop K).cyclesOpIso i)
    (fun _ => cyclesOpIso_hom_naturality _ _)

中文:
定义 cyclesOp自然数Iso
  签名: :
  定义体: NatIso.ofComponents (fun K => (unop K).cyclesOpIso i)
    (fun _ => cyclesOpIso_hom_naturality _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, cyclesOpIso, cyclesOpIso_hom_naturality, ofComponents
-/
def cyclesOpNatIso :
    opFunctor V c ⋙ cyclesFunctor Vᵒᵖ c.symm i ≅ (opcyclesFunctor V c i).op :=
  NatIso.ofComponents (fun K => (unop K).cyclesOpIso i)
    (fun _ => cyclesOpIso_hom_naturality _ _)

/--
Definition of `opcyclesOpNatIso` / `opcyclesOpNatIso` 的定义

English:
definition opcyclesOpNatIso
  signature: :
  body: NatIso.ofComponents (fun K => (unop K).opcyclesOpIso i)
    (fun _ => opcyclesOpIso_hom_naturality _ _)

中文:
定义 opcyclesOp自然数Iso
  签名: :
  定义体: NatIso.ofComponents (fun K => (unop K).opcyclesOpIso i)
    (fun _ => opcyclesOpIso_hom_naturality _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, ofComponents, opcyclesOpIso, opcyclesOpIso_hom_naturality
-/
def opcyclesOpNatIso :
    opFunctor V c ⋙ opcyclesFunctor Vᵒᵖ c.symm i ≅ (cyclesFunctor V c i).op :=
  NatIso.ofComponents (fun K => (unop K).opcyclesOpIso i)
    (fun _ => opcyclesOpIso_hom_naturality _ _)

/--
Definition of `homologyOpNatIso` / `homologyOpNatIso` 的定义

English:
definition homologyOpNatIso
  signature: :
  body: NatIso.ofComponents (fun K => (unop K).homologyOp i)
    (fun _ => homologyOp_hom_naturality _ _)

中文:
定义 homologyOp自然数Iso
  签名: :
  定义体: NatIso.ofComponents (fun K => (unop K).homologyOp i)
    (fun _ => homologyOp_hom_naturality _ _)

Depends on / 依赖: NatIso, NatIso.ofComponents, homologyOp, homologyOp_hom_naturality, ofComponents
-/
def homologyOpNatIso :
    opFunctor V c ⋙ homologyFunctor Vᵒᵖ c.symm i ≅ (homologyFunctor V c i).op :=
  NatIso.ofComponents (fun K => (unop K).homologyOp i)
    (fun _ => homologyOp_hom_naturality _ _)

end

end

section

variable [Preadditive V]

example : Preadditive (HomologicalComplex Vᵒᵖ c) := inferInstance

/--
Instance `opFunctor_additive` / 实例 `opFunctor_additive`

English:
instance opFunctor_additive
  signature: : (@opFunctor ι V _ c _).Additive where

中文:
实例 opFunctor_additive
  签名: : (@opFunctor ι V _ c _).加性 where
-/
instance opFunctor_additive : (@opFunctor ι V _ c _).Additive where

/--
Instance `unopFunctor_additive` / 实例 `unopFunctor_additive`

English:
instance unopFunctor_additive
  signature: : (@unopFunctor ι V _ c _).Additive where

中文:
实例 unopFunctor_additive
  签名: : (@unopFunctor ι V _ c _).加性 where
-/
instance unopFunctor_additive : (@unopFunctor ι V _ c _).Additive where

end

end HomologicalComplex

namespace Homotopy

open HomologicalComplex

variable {V : Type*} [Category* V] {ι : Type*} {c : ComplexShape ι} [Preadditive V]

set_option backward.defeqAttrib.useBackward true in
/-- The opposite of a homotopy between morphisms of homological complexes. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {F G : HomologicalComplex V c} {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂)
  body: (h.hom j i).op
  zero i j hij := Quiver.Hom.unop_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.unop_inj (by
    dsimp
    rw [h.comm n]
    nth_rw 2 [add_comm]
    rfl)

中文:
定义 op
  签名: {F G : 同调复形 V c} {φ₁ φ₂ : F ⟶ G} (h : 同伦 φ₁ φ₂)
  定义体: (h.hom j i).op
  zero i j hij := Quiver.Hom.unop_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.unop_inj (by
    dsimp
    rw [h.comm n]
    nth_rw 2 [add_comm]
    rfl)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.id, h.hom, rightHomologyMap
-/
def op {F G : HomologicalComplex V c} {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    Homotopy ((opFunctor V c).map φ₁.op) ((opFunctor V c).map φ₂.op) where
  hom i j := (h.hom j i).op
  zero i j hij := Quiver.Hom.unop_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.unop_inj (by
    dsimp
    rw [h.comm n]
    nth_rw 2 [add_comm]
    rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The homotopy between morphisms of homological complexes that is deduced
from a homotopy in the opposite category. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {F G : HomologicalComplex Vᵒᵖ c} {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂)
  body: (h.hom j i).unop
  zero i j hij := Quiver.Hom.op_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.op_inj (by
    dsimp
    rw [h.comm n]
    nth_rw 2 [add_comm]
    rfl)

中文:
定义 unop
  签名: {F G : 同调复形 Vᵒᵖ c} {φ₁ φ₂ : F ⟶ G} (h : 同伦 φ₁ φ₂)
  定义体: (h.hom j i).unop
  zero i j hij := Quiver.Hom.op_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.op_inj (by
    dsimp
    rw [h.comm n]
    nth_rw 2 [add_comm]
    rfl)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.id, h.hom, opcyclesMap
-/
def unop {F G : HomologicalComplex Vᵒᵖ c} {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) :
    Homotopy ((unopFunctor V c).map φ₁.op) ((unopFunctor V c).map φ₂.op) where
  hom i j := (h.hom j i).unop
  zero i j hij := Quiver.Hom.op_inj (h.zero _ _ hij)
  comm n := Quiver.Hom.op_inj (by
    dsimp
    rw [h.comm n]
    nth_rw 2 [add_comm]
    rfl)

end Homotopy
