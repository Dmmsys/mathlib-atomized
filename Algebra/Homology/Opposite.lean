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

/-
**imageToKernel_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_op {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) : ima
geToKernel g.op f.op (by rw [← op_comp, w, op_zero]) = (imageSubobjectIso _ ≪≫ (
imageOpOp _).symm).hom ≫ (cokernel.desc f (factorThruImage g) (by rw [← cancel_m
ono (image.ι g), Category.assoc, image.fac, w, zero_comp])).op ≫ (kernelSubobjec
tIso _ ≪≫ kernelOpOp _).inv
参数：f : X ⟶ Y；g : Y ⟶ Z；w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.imageUnopOp_inv_comp_op_factorThruImage`：imageUnopOp_inv_
comp_op_factorThruImage : (imageUnopOp g).inv ≫ (factorThruImage g.unop).op = im
age.ι g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.kernelOpOp_inv`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C] {X Y : C}   (f : X ⟶ Y
),   (CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
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
/-
**imageToKernel_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_unop {X Y Z : Vᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
 imageToKernel g.unop f.unop (by rw [← unop_comp, w, unop_zero]) = (imageSubobje
ctIso _ ≪≫ (imageUnopUnop _).symm).hom ≫ (cokernel.desc f (factorThruImage g) (b
y rw [← cancel_mono (image.ι g), Category.assoc, image.fac, w, zero_comp])).unop
 ≫ (kernelSubobjectIso _ ≪≫ kernelUnopUnop _).inv
参数：f : X ⟶ Y；g : Y ⟶ Z；w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasSt
rongEpiMonoFactorisations C],   CategoryTheory.Limits.H…
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.unop_inv`：∀ {C : Type u₁} [inst : CategoryTheory.Cate
gory.{v₁, u₁} C] {X Y : Cᵒᵖ} (f : X ≅ Y), f.unop.inv = f.inv.unop
· 使用定理 `CategoryTheory.kernelUnopUnop_inv`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C] {A B : Cᵒᵖ}   (g :
 A ⟶ B),   (CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.factorThruImage_comp_imageUnopOp_inv`：factorThruImage_com
p_imageUnopOp_inv : factorThruImage g ≫ (imageUnopOp g).inv = (image.ι g.unop).o
p
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow`：imageSubobject_arrow : (imag
eSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**HomologicalComplex.op** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   {V : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_2} V] →       {c : ComplexShape ι} →         [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms V] → HomologicalComplex V c → HomologicalComplex Vᵒᵖ c.symm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a complex `X` with objects in `V` to the corresponding complex with object
s in `Vᵒᵖ`.
-/
protected def op (X : HomologicalComplex V c) : HomologicalComplex Vᵒᵖ c.symm where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

/-- Sends a complex `X` with objects in `V` to the corresponding complex with objects in `Vᵒᵖ`. -/
@[simps]
/-
**HomologicalComplex.opSymm** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   {V : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_2} V] →       {c : ComplexShape ι} →         [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms V] → HomologicalComplex V c.symm → HomologicalComplex Vᵒᵖ c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a complex `X` with objects in `V` to the corresponding complex with object
s in `Vᵒᵖ`.
-/
protected def opSymm (X : HomologicalComplex V c.symm) : HomologicalComplex Vᵒᵖ c where
  X i := op (X.X i)
  d i j := (X.d j i).op
  shape i j hij := by rw [X.shape j i hij, op_zero]
  d_comp_d' _ _ _ _ _ := by rw [← op_comp, X.d_comp_d, op_zero]

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
/-
**HomologicalComplex.unop** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   {V : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_2} V] →       {c : ComplexShape ι} →         [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms V] → HomologicalComplex Vᵒᵖ c → HomologicalComplex V c.symm
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with obje
cts in `V`.
-/
protected def unop (X : HomologicalComplex Vᵒᵖ c) : HomologicalComplex V c.symm where
  X i := unop (X.X i)
  d i j := (X.d j i).unop
  shape i j hij := by rw [X.shape j i hij, unop_zero]
  d_comp_d' _ _ _ _ _ := by rw [← unop_comp, X.d_comp_d, unop_zero]

/-- Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with objects in `V`. -/
@[simps]
/-
**HomologicalComplex.unopSymm** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：{ι : Type u_1} →   {V : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_2} V] →       {c : ComplexShape ι} →         [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms V] → HomologicalComplex Vᵒᵖ c.symm → HomologicalComplex V c
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a complex `X` with objects in `Vᵒᵖ` to the corresponding complex with obje
cts in `V`.
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
/-
**HomologicalComplex.opFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：opFunctor : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm whe
re obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `opEquivalence`.
-/
def opFunctor : (HomologicalComplex V c)ᵒᵖ ⥤ HomologicalComplex Vᵒᵖ c.symm where
  obj X := (unop X).op
  map f :=
    { f := fun i => (f.unop.f i).op
      comm' := fun i j _ => by simp only [op_d, ← op_comp, f.unop.comm] }

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `opEquivalence`. -/
@[simps]
/-
**HomologicalComplex.opInverse** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：opInverse : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ whe
re obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `opEquivalence`.
-/
def opInverse : HomologicalComplex Vᵒᵖ c.symm ⥤ (HomologicalComplex V c)ᵒᵖ where
  obj X := op X.unopSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).unop
      comm' := fun i j _ => by simp only [unopSymm_d, ← unop_comp, f.comm] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `opEquivalence`. -/
/-
**HomologicalComplex.opUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：opUnitIso : 𝟭 (HomologicalComplex V c)ᵒᵖ ≅ opFunctor V c ⋙ opInverse V c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `opEquivalence`.
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
/-- Auxiliary definition for `opEquivalence`. -/
/-
**HomologicalComplex.opCounitIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：opCounitIso : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.
symm)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `opEquivalence`.
-/
def opCounitIso : opInverse V c ⋙ opFunctor V c ≅ 𝟭 (HomologicalComplex Vᵒᵖ c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a category of complexes with objects in `V`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `Vᵒᵖ`. -/
@[simps]
/-
**HomologicalComplex.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：opEquivalence : (HomologicalComplex V c)ᵒᵖ ≌ HomologicalComplex Vᵒᵖ c.symm
 where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a category of complexes with objects in `V`, there is a natural equivalenc
e between its
opposite category and a category of complexes with objects in `Vᵒᵖ`.
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
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (opFunctor V c).IsEquivalence := (opEquivalence V c).isEquivalence_functor
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (opInverse V c).IsEquivalence := (opEquivalence V c).isEquivalence_inverse

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
/-
**HomologicalComplex.unopFunctor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm w
here obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `unopEquivalence`.
-/
def unopFunctor : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ⥤ HomologicalComplex V c.symm where
  obj X := (unop X).unop
  map f :=
    { f := fun i => (f.unop.f i).unop
      comm' := fun i j _ => by simp only [unop_d, ← unop_comp, f.unop.comm] }

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unopEquivalence`. -/
@[simps]
/-
**HomologicalComplex.unopInverse** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：unopInverse : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ w
here obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `unopEquivalence`.
-/
def unopInverse : HomologicalComplex V c.symm ⥤ (HomologicalComplex Vᵒᵖ c)ᵒᵖ where
  obj X := op X.opSymm
  map f := Quiver.Hom.op
    { f := fun i => (f.f i).op
      comm' := fun i j _ => by simp only [opSymm_d, ← op_comp, f.comm] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `unopEquivalence`. -/
/-
**HomologicalComplex.unopUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：unopUnitIso : 𝟭 (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≅ unopFunctor V c ⋙ unopInver
se V c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `unopEquivalence`.
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
/-- Auxiliary definition for `unopEquivalence`. -/
/-
**HomologicalComplex.unopCounitIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：unopCounitIso : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex 
V c.symm)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `unopEquivalence`.
-/
def unopCounitIso : unopInverse V c ⋙ unopFunctor V c ≅ 𝟭 (HomologicalComplex V c.symm) :=
  NatIso.ofComponents
    fun X => HomologicalComplex.Hom.isoOfComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivalence between its
opposite category and a category of complexes with objects in `V`. -/
@[simps]
/-
**HomologicalComplex.unopEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：unopEquivalence : (HomologicalComplex Vᵒᵖ c)ᵒᵖ ≌ HomologicalComplex V c.sy
mm where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a category of complexes with objects in `Vᵒᵖ`, there is a natural equivale
nce between its
opposite category and a category of complexes with objects in `V`.
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
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (unopFunctor V c).IsEquivalence := (unopEquivalence V c).isEquivalence_functor
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (unopInverse V c).IsEquivalence := (unopEquivalence V c).isEquivalence_inverse
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.HasHomology i :=
  inferInstanceAs <| (K.sc i).op.HasHomology
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.HasHomology i :=
  inferInstanceAs <| (K.sc i).unop.HasHomology

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    ((opFunctor _ _).obj (op K)).HasHomology i := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    ((unopFunctor _ _).obj (op K)).HasHomology i := by
  dsimp
  infer_instance

variable {V c}

@[simp]
/-
**HomologicalComplex.quasiIsoAt_opFunctor_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：quasiIsoAt_opFunctor_map_iff {K L : HomologicalComplex V c} (φ : K ⟶ L) (i
 : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt ((opFunctor _ _).map φ.op
) i ↔ QuasiIsoAt φ i
参数：φ : K ⟶ L；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.quasiIso_opMap_iff`：quasiIso_opMap_iff (φ : 
S₁ ⟶ S₂) : QuasiIso (opMap φ) ↔ QuasiIso φ
-/
lemma quasiIsoAt_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((opFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  simp only [quasiIsoAt_iff]
  exact ShortComplex.quasiIso_opMap_iff ((shortComplexFunctor V c i).map φ)

@[simp]
/-
**HomologicalComplex.quasiIsoAt_unopFunctor_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `H
omologicalComplex`。
形式化陈述：quasiIsoAt_unopFunctor_map_iff {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L
) (i : ι) [K.HasHomology i] [L.HasHomology i] : QuasiIsoAt ((unopFunctor _ _).ma
p φ.op) i ↔ QuasiIsoAt φ i
参数：φ : K ⟶ L；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjOppositeSymmUnopFunctorOp`：∀ {ι : T
ype u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Compl
exShape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.quasiIsoAt_opFunctor_map_iff`：quasiIsoAt_opFunctor_ma
p_iff {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι) [K.HasHomology i] [L.Ha
sHomology i] : QuasiIsoAt ((opFunctor…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIsoAt_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    QuasiIsoAt ((unopFunctor _ _).map φ.op) i ↔ QuasiIsoAt φ i := by
  rw [← quasiIsoAt_opFunctor_map_iff]
  rfl
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : HomologicalComplex V c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt φ i] :
    QuasiIsoAt ((opFunctor _ _).map φ.op) i := by
  rw [quasiIsoAt_opFunctor_map_iff]
  infer_instance
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt φ i] :
    QuasiIsoAt ((unopFunctor _ _).map φ.op) i := by
  rw [quasiIsoAt_unopFunctor_map_iff]
  infer_instance

@[simp]
/-
**HomologicalComplex.quasiIso_opFunctor_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：quasiIso_opFunctor_map_iff {K L : HomologicalComplex V c} (φ : K ⟶ L) [for
all i, K.HasHomology i] [forall i, L.HasHomology i] : QuasiIso ((opFunctor _ _).
map φ.op) ↔ QuasiIso φ
参数：φ : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasHomologyOppositeObjSymmOpFunctorOp`：∀ {ι : Typ
e u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Complex
Shape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quasiIso_opFunctor_map_iff
    {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso ((opFunctor _ _).map φ.op) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_opFunctor_map_iff]

@[simp]
/-
**HomologicalComplex.quasiIso_unopFunctor_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：quasiIso_unopFunctor_map_iff {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L) 
[forall i, K.HasHomology i] [forall i, L.HasHomology i] : QuasiIso ((unopFunctor
 _ _).map φ.op) ↔ QuasiIso φ
参数：φ : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasHomologyObjOppositeSymmUnopFunctorOp`：∀ {ι : T
ype u_1} (V : Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : Compl
exShape ι)   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma quasiIso_unopFunctor_map_iff
    {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] :
    QuasiIso ((unopFunctor _ _).map φ.op) ↔ QuasiIso φ := by
  simp only [quasiIso_iff, quasiIsoAt_unopFunctor_map_iff]
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : HomologicalComplex V c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] [QuasiIso φ] :
    QuasiIso ((opFunctor _ _).map φ.op) := by
  rw [quasiIso_opFunctor_map_iff]
  infer_instance
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : HomologicalComplex Vᵒᵖ c} (φ : K ⟶ L)
    [∀ i, K.HasHomology i] [∀ i, L.HasHomology i] [QuasiIso φ] :
    QuasiIso ((unopFunctor _ _).map φ.op) := by
  rw [quasiIso_unopFunctor_map_iff]
  infer_instance
/-
**HomologicalComplex.ExactAt.op** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.Ex
actAt`。
形式化陈述：∀ {ι : Type u_1} {V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {
K : HomologicalComplex V c} {i : ι}, K.ExactAt i → K.op.ExactAt i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.op`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {S : CategoryTheory.Sho…
-/
lemma ExactAt.op {K : HomologicalComplex V c} {i : ι} (h : K.ExactAt i) :
    K.op.ExactAt i :=
  ShortComplex.Exact.op h
/-
**HomologicalComplex.ExactAt.unop** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.
ExactAt`。
形式化陈述：∀ {ι : Type u_1} {V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {
K : HomologicalComplex Vᵒᵖ c} {i : ι},   K.ExactAt i → K.unop.ExactAt i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.unop`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms 
C]   {S : CategoryTheory.Sho…
-/
lemma ExactAt.unop {K : HomologicalComplex Vᵒᵖ c} {i : ι} (h : K.ExactAt i) :
    K.unop.ExactAt i :=
  ShortComplex.Exact.unop h

@[simp]
/-
**HomologicalComplex.exactAt_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：exactAt_op_iff (K : HomologicalComplex V c) {i : ι} : K.op.ExactAt i ↔ K.E
xactAt i
参数：K : HomologicalComplex V c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ExactAt.unop`：∀ {ι : Type u_1} {V : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : Category
Theory.Limits.HasZero…
· 使用定理 `HomologicalComplex.ExactAt.op`：∀ {ι : Type u_1} {V : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTh
eory.Limits.HasZero…
-/
lemma exactAt_op_iff (K : HomologicalComplex V c) {i : ι} :
    K.op.ExactAt i ↔ K.ExactAt i :=
  ⟨fun h ↦ h.unop, fun h ↦ h.op⟩
/-
**HomologicalComplex.Acyclic.op** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.Ac
yclic`。
形式化陈述：∀ {ι : Type u_1} {V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {
K : HomologicalComplex V c}, K.Acyclic → K.op.Acyclic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ExactAt.op`：∀ {ι : Type u_1} {V : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTh
eory.Limits.HasZero…
-/
lemma Acyclic.op {K : HomologicalComplex V c} (h : K.Acyclic) :
    K.op.Acyclic :=
  fun i ↦ (h i).op
/-
**HomologicalComplex.Acyclic.unop** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComplex.
Acyclic`。
形式化陈述：∀ {ι : Type u_1} {V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {
K : HomologicalComplex Vᵒᵖ c}, K.Acyclic → K.unop.Acyclic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.ExactAt.unop`：∀ {ι : Type u_1} {V : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : Category
Theory.Limits.HasZero…
-/
lemma Acyclic.unop {K : HomologicalComplex Vᵒᵖ c} (h : K.Acyclic) :
    K.unop.Acyclic :=
  fun i ↦ (h i).unop

@[simp]
/-
**HomologicalComplex.acyclic_op_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComple
x`。
形式化陈述：acyclic_op_iff (K : HomologicalComplex V c) : K.op.Acyclic ↔ K.Acyclic
参数：K : HomologicalComplex V c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.Acyclic.unop`：∀ {ι : Type u_1} {V : Type u_2} [inst :
 CategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : Category
Theory.Limits.HasZero…
· 使用定理 `HomologicalComplex.Acyclic.op`：∀ {ι : Type u_1} {V : Type u_2} [inst : C
ategoryTheory.Category.{v_1, u_2} V] {c : ComplexShape ι}   [inst_1 : CategoryTh
eory.Limits.HasZero…
-/
lemma acyclic_op_iff (K : HomologicalComplex V c) :
    K.op.Acyclic ↔ K.Acyclic :=
  ⟨fun h ↦ h.unop, fun h ↦ h.op⟩

/-- If `K` is a homological complex, then the homology of `K.op` identifies to
the opposite of the homology of `K`. -/
/-
**HomologicalComplex.homologyOp** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homologyOp (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] : K.op.h
omology i ≅ op (K.homology i)
参数：K : HomologicalComplex V c；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K` is a homological complex, then the homology of `K.op` identifies to
the opposite of the homology of `K`.
-/
def homologyOp (K : HomologicalComplex V c) (i : ι) [K.HasHomology i] :
    K.op.homology i ≅ op (K.homology i) :=
  (K.sc i).homologyOpIso

/-- If `K` is a homological complex in the opposite category,
then the homology of `K.unop` identifies to the opposite of the homology of `K`. -/
/-
**HomologicalComplex.homologyUnop** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：homologyUnop (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] : K.
unop.homology i ≅ unop (K.homology i)
参数：K : HomologicalComplex Vᵒᵖ c；i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyUnopOfOpposite`：∀ {ι : Type u_1} (V : 
Type u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [
inst_1 : CategoryTheory.Limits.HasZero…

--- 原说明 ---
If `K` is a homological complex in the opposite category,
then the homology of `K.unop` identifies to the opposite of the homology of `K`.
-/
def homologyUnop (K : HomologicalComplex Vᵒᵖ c) (i : ι) [K.HasHomology i] :
    K.unop.homology i ≅ unop (K.homology i) :=
  (K.unop.homologyOp i).unop

section

variable (K : HomologicalComplex V c) (i : ι) [K.HasHomology i]

/-- The canonical isomorphism `K.op.cycles i ≅ op (K.opcycles i)`. -/
/-
**HomologicalComplex.cyclesOpIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：cyclesOpIso : K.op.cycles i ≅ op (K.opcycles i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.op.cycles i ≅ op (K.opcycles i)`.
-/
def cyclesOpIso : K.op.cycles i ≅ op (K.opcycles i) :=
  (K.sc i).cyclesOpIso

/-- The canonical isomorphism `K.op.opcycles i ≅ op (K.cycles i)`. -/
/-
**HomologicalComplex.opcyclesOpIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：opcyclesOpIso : K.op.opcycles i ≅ op (K.cycles i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `K.op.opcycles i ≅ op (K.cycles i)`.
-/
def opcyclesOpIso : K.op.opcycles i ≅ op (K.cycles i) :=
  (K.sc i).opcyclesOpIso

variable (j : ι)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.opcyclesOpIso_hom_toCycles_op** 是 Mathlib 中的一个引理，位于命名空间 `Ho
mologicalComplex`。
形式化陈述：opcyclesOpIso_hom_toCycles_op : (K.opcyclesOpIso i).hom ≫ (K.toCycles j i)
.op = K.op.fromOpcycles i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用引理 `CategoryTheory.ShortComplex.opcyclesOpIso_hom_toCycles_op`：opcyclesOpIso
_hom_toCycles_op [S.HasLeftHomology] : S.opcyclesOpIso.hom ≫ S.toCycles.op = S.o
p.fromOpcycles
· 使用定理 `ComplexShape.prev_eq'`：∀ {ι : Type u_1} (c : ComplexShape ι) {i j : ι}, 
c.Rel j i → c.prev i = j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.toCycles_eq_zero`：toCycles_eq_zero [K.HasHomology j] 
(hij : ¬ c.Rel i j) : K.toCycles i j = 0
· 使用引理 `HomologicalComplex.fromOpcycles_eq_zero`：fromOpcycles_eq_zero (hij : ¬ c
.Rel i j) : K.fromOpcycles i j = 0
· 使用定理 `CategoryTheory.Limits.op_zero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (X Y : C),  
 Quiver.Hom.op 0 = …
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma opcyclesOpIso_hom_toCycles_op :
    (K.opcyclesOpIso i).hom ≫ (K.toCycles j i).op = K.op.fromOpcycles i j := by
  by_cases hij : c.Rel j i
  · obtain rfl := c.prev_eq' hij
    exact (K.sc i).opcyclesOpIso_hom_toCycles_op
  · rw [K.toCycles_eq_zero hij, K.op.fromOpcycles_eq_zero hij, op_zero, comp_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.fromOpcycles_op_cyclesOpIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `
HomologicalComplex`。
形式化陈述：fromOpcycles_op_cyclesOpIso_inv : (K.fromOpcycles i j).op ≫ (K.cyclesOpIso
 i).inv = K.op.toCycles j i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyOppositeOp`：∀ {ι : Type u_1} (V : Type
 u_2) [inst : CategoryTheory.Category.{v_1, u_2} V] (c : ComplexShape ι)   [inst
_1 : CategoryTheory.Limits.HasZero…
· 使用引理 `CategoryTheory.ShortComplex.fromOpcycles_op_cyclesOpIso_inv`：fromOpcycle
s_op_cyclesOpIso_inv [S.HasRightHomology] : S.fromOpcycles.op ≫ S.cyclesOpIso.in
v = S.op.toCycles
· 使用定理 `ComplexShape.next_eq'`：next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Re
l i j) : c.next i = j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `HomologicalComplex.toCycles_eq_zero`：toCycles_eq_zero [K.HasHomology j] 
(hij : ¬ c.Rel i j) : K.toCycles i j = 0
· 使用引理 `HomologicalComplex.fromOpcycles_eq_zero`：fromOpcycles_eq_zero (hij : ¬ c
.Rel i j) : K.fromOpcycles i j = 0
· 使用定理 `CategoryTheory.Limits.op_zero`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] (X Y : C),  
 Quiver.Hom.op 0 = …
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
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
/-
**HomologicalComplex.homologyOp_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：homologyOp_hom_naturality : homologyMap ((opFunctor _ _).map φ.op) _ ≫ (K.
homologyOp i).hom = (L.homologyOp i).hom ≫ (homologyMap φ i).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.homologyOpIso_hom_naturality`：homologyOpIso_
hom_naturality [S₁.HasHomology] [S₂.HasHomology] : homologyMap (opMap φ) ≫ (S₁.h
omologyOpIso).hom = S₂.homologyOpIso.hom ≫ (ho…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma homologyOp_hom_naturality :
    homologyMap ((opFunctor _ _).map φ.op) _ ≫ (K.homologyOp i).hom =
      (L.homologyOp i).hom ≫ (homologyMap φ i).op :=
  ShortComplex.homologyOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**HomologicalComplex.opcyclesOpIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：opcyclesOpIso_hom_naturality : opcyclesMap ((opFunctor _ _).map φ.op) _ ≫ 
(K.opcyclesOpIso i).hom = (L.opcyclesOpIso i).hom ≫ (cyclesMap φ i).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.opcyclesOpIso_hom_naturality`：opcyclesOpIso_
hom_naturality (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] : opcycle
sMap (opMap φ) ≫ (S₁.opcyclesOpIso).hom = S₂.o…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opcyclesOpIso_hom_naturality :
    opcyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.opcyclesOpIso i).hom =
      (L.opcyclesOpIso i).hom ≫ (cyclesMap φ i).op :=
  ShortComplex.opcyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.opcyclesOpIso_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：opcyclesOpIso_inv_naturality : (cyclesMap φ i).op ≫ (K.opcyclesOpIso i).in
v = (L.opcyclesOpIso i).inv ≫ opcyclesMap ((opFunctor _ _).map φ.op) _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.opcyclesOpIso_inv_naturality`：opcyclesOpIso_
inv_naturality (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] : (cycles
Map φ).op ≫ (S₁.opcyclesOpIso).inv = S₂.opcycl…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma opcyclesOpIso_inv_naturality :
    (cyclesMap φ i).op ≫ (K.opcyclesOpIso i).inv =
      (L.opcyclesOpIso i).inv ≫ opcyclesMap ((opFunctor _ _).map φ.op) _ :=
  ShortComplex.opcyclesOpIso_inv_naturality ((shortComplexFunctor V c i).map φ)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**HomologicalComplex.cyclesOpIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：cyclesOpIso_hom_naturality : cyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.c
yclesOpIso i).hom = (L.cyclesOpIso i).hom ≫ (opcyclesMap φ i).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cyclesOpIso_hom_naturality`：cyclesOpIso_hom_
naturality (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] : cyclesMap
 (opMap φ) ≫ (S₁.cyclesOpIso).hom = S₂.cycle…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma cyclesOpIso_hom_naturality :
    cyclesMap ((opFunctor _ _).map φ.op) _ ≫ (K.cyclesOpIso i).hom =
      (L.cyclesOpIso i).hom ≫ (opcyclesMap φ i).op :=
  ShortComplex.cyclesOpIso_hom_naturality ((shortComplexFunctor V c i).map φ)

@[reassoc]
/-
**HomologicalComplex.cyclesOpIso_inv_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：cyclesOpIso_inv_naturality : (opcyclesMap φ i).op ≫ (K.cyclesOpIso i).inv 
= (L.cyclesOpIso i).inv ≫ cyclesMap ((opFunctor _ _).map φ.op) _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.cyclesOpIso_inv_naturality`：cyclesOpIso_inv_
naturality (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] : (opcycles
Map φ).op ≫ (S₁.cyclesOpIso).inv = S₂.cycles…
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
/-
**HomologicalComplex.cyclesOpNatIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComple
x`。
形式化陈述：cyclesOpNatIso : opFunctor V c ⋙ cyclesFunctor Vᵒᵖ c.symm i ≅ (opcyclesFun
ctor V c i).op
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instCategoryWithHomologyOpposite`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   [CategoryTheory.CategoryWithH…

--- 原说明 ---
The natural isomorphism `K.op.cycles i ≅ op (K.opcycles i)`.
-/
def cyclesOpNatIso :
    opFunctor V c ⋙ cyclesFunctor Vᵒᵖ c.symm i ≅ (opcyclesFunctor V c i).op :=
  NatIso.ofComponents (fun K ↦ (unop K).cyclesOpIso i)
    (fun _ ↦ cyclesOpIso_hom_naturality _ _)

/-- The natural isomorphism `K.op.opcycles i ≅ op (K.cycles i)`. -/
/-
**HomologicalComplex.opcyclesOpNatIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：opcyclesOpNatIso : opFunctor V c ⋙ opcyclesFunctor Vᵒᵖ c.symm i ≅ (cyclesF
unctor V c i).op
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instCategoryWithHomologyOpposite`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   [CategoryTheory.CategoryWithH…

--- 原说明 ---
The natural isomorphism `K.op.opcycles i ≅ op (K.cycles i)`.
-/
def opcyclesOpNatIso :
    opFunctor V c ⋙ opcyclesFunctor Vᵒᵖ c.symm i ≅ (cyclesFunctor V c i).op :=
  NatIso.ofComponents (fun K ↦ (unop K).opcyclesOpIso i)
    (fun _ ↦ opcyclesOpIso_hom_naturality _ _)

/-- The natural isomorphism `K.op.homology i ≅ op (K.homology i)`. -/
/-
**HomologicalComplex.homologyOpNatIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComp
lex`。
形式化陈述：homologyOpNatIso : opFunctor V c ⋙ homologyFunctor Vᵒᵖ c.symm i ≅ (homolog
yFunctor V c i).op
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.instCategoryWithHomologyOpposite`：∀ (C : Typ
e u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroMorphisms C]   [CategoryTheory.CategoryWithH…

--- 原说明 ---
The natural isomorphism `K.op.homology i ≅ op (K.homology i)`.
-/
def homologyOpNatIso :
    opFunctor V c ⋙ homologyFunctor Vᵒᵖ c.symm i ≅ (homologyFunctor V c i).op :=
  NatIso.ofComponents (fun K ↦ (unop K).homologyOp i)
    (fun _ ↦ homologyOp_hom_naturality _ _)

end

end

section

variable [Preadditive V]

/-
**HomologicalComplex.** 是 Mathlib 中的一个示例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : Preadditive (HomologicalComplex Vᵒᵖ c) := inferInstance
/-
**HomologicalComplex.opFunctor_additive** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：∀ {ι : Type u_1} {V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.Preadditive V], (Homological
Complex.opFunctor V c).Additive
参数：HomologicalComplex.opFunctor V c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance opFunctor_additive : (@opFunctor ι V _ c _).Additive where
/-
**HomologicalComplex.unopFunctor_additive** 是 Mathlib 中的一个定理，位于命名空间 `Homological
Complex`。
形式化陈述：∀ {ι : Type u_1} {V : Type u_2} [inst : CategoryTheory.Category.{v_1, u_2}
 V] {c : ComplexShape ι}   [inst_1 : CategoryTheory.Preadditive V], (Homological
Complex.unopFunctor V c).Additive
参数：HomologicalComplex.unopFunctor V c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Homotopy.op** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：op {F G : HomologicalComplex V c} {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂) : H
omotopy ((opFunctor V c).map φ₁.op) ((opFunctor V c).map φ₂.op) where hom i j
参数：h : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a homotopy between morphisms of homological complexes.
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
/-
**Homotopy.unop** 是 Mathlib 中的一个定义，位于命名空间 `Homotopy`。
形式化陈述：unop {F G : HomologicalComplex Vᵒᵖ c} {φ₁ φ₂ : F ⟶ G} (h : Homotopy φ₁ φ₂)
 : Homotopy ((unopFunctor V c).map φ₁.op) ((unopFunctor V c).map φ₂.op) where ho
m i j
参数：h : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between morphisms of homological complexes that is deduced
from a homotopy in the opposite category.
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

