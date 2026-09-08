/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
/-!
# The homology of single complexes

The main definition in this file is `HomologicalComplex.homologyFunctorSingleIso`
which is a natural isomorphism `single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`.

-/

@[expose] public section

universe v u

open CategoryTheory Category Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

namespace HomologicalComplex

variable (A : C)

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : ((single C c j).obj A).HasHomology i := by
  apply ShortComplex.hasHomology_of_zeros
/-
**HomologicalComplex.exactAt_single_obj** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalCo
mplex`。
形式化陈述：exactAt_single_obj (A : C) (i : ι) (hi : i != j) : ExactAt ((single C c j)
.obj A) i
参数：A : C；i : ι；hi : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.exact_of_isZero_X₂`：exact_of_isZero_X₂ (h : 
IsZero S.X₂) : S.Exact
· 使用引理 `HomologicalComplex.isZero_single_obj_X`：isZero_single_obj_X (j : ι) (A :
 V) (i : ι) (hi : i != j) : IsZero (((single V c j).obj A).X i)
-/
lemma exactAt_single_obj (A : C) (i : ι) (hi : i ≠ j) :
    ExactAt ((single C c j).obj A) i :=
  ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)
/-
**HomologicalComplex.isZero_single_obj_homology** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：isZero_single_obj_homology (A : C) (i : ι) (hi : i != j) : IsZero (((singl
e C c j).obj A).homology i)
参数：A : C；i : ι；hi : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用引理 `HomologicalComplex.exactAt_single_obj`：exactAt_single_obj (A : C) (i : ι
) (hi : i != j) : ExactAt ((single C c j).obj A) i
-/
lemma isZero_single_obj_homology (A : C) (i : ι) (hi : i ≠ j) :
    IsZero (((single C c j).obj A).homology i) := by
  simpa only [← exactAt_iff_isZero_homology]
    using exactAt_single_obj c j A i hi

/-- The canonical isomorphism `((single C c j).obj A).cycles j ≅ A` -/
/-
**HomologicalComplex.singleObjCyclesSelfIso** 是 Mathlib 中的一个定义，位于命名空间 `Homologic
alComplex`。
形式化陈述：singleObjCyclesSelfIso : ((single C c j).obj A).cycles j ≅ A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…

--- 原说明 ---
The canonical isomorphism `((single C c j).obj A).cycles j ≅ A`
-/
noncomputable def singleObjCyclesSelfIso :
    ((single C c j).obj A).cycles j ≅ A :=
  ((single C c j).obj A).iCyclesIso j _ rfl rfl ≪≫ singleObjXSelf c j A

@[reassoc]
/-
**HomologicalComplex.singleObjCyclesSelfIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：singleObjCyclesSelfIso_hom : (singleObjCyclesSelfIso c j A).hom = ((single
 C c j).obj A).iCycles j ≫ (singleObjXSelf c j A).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
-/
lemma singleObjCyclesSelfIso_hom :
    (singleObjCyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ (singleObjXSelf c j A).hom := rfl

/-- The canonical isomorphism `((single C c j).obj A).opcycles j ≅ A` -/
/-
**HomologicalComplex.singleObjOpcyclesSelfIso** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex`。
形式化陈述：singleObjOpcyclesSelfIso : A ≅ ((single C c j).obj A).opcycles j
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…

--- 原说明 ---
The canonical isomorphism `((single C c j).obj A).opcycles j ≅ A`
-/
noncomputable def singleObjOpcyclesSelfIso :
    A ≅ ((single C c j).obj A).opcycles j :=
  (singleObjXSelf c j A).symm ≪≫ ((single C c j).obj A).pOpcyclesIso _ j rfl rfl

@[reassoc]
/-
**HomologicalComplex.singleObjOpcyclesSelfIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Hom
ologicalComplex`。
形式化陈述：singleObjOpcyclesSelfIso_hom : (singleObjOpcyclesSelfIso c j A).hom = (sin
gleObjXSelf c j A).inv ≫ ((single C c j).obj A).pOpcycles j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
-/
lemma singleObjOpcyclesSelfIso_hom :
    (singleObjOpcyclesSelfIso c j A).hom =
      (singleObjXSelf c j A).inv ≫ ((single C c j).obj A).pOpcycles j := rfl

/-- The canonical isomorphism `((single C c j).obj A).homology j ≅ A` -/
/-
**HomologicalComplex.singleObjHomologySelfIso** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex`。
形式化陈述：singleObjHomologySelfIso : ((single C c j).obj A).homology j ≅ A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…

--- 原说明 ---
The canonical isomorphism `((single C c j).obj A).homology j ≅ A`
-/
noncomputable def singleObjHomologySelfIso :
    ((single C c j).obj A).homology j ≅ A :=
  (((single C c j).obj A).isoHomologyπ _ j rfl rfl).symm ≪≫ singleObjCyclesSelfIso c j A

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles** 是 Mathlib 中的一个引理，位于命名空
间 `HomologicalComplex`。
形式化陈述：singleObjCyclesSelfIso_inv_iCycles : (singleObjCyclesSelfIso _ _ _).inv ≫ 
((single C c j).obj A).iCycles j = (singleObjXSelf c j A).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.iCyclesIso_inv_hom_id`：iCyclesIso_inv_hom_id : (K.iCy
clesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma singleObjCyclesSelfIso_inv_iCycles :
    (singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).iCycles j =
      (singleObjXSelf c j A).inv := by
  simp [singleObjCyclesSelfIso]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyπ_singleObjHomologySelfIso_hom :
    ((single C c j).obj A).homologyπ j ≫ (singleObjHomologySelfIso _ _ _).hom =
      (singleObjCyclesSelfIso _ _ _).hom := by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv**
 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv : (singleObjCycl
esSelfIso c j A).hom ≫ (singleObjHomologySelfIso c j A).inv = ((single C c j).ob
j A).homologyπ j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom`：homologyπ_sin
gleObjHomologySelfIso_hom : ((single C c j).obj A).homologyπ j ≫ (singleObjHomol
ogySelfIso _ _ _).hom = (singleObjCyclesSelfIso…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv :
    (singleObjCyclesSelfIso c j A).hom ≫ (singleObjHomologySelfIso c j A).inv =
      ((single C c j).obj A).homologyπ j := by
  simp only [← cancel_mono (singleObjHomologySelfIso _ _ _).hom, assoc,
    Iso.inv_hom_id, comp_id, homologyπ_singleObjHomologySelfIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom** 是
 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom : (singleObjCycles
SelfIso c j A).hom ≫ (singleObjOpcyclesSelfIso c j A).hom = ((single C c j).obj 
A).iCycles j ≫ ((single C c j).obj A).pOpcycles j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HomologicalComplex.iCyclesIso_hom`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   
{ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.pOpcyclesIso_hom`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (singleObjCyclesSelfIso c j A).hom ≫ (singleObjOpcyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ ((single C c j).obj A).pOpcycles j := by
  simp [singleObjCyclesSelfIso, singleObjOpcyclesSelfIso]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjCyclesSelfIso_inv_homology** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleObjCyclesSelfIso_inv_homologyπ :
    (singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyπ j =
      (singleObjHomologySelfIso _ _ _).inv := by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjHomologySelfIso_inv_homology** 是 Mathlib 中的一个引理，位于
命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleObjHomologySelfIso_inv_homologyι :
    (singleObjHomologySelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyι j =
      (singleObjOpcyclesSelfIso _ _ _).hom := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom,
    singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc, homology_π_ι,
    singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.homology** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：homology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homologyι_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).homologyι j ≫ (singleObjOpcyclesSelfIso _ _ _).inv =
      (singleObjHomologySelfIso _ _ _).hom := by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv,
    singleObjHomologySelfIso_inv_homologyι_assoc, Iso.hom_inv_id, Iso.inv_hom_id]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom**
 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom : (singleObjHomo
logySelfIso _ _ _).hom ≫ (singleObjOpcyclesSelfIso _ _ _).hom = ((single C c j).
obj A).homologyι j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `HomologicalComplex.singleObjHomologySelfIso_inv_homologyι`：singleObjHomo
logySelfIso_inv_homologyι : (singleObjHomologySelfIso _ _ _).inv ≫ ((single C c 
j).obj A).homologyι j = (singleObjOpcyclesSelfI…
-/
lemma singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (singleObjHomologySelfIso _ _ _).hom ≫ (singleObjOpcyclesSelfIso _ _ _).hom =
      ((single C c j).obj A).homologyι j := by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv,
    Iso.inv_hom_id_assoc, singleObjHomologySelfIso_inv_homologyι]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.pOpcycles_singleObjOpcyclesSelfIso_inv** 是 Mathlib 中的一个引理，位
于命名空间 `HomologicalComplex`。
形式化陈述：pOpcycles_singleObjOpcyclesSelfIso_inv : ((single C c j).obj A).pOpcycles 
j ≫ (singleObjOpcyclesSelfIso _ _ _).inv = (singleObjXSelf c j A).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用引理 `HomologicalComplex.isIso_iCycles`：isIso_iCycles : IsIso (K.iCycles i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `HomologicalComplex.homology_π_ι_assoc`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.homologyι_singleObjOpcyclesSelfIso_inv`：homologyι_sin
gleObjOpcyclesSelfIso_inv : ((single C c j).obj A).homologyι j ≫ (singleObjOpcyc
lesSelfIso _ _ _).inv = (singleObjHomologySelfI…
· 使用引理 `HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom`：homologyπ_sin
gleObjHomologySelfIso_hom : ((single C c j).obj A).homologyπ j ≫ (singleObjHomol
ogySelfIso _ _ _).hom = (singleObjCyclesSelfIso…
· 使用引理 `HomologicalComplex.singleObjCyclesSelfIso_hom`：singleObjCyclesSelfIso_ho
m : (singleObjCyclesSelfIso c j A).hom = ((single C c j).obj A).iCycles j ≫ (sin
gleObjXSelf c j A).hom
-/
lemma pOpcycles_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).pOpcycles j ≫ (singleObjOpcyclesSelfIso _ _ _).inv =
      (singleObjXSelf c j A).hom := by
  have := ((single C c j).obj A).isIso_iCycles j _ rfl (by simp)
  rw [← cancel_epi (((single C c j).obj A).iCycles j),
    ← HomologicalComplex.homology_π_ι_assoc, homologyι_singleObjOpcyclesSelfIso_inv,
    homologyπ_singleObjHomologySelfIso_hom, singleObjCyclesSelfIso_hom]

variable {A}
variable {B : C} (f : A ⟶ B)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjCyclesSelfIso_hom_naturality** 是 Mathlib 中的一个引理，位于
命名空间 `HomologicalComplex`。
形式化陈述：singleObjCyclesSelfIso_hom_naturality : cyclesMap ((single C c j).map f) j
 ≫ (singleObjCyclesSelfIso c j B).hom = (singleObjCyclesSelfIso c j A).hom ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `HomologicalComplex.instMonoICycles`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {ι : Type u_2} {c : Com…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `HomologicalComplex.cyclesMap_i`：cyclesMap_i : cyclesMap φ i ≫ L.iCycles 
i = K.iCycles i ≫ φ.f i
· 使用定理 `HomologicalComplex.single_map_f_self`：single_map_f_self (j : ι) {A B : V
} (f : A ⟶ B) : ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫ f ≫ (s
ingleObjXSelf c j B).inv
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.iCyclesIso_hom`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   
{ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.iCyclesIso_inv_hom_id`：iCyclesIso_inv_hom_id : (K.iCy
clesIso i j hj h).inv ≫ K.iCycles i = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma singleObjCyclesSelfIso_hom_naturality :
    cyclesMap ((single C c j).map f) j ≫ (singleObjCyclesSelfIso c j B).hom =
      (singleObjCyclesSelfIso c j A).hom ≫ f := by
  rw [← cancel_mono (singleObjCyclesSelfIso c j B).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← cancel_mono (iCycles _ _)]
  simp only [cyclesMap_i, singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, Iso.trans_inv,
    assoc, iCyclesIso_inv_hom_id, comp_id, single_map_f_self]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjCyclesSelfIso_inv_naturality** 是 Mathlib 中的一个引理，位于
命名空间 `HomologicalComplex`。
形式化陈述：singleObjCyclesSelfIso_inv_naturality : (singleObjCyclesSelfIso c j A).inv
 ≫ cyclesMap ((single C c j).map f) j = f ≫ (singleObjCyclesSelfIso c j B).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `HomologicalComplex.singleObjCyclesSelfIso_hom_naturality_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits
.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma singleObjCyclesSelfIso_inv_naturality :
    (singleObjCyclesSelfIso c j A).inv ≫ cyclesMap ((single C c j).map f) j =
      f ≫ (singleObjCyclesSelfIso c j B).inv := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom, Iso.hom_inv_id_assoc,
    ← singleObjCyclesSelfIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjHomologySelfIso_hom_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjHomologySelfIso_hom_naturality : homologyMap ((single C c j).map 
f) j ≫ (singleObjHomologySelfIso c j B).hom = (singleObjHomologySelfIso c j A).h
om ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiHomologyπ`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {ι : Type u_2} {c : Com…
· 使用定理 `HomologicalComplex.homologyπ_naturality_assoc`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {ι : Type u_2} {c : Com…
· 使用引理 `HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom`：homologyπ_sin
gleObjHomologySelfIso_hom : ((single C c j).obj A).homologyπ j ≫ (singleObjHomol
ogySelfIso _ _ _).hom = (singleObjCyclesSelfIso…
· 使用引理 `HomologicalComplex.singleObjCyclesSelfIso_hom_naturality`：singleObjCycle
sSelfIso_hom_naturality : cyclesMap ((single C c j).map f) j ≫ (singleObjCyclesS
elfIso c j B).hom = (singleObjCyclesSelfIso c …
· 使用定理 `HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limit
s.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limi…
-/
lemma singleObjHomologySelfIso_hom_naturality :
    homologyMap ((single C c j).map f) j ≫ (singleObjHomologySelfIso c j B).hom =
      (singleObjHomologySelfIso c j A).hom ≫ f := by
  rw [← cancel_epi (((single C c j).obj A).homologyπ j),
    homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom_naturality, homologyπ_singleObjHomologySelfIso_hom_assoc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjHomologySelfIso_inv_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjHomologySelfIso_inv_naturality : (singleObjHomologySelfIso c j A)
.inv ≫ homologyMap ((single C c j).map f) j = f ≫ (singleObjHomologySelfIso c j 
B).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.singleObjHomologySelfIso_hom_naturality`：singleObjHom
ologySelfIso_hom_naturality : homologyMap ((single C c j).map f) j ≫ (singleObjH
omologySelfIso c j B).hom = (singleObjHomologySe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma singleObjHomologySelfIso_inv_naturality :
    (singleObjHomologySelfIso c j A).inv ≫ homologyMap ((single C c j).map f) j =
      f ≫ (singleObjHomologySelfIso c j B).inv := by
  rw [← cancel_mono (singleObjHomologySelfIso c j B).hom, assoc, assoc,
    singleObjHomologySelfIso_hom_naturality,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjOpcyclesSelfIso_hom_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjOpcyclesSelfIso_hom_naturality : (singleObjOpcyclesSelfIso c j A)
.hom ≫ opcyclesMap ((single C c j).map f) j = f ≫ (singleObjOpcyclesSelfIso c j 
B).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `HomologicalComplex.singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_h
om_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Cat
egoryTheory.Limits.HasZeroMorphisms C]   [inst_2 : CategoryTheory.Limi…
· 使用引理 `HomologicalComplex.p_opcyclesMap`：p_opcyclesMap : K.pOpcycles i ≫ opcycl
esMap φ i = φ.f i ≫ L.pOpcycles i
· 使用定理 `HomologicalComplex.single_map_f_self`：single_map_f_self (j : ι) {A B : V
} (f : A ⟶ B) : ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫ f ≫ (s
ingleObjXSelf c j B).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.singleObjCyclesSelfIso_hom`：singleObjCyclesSelfIso_ho
m : (singleObjCyclesSelfIso c j A).hom = ((single C c j).obj A).iCycles j ≫ (sin
gleObjXSelf c j A).hom
· 使用引理 `HomologicalComplex.singleObjOpcyclesSelfIso_hom`：singleObjOpcyclesSelfIs
o_hom : (singleObjOpcyclesSelfIso c j A).hom = (singleObjXSelf c j A).inv ≫ ((si
ngle C c j).obj A).pOpcycles j
-/
lemma singleObjOpcyclesSelfIso_hom_naturality :
    (singleObjOpcyclesSelfIso c j A).hom ≫ opcyclesMap ((single C c j).map f) j =
      f ≫ (singleObjOpcyclesSelfIso c j B).hom := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom,
    singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc, p_opcyclesMap,
    single_map_f_self, assoc, assoc, singleObjCyclesSelfIso_hom,
    singleObjOpcyclesSelfIso_hom, assoc]

@[reassoc (attr := simp)]
/-
**HomologicalComplex.singleObjOpcyclesSelfIso_inv_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `HomologicalComplex`。
形式化陈述：singleObjOpcyclesSelfIso_inv_naturality : opcyclesMap ((single C c j).map 
f) j ≫ (singleObjOpcyclesSelfIso c j B).inv = (singleObjOpcyclesSelfIso c j A).i
nv ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasHomologyObjSingle`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `HomologicalComplex.singleObjOpcyclesSelfIso_hom_naturality`：singleObjOpc
yclesSelfIso_hom_naturality : (singleObjOpcyclesSelfIso c j A).hom ≫ opcyclesMap
 ((single C c j).map f) j = f ≫ (singleObjOpcycl…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma singleObjOpcyclesSelfIso_inv_naturality :
    opcyclesMap ((single C c j).map f) j ≫ (singleObjOpcyclesSelfIso c j B).inv =
      (singleObjOpcyclesSelfIso c j A).inv ≫ f := by
  rw [← cancel_mono (singleObjOpcyclesSelfIso c j B).hom, assoc, assoc, Iso.inv_hom_id,
    comp_id, ← singleObjOpcyclesSelfIso_hom_naturality, Iso.inv_hom_id_assoc]

variable (C)

/-- The computation of the homology of single complexes, as a natural isomorphism
`single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`. -/
@[simps!]
/-
**HomologicalComplex.homologyFunctorSingleIso** 是 Mathlib 中的一个定义，位于命名空间 `Homolog
icalComplex`。
形式化陈述：homologyFunctorSingleIso [CategoryWithHomology C] : single C c j ⋙ homolog
yFunctor C c j ≅ 𝟭 _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.singleObjHomologySelfIso_hom_naturality`：singleObjHom
ologySelfIso_hom_naturality : homologyMap ((single C c j).map f) j ≫ (singleObjH
omologySelfIso c j B).hom = (singleObjHomologySe…

--- 原说明 ---
The computation of the homology of single complexes, as a natural isomorphism
`single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`.
-/
noncomputable def homologyFunctorSingleIso [CategoryWithHomology C] :
    single C c j ⋙ homologyFunctor C c j ≅ 𝟭 _ :=
  NatIso.ofComponents (fun A => (singleObjHomologySelfIso c j A))
    (fun f => singleObjHomologySelfIso_hom_naturality c j f)

end HomologicalComplex

open HomologicalComplex

/-
**ChainComplex.exactAt_succ_single_obj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ChainComplex.exactAt_succ_single_obj (A : C) (n : Nat) : ExactAt ((single₀
 C).obj A) (n + 1)
参数：A : C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.exactAt_single_obj`：exactAt_single_obj (A : C) (i : ι
) (hi : i != j) : ExactAt ((single C c j).obj A) i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma ChainComplex.exactAt_succ_single_obj (A : C) (n : ℕ) :
    ExactAt ((single₀ C).obj A) (n + 1) :=
  exactAt_single_obj _ _ _ _ (by simp)
/-
**CochainComplex.exactAt_succ_single_obj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CochainComplex.exactAt_succ_single_obj (A : C) (n : Nat) : ExactAt ((singl
e₀ C).obj A) (n + 1)
参数：A : C；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.exactAt_single_obj`：exactAt_single_obj (A : C) (i : ι
) (hi : i != j) : ExactAt ((single C c j).obj A) i
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma CochainComplex.exactAt_succ_single_obj (A : C) (n : ℕ) :
    ExactAt ((single₀ C).obj A) (n + 1) :=
  exactAt_single_obj _ _ _ _ (by simp)
