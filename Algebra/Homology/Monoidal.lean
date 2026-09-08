/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The monoidal category structure on homological complexes

Let `c : ComplexShape I` with `I` an additive monoid. If `c` is equipped
with the data and axioms `c.TensorSigns`, then the category
`HomologicalComplex C c` can be equipped with a monoidal category
structure if `C` is a monoidal category such that `C` has certain
coproducts and both left/right tensoring commute with these.

In particular, we obtain a monoidal category structure on
`ChainComplex C ℕ` when `C` is an additive monoidal category.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Limits MonoidalCategory Category

namespace HomologicalComplex

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

/-- If `K₁` and `K₂` are two homological complexes, this is the property that
for all `j`, the coproduct of `K₁ i₁ ⊗ K₂ i₂` for `i₁ + i₂ = j` exists. -/
/-
**HomologicalComplex.HasTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：HasTensor (K₁ K₂ : HomologicalComplex C c)
参数：K₁ K₂ : HomologicalComplex C c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K₁` and `K₂` are two homological complexes, this is the property that
for all `j`, the coproduct of `K₁ i₁ ⊗ K₂ i₂` for `i₁ + i₂ = j` exists.
-/
abbrev HasTensor (K₁ K₂ : HomologicalComplex C c) := HasMapBifunctor K₁ K₂ (curriedTensor C) c

section

variable [DecidableEq I]

/-- The tensor product of two homological complexes. -/
/-
**HomologicalComplex.tensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：tensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂] : Homological
Complex C c
参数：K₁ K₂ : HomologicalComplex C c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two homological complexes.
-/
noncomputable abbrev tensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂] :
    HomologicalComplex C c :=
  mapBifunctor K₁ K₂ (curriedTensor C) c

/-- The inclusion `K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j` of a summand in
the tensor product of the homological complexes. -/
/-
**HomologicalComplex.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j` of a summand in
the tensor product of the homological complexes.
-/
noncomputable abbrev ιTensorObj (K₁ K₂ : HomologicalComplex C c) [HasTensor K₁ K₂]
    (i₁ i₂ j : I) (h : i₁ + i₂ = j) :
    K₁.X i₁ ⊗ K₂.X i₂ ⟶ (tensorObj K₁ K₂).X j :=
  ιMapBifunctor K₁ K₂ (curriedTensor C) c i₁ i₂ j h

/-- The tensor product of two morphisms of homological complexes. -/
/-
**HomologicalComplex.tensorHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`。
形式化陈述：tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L
₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] : tensorObj K₁ K₂ ⟶ tensorObj L₁ L₂
参数：f : K₁ ⟶ L₁；g : K₂ ⟶ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two morphisms of homological complexes.
-/
noncomputable abbrev tensorHom {K₁ K₂ L₁ L₂ : HomologicalComplex C c}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [HasTensor K₁ K₂] [HasTensor L₁ L₂] :
    tensorObj K₁ K₂ ⟶ tensorObj L₁ L₂ :=
  mapBifunctorMap f g _ _

/-- Given three homological complexes `K₁`, `K₂`, and `K₃`, this asserts that for
all `j`, the functor `- ⊗ K₃.X i₃` commutes with the coproduct of
the `K₁.X i₁ ⊗ K₂.X i₂` such that `i₁ + i₂ = j`. -/
/-
**HomologicalComplex.HasGoodTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCompl
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three homological complexes `K₁`, `K₂`, and `K₃`, this asserts that for
all `j`, the functor `- ⊗ K₃.X i₃` commutes with the coproduct of
the `K₁.X i₁ ⊗ K₂.X i₂` such that `i₁ + i₂ = j`.
-/
abbrev HasGoodTensor₁₂ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c

/-- Given three homological complexes `K₁`, `K₂`, and `K₃`, this asserts that for
all `j`, the functor `K₁.X i₁` commutes with the coproduct of
the `K₂.X i₂ ⊗ K₃.X i₃` such that `i₂ + i₃ = j`. -/
/-
**HomologicalComplex.HasGoodTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalCompl
ex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three homological complexes `K₁`, `K₂`, and `K₃`, this asserts that for
all `j`, the functor `K₁.X i₁` commutes with the coproduct of
the `K₂.X i₂ ⊗ K₃.X i₃` such that `i₂ + i₃ = j`.
-/
abbrev HasGoodTensor₂₃ (K₁ K₂ K₃ : HomologicalComplex C c) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) K₁ K₂ K₃ c c c

/-- The associator isomorphism for the tensor product of homological complexes. -/
/-
**HomologicalComplex.associator** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：associator (K₁ K₂ K₃ : HomologicalComplex C c) [HasTensor K₁ K₂] [HasTenso
r K₂ K₃] [HasTensor (tensorObj K₁ K₂) K₃] [HasTensor K₁ (tensorObj K₂ K₃)] [HasG
oodTensor₁₂ K₁ K₂ K₃] [HasGoodTensor₂₃ K₁ K₂ K₃] : tensorObj (tensorObj K₁ K₂) K
₃ ≅ tensorObj K₁ (tensorObj K₂ K₃)
参数：K₁ K₂ K₃ : HomologicalComplex C c；tensorObj K₁ K₂；tensorObj K₂ K₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ComplexShape.instAssociative`：∀ {I : Type u_7} [inst : AddMonoid I] (c :
 ComplexShape I) [inst_1 : c.TensorSigns], c.Associative c c c c c

--- 原说明 ---
The associator isomorphism for the tensor product of homological complexes.
-/
noncomputable abbrev associator (K₁ K₂ K₃ : HomologicalComplex C c)
    [HasTensor K₁ K₂] [HasTensor K₂ K₃]
    [HasTensor (tensorObj K₁ K₂) K₃] [HasTensor K₁ (tensorObj K₂ K₃)]
    [HasGoodTensor₁₂ K₁ K₂ K₃] [HasGoodTensor₂₃ K₁ K₂ K₃] :
    tensorObj (tensorObj K₁ K₂) K₃ ≅ tensorObj K₁ (tensorObj K₂ K₃) :=
  mapBifunctorAssociator (curriedAssociatorNatIso C) K₁ K₂ K₃ c c c

variable (C c) in
/-- The unit of the tensor product of homological complexes. -/
/-
**HomologicalComplex.tensorUnit** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：tensorUnit : HomologicalComplex C c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the tensor product of homological complexes.
-/
noncomputable abbrev tensorUnit : HomologicalComplex C c := (single C c 0).obj (𝟙_ C)

variable (C c) in
/-- As a graded object, the single complex `(single C c 0).obj (𝟙_ C)` identifies
to the unit `(GradedObject.single₀ I).obj (𝟙_ C)` of the tensor product of graded objects. -/
/-
**HomologicalComplex.tensorUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex
`。
形式化陈述：tensorUnitIso : (GradedObject.single₀ I).obj (𝟙_ C) ≅ (tensorUnit C c).X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C

--- 原说明 ---
As a graded object, the single complex `(single C c 0).obj (𝟙_ C)` identifies
to the unit `(GradedObject.single₀ I).obj (𝟙_ C)` of the tensor product of grade
d objects.
-/
noncomputable def tensorUnitIso :
    (GradedObject.single₀ I).obj (𝟙_ C) ≅ (tensorUnit C c).X :=
  GradedObject.isoMk _ _ (fun i ↦
    if hi : i = 0 then
      (GradedObject.singleObjApplyIsoOfEq (0 : I) (𝟙_ C) i hi).trans
        (singleObjXIsoOfEq c 0 (𝟙_ C) i hi).symm
    else
      { hom := 0
        inv := 0
        hom_inv_id := (GradedObject.isInitialSingleObjApply 0 (𝟙_ C) i hi).hom_ext _ _
        inv_hom_id := (isZero_single_obj_X c 0 (𝟙_ C) i hi).eq_of_src _ _ })

end

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K₁ K₂ : HomologicalComplex C c) [GradedObject.HasTensor K₁.X K₂.X] :
    HasTensor K₁ K₂ := by
  assumption
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X] :
    HasGoodTensor₁₂ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensor₁₂Tensor K₁.X K₂.X K₃.X)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K₁ K₂ K₃ : HomologicalComplex C c)
    [GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X] :
    HasGoodTensor₂₃ K₁ K₂ K₃ :=
  inferInstanceAs (GradedObject.HasGoodTensorTensor₂₃ K₁.X K₂.X K₃.X)

section

variable (K : HomologicalComplex C c) [DecidableEq I]

section

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GradedObject.HasTensor (tensorUnit C c).X K.X :=
  GradedObject.hasTensor_of_iso (tensorUnitIso C c) (Iso.refl _)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTensor (tensorUnit C c) K :=
  inferInstanceAs (GradedObject.HasTensor (tensorUnit C c).X K.X)

@[simp]
/-
**HomologicalComplex.unit_tensor_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unit_tensor_d₁ (i₁ i₂ j : I) :
    mapBifunctor.d₁ (tensorUnit C c) K (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

end

section

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GradedObject.HasTensor K.X (tensorUnit C c).X :=
  GradedObject.hasTensor_of_iso (Iso.refl _) (tensorUnitIso C c)
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTensor K (tensorUnit C c) :=
  inferInstanceAs (GradedObject.HasTensor K.X (tensorUnit C c).X)

@[simp]
/-
**HomologicalComplex.tensor_unit_d** 是 Mathlib 中的一个引理，位于命名空间 `HomologicalComplex
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensor_unit_d₂ (i₁ i₂ j : I) :
    mapBifunctor.d₂ K (tensorUnit C c) (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

end

end

section Unitor

variable (K : HomologicalComplex C c) [DecidableEq I]

section LeftUnitor

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `leftUnitor`. -/
/-
**HomologicalComplex.leftUnitor'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：leftUnitor' : (tensorObj (tensorUnit C c) K).X ≅ K.X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C] 
  [inst_2 : CategoryTheory.Pread…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `HomologicalComplex.instHasTensorXTensorUnit`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Pread…

--- 原说明 ---
Auxiliary definition for `leftUnitor`.
-/
noncomputable def leftUnitor' :
    (tensorObj (tensorUnit C c) K).X ≅ K.X :=
  GradedObject.Monoidal.tensorIso ((tensorUnitIso C c).symm) (Iso.refl _) ≪≫
    GradedObject.Monoidal.leftUnitor K.X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.leftUnitor'_inv** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalCompl
ex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Preadditive C] [ins
t_3 : CategoryTheory.Limits.HasZeroObject C]   [inst_4 : (CategoryTheory.Monoida
lCategory.curriedTensor C).Additive]   [inst_5 : ∀ (X₁ : C), ((CategoryTheory.Mo
noidalCategory.curriedTensor C).obj X₁).Additive] {I : Type u_2}   [inst_6 : Add
Monoid I] {c : ComplexShape I} [inst_7 : c.TensorSigns] (K : HomologicalComplex 
C c)   [inst_8 : DecidableEq I]   [inst_9 :     ∀ (X₂ : C),       CategoryTheory
.Limits.PreservesColimit (CategoryTheory.Functor.empty C)         ((CategoryTheo
ry.MonoidalCategory.curriedTensor C).flip.obj X₂)]   (i : I),   K.leftUnitor'.in
v i =     CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStr
uct.leftUnitor (K.X i)).inv       (CategoryTheory.CategoryStruct.comp         (C
ategoryTheory.MonoidalCategoryStruct.whiskerRight           (HomologicalComplex.
singleObjXSelf c 0 (CategoryTheory.MonoidalCategoryStruct.tensorUnit C)).inv (K.
X i))         ((HomologicalComplex.tensorUnit C c).ιTensorObj K 0 i i ⋯))
参数：CategoryTheory.MonoidalCategory.curriedTensor C；X₁ : C；(CategoryTheory.Monoid
alCategory.curriedTensor C).obj X₁；K : HomologicalComplex C c；X₂ : C；CategoryThe
ory.Functor.empty C；(CategoryTheory.MonoidalCategory.curriedTensor C).flip.obj X
₂；i : I；CategoryTheory.MonoidalCategoryStruct.leftUnitor (K.X i)；CategoryTheory.
CategoryStruct.comp         (CategoryTheory.MonoidalCategoryStruct.whiskerRight 
          (HomologicalComplex.singleObjXSelf c 0 (CategoryTheory.MonoidalCategor
yStruct.tensorUnit C)).inv (K.X i))         ((HomologicalComplex.tensorUnit C c)
.ιTensorObj K 0 i i ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C] 
  [inst_2 : CategoryTheory.Pread…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `HomologicalComplex.instHasTensorXTensorUnit`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Pread…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit`：∀ {I : Typ
e u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.Monoidal.leftUnitor_inv_apply`：leftUnitor_in
v_apply (i : I) : (leftUnitor X).inv i = (fun_ (X i)).inv ≫ tensorUnit₀.inv ▷ (X
 i) ≫ ιTensorObj tensorUnit X 0 i i (zero_add i…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.cancel_iso_inv_left`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} (g : Y ≅ Z) (f f' : Y ⟶ X),   CategoryTheor
y.CategoryStruct.comp g.inv …
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma leftUnitor'_inv (i : I) :
    (leftUnitor' K).inv i = (λ_ (K.X i)).inv ≫ ((singleObjXSelf c 0 (𝟙_ C)).inv ▷ (K.X i)) ≫
      ιTensorObj (tensorUnit C c) K 0 i i (zero_add i) := by
  dsimp [leftUnitor']
  rw [GradedObject.Monoidal.leftUnitor_inv_apply, assoc, assoc, Iso.cancel_iso_inv_left,
    GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [tensorHom_id, ← comp_whiskerRight_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom, Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**HomologicalComplex.leftUnitor'_inv_comm** 是 Mathlib 中的一个定理，位于命名空间 `Homological
Complex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Preadditive C] [ins
t_3 : CategoryTheory.Limits.HasZeroObject C]   [inst_4 : (CategoryTheory.Monoida
lCategory.curriedTensor C).Additive]   [inst_5 : ∀ (X₁ : C), ((CategoryTheory.Mo
noidalCategory.curriedTensor C).obj X₁).Additive] {I : Type u_2}   [inst_6 : Add
Monoid I] {c : ComplexShape I} [inst_7 : c.TensorSigns] (K : HomologicalComplex 
C c)   [inst_8 : DecidableEq I]   [inst_9 :     ∀ (X₂ : C),       CategoryTheory
.Limits.PreservesColimit (CategoryTheory.Functor.empty C)         ((CategoryTheo
ry.MonoidalCategory.curriedTensor C).flip.obj X₂)]   (i j : I),   CategoryTheory
.CategoryStruct.comp (K.leftUnitor'.inv i) (((HomologicalComplex.tensorUnit C c)
.tensorObj K).d i j) =     CategoryTheory.CategoryStruct.comp (K.d i j) (K.leftU
nitor'.inv j)
参数：CategoryTheory.MonoidalCategory.curriedTensor C；X₁ : C；(CategoryTheory.Monoid
alCategory.curriedTensor C).obj X₁；K : HomologicalComplex C c；X₂ : C；CategoryThe
ory.Functor.empty C；(CategoryTheory.MonoidalCategory.curriedTensor C).flip.obj X
₂；i j : I；K.leftUnitor'.inv i；((HomologicalComplex.tensorUnit C c).tensorObj K).
d i j；K.d i j；K.leftUnitor'.inv j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C] 
  [inst_2 : CategoryTheory.Pread…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.leftUnitor'_inv`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [inst_
2 : CategoryTheory.Pread…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.mapBifunctor.ι_D₁`：ι_D₁ : ιMapBifunctor K₁ K₂ F c i₁ 
i₂ j h ≫ D₁ K₁ K₂ F c j j' = d₁ K₁ K₂ F c i₁ i₂ j'
· 使用引理 `HomologicalComplex.unit_tensor_d₁`：unit_tensor_d₁ (i₁ i₂ j : I) : mapBif
unctor.d₁ (tensorUnit C c) K (curriedTensor C) c i₁ i₂ j = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `HomologicalComplex.mapBifunctor.ι_D₂`：ι_D₂ : ιMapBifunctor K₁ K₂ F c i₁ 
i₂ j h ≫ D₂ K₁ K₂ F c j j' = d₂ K₁ K₂ F c i₁ i₂ j'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.mapBifunctor.d₂_eq`：d₂_eq (i₁ : I₁) {i₂ i₂' : I₂} (h 
: c₂.Rel i₂ i₂') (j : J) (h' : ComplexShape.π c₁ c₂ c ⟨i₁, i₂'⟩ = j) : d₂ K₁ K₂ 
F c i₁ i₂ j = ComplexShape.…
· 使用引理 `ComplexShape.ε_zero`：ε_zero : c.ε 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma leftUnitor'_inv_comm (i j : I) :
    (leftUnitor' K).inv i ≫ (tensorObj (tensorUnit C c) K).d i j =
      K.d i j ≫ (leftUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [leftUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      unit_tensor_d₁, comp_zero, zero_add]
    rw [mapBifunctor.d₂_eq _ _ _ _ _ hij _ (by simp)]
    dsimp
    simp only [ComplexShape.ε_zero, one_smul, ← whisker_exchange_assoc,
      id_whiskerLeft, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

/-- The left unitor for the tensor product of homological complexes. -/
/-
**HomologicalComplex.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：leftUnitor : tensorObj (tensorUnit C c) K ≅ K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C] 
  [inst_2 : CategoryTheory.Pread…
· 使用定理 `HomologicalComplex.leftUnitor'_inv_comm`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [
inst_2 : CategoryTheory.Pread…

--- 原说明 ---
The left unitor for the tensor product of homological complexes.
-/
noncomputable def leftUnitor :
    tensorObj (tensorUnit C c) K ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i ↦ (GradedObject.eval i).mapIso (leftUnitor' K).symm)
    (fun _ _ _ ↦ leftUnitor'_inv_comm _ _ _))

end LeftUnitor

section RightUnitor

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `rightUnitor`. -/
/-
**HomologicalComplex.rightUnitor'** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`
。
形式化陈述：rightUnitor' : (tensorObj K (tensorUnit C c)).X ≅ K.X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit_1`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C
]   [inst_2 : CategoryTheory.Pread…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `HomologicalComplex.instHasTensorXTensorUnit_1`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory 
C]   [inst_2 : CategoryTheory.Pread…

--- 原说明 ---
Auxiliary definition for `rightUnitor`.
-/
noncomputable def rightUnitor' :
    (tensorObj K (tensorUnit C c)).X ≅ K.X :=
  GradedObject.Monoidal.tensorIso (Iso.refl _) ((tensorUnitIso C c).symm) ≪≫
    GradedObject.Monoidal.rightUnitor K.X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.rightUnitor'_inv** 是 Mathlib 中的一个定理，位于命名空间 `HomologicalComp
lex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Preadditive C] [ins
t_3 : CategoryTheory.Limits.HasZeroObject C]   [inst_4 : (CategoryTheory.Monoida
lCategory.curriedTensor C).Additive]   [inst_5 : ∀ (X₁ : C), ((CategoryTheory.Mo
noidalCategory.curriedTensor C).obj X₁).Additive] {I : Type u_2}   [inst_6 : Add
Monoid I] {c : ComplexShape I} [inst_7 : c.TensorSigns] (K : HomologicalComplex 
C c)   [inst_8 : DecidableEq I]   [inst_9 :     ∀ (X₁ : C),       CategoryTheory
.Limits.PreservesColimit (CategoryTheory.Functor.empty C)         ((CategoryTheo
ry.MonoidalCategory.curriedTensor C).obj X₁)]   (i : I),   K.rightUnitor'.inv i 
=     CategoryTheory.CategoryStruct.comp (CategoryTheory.MonoidalCategoryStruct.
rightUnitor (K.X i)).inv       (CategoryTheory.CategoryStruct.comp         (Cate
goryTheory.MonoidalCategoryStruct.whiskerLeft (K.X i)           (HomologicalComp
lex.singleObjXSelf c 0 (CategoryTheory.MonoidalCategoryStruct.tensorUnit C)).inv
)         (K.ιTensorObj (HomologicalComplex.tensorUnit C c) i 0 i ⋯))
参数：CategoryTheory.MonoidalCategory.curriedTensor C；X₁ : C；(CategoryTheory.Monoid
alCategory.curriedTensor C).obj X₁；K : HomologicalComplex C c；X₁ : C；CategoryThe
ory.Functor.empty C；(CategoryTheory.MonoidalCategory.curriedTensor C).obj X₁；i :
 I；CategoryTheory.MonoidalCategoryStruct.rightUnitor (K.X i)；CategoryTheory.Cate
goryStruct.comp         (CategoryTheory.MonoidalCategoryStruct.whiskerLeft (K.X 
i)           (HomologicalComplex.singleObjXSelf c 0 (CategoryTheory.MonoidalCate
goryStruct.tensorUnit C)).inv)         (K.ιTensorObj (HomologicalComplex.tensorU
nit C c) i 0 i ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit_1`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C
]   [inst_2 : CategoryTheory.Pread…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
· 使用定理 `HomologicalComplex.instHasTensorXTensorUnit_1`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory 
C]   [inst_2 : CategoryTheory.Pread…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit_1`：∀ {I : T
ype u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_
1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.Monoidal.rightUnitor_inv_apply`：rightUnitor_
inv_apply (i : I) : (rightUnitor X).inv i = (ρ_ (X i)).inv ≫ (X i) ◁ tensorUnit₀
.inv ≫ ιTensorObj X tensorUnit i 0 i (add_zero i…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.cancel_iso_inv_left`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} (g : Y ≅ Z) (f f' : Y ⟶ X),   CategoryTheor
y.CategoryStruct.comp g.inv …
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
lemma rightUnitor'_inv (i : I) :
    (rightUnitor' K).inv i = (ρ_ (K.X i)).inv ≫ ((K.X i) ◁ (singleObjXSelf c 0 (𝟙_ C)).inv) ≫
      ιTensorObj K (tensorUnit C c) i 0 i (add_zero i) := by
  dsimp [rightUnitor']
  rw [GradedObject.Monoidal.rightUnitor_inv_apply, assoc, assoc, Iso.cancel_iso_inv_left,
    GradedObject.Monoidal.ι_tensorHom]
  dsimp
  rw [id_tensorHom, ← whiskerLeft_comp_assoc]
  congr 2
  rw [← cancel_epi (GradedObject.Monoidal.tensorUnit₀ (I := I)).hom, Iso.hom_inv_id_assoc]
  dsimp [tensorUnitIso]
  rw [dif_pos rfl]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomologicalComplex.rightUnitor'_inv_comm** 是 Mathlib 中的一个定理，位于命名空间 `Homologica
lComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.MonoidalCategory C]   [inst_2 : CategoryTheory.Preadditive C] [ins
t_3 : CategoryTheory.Limits.HasZeroObject C]   [inst_4 : (CategoryTheory.Monoida
lCategory.curriedTensor C).Additive]   [inst_5 : ∀ (X₁ : C), ((CategoryTheory.Mo
noidalCategory.curriedTensor C).obj X₁).Additive] {I : Type u_2}   [inst_6 : Add
Monoid I] {c : ComplexShape I} [inst_7 : c.TensorSigns] (K : HomologicalComplex 
C c)   [inst_8 : DecidableEq I]   [inst_9 :     ∀ (X₁ : C),       CategoryTheory
.Limits.PreservesColimit (CategoryTheory.Functor.empty C)         ((CategoryTheo
ry.MonoidalCategory.curriedTensor C).obj X₁)]   (i j : I),   CategoryTheory.Cate
goryStruct.comp (K.rightUnitor'.inv i) ((K.tensorObj (HomologicalComplex.tensorU
nit C c)).d i j) =     CategoryTheory.CategoryStruct.comp (K.d i j) (K.rightUnit
or'.inv j)
参数：CategoryTheory.MonoidalCategory.curriedTensor C；X₁ : C；(CategoryTheory.Monoid
alCategory.curriedTensor C).obj X₁；K : HomologicalComplex C c；X₁ : C；CategoryThe
ory.Functor.empty C；(CategoryTheory.MonoidalCategory.curriedTensor C).obj X₁；i j
 : I；K.rightUnitor'.inv i；(K.tensorObj (HomologicalComplex.tensorUnit C c)).d i 
j；K.d i j；K.rightUnitor'.inv j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit_1`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C
]   [inst_2 : CategoryTheory.Pread…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomologicalComplex.rightUnitor'_inv`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]   [inst
_2 : CategoryTheory.Pread…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `HomologicalComplex.mapBifunctor.ι_D₁`：ι_D₁ : ιMapBifunctor K₁ K₂ F c i₁ 
i₂ j h ≫ D₁ K₁ K₂ F c j j' = d₁ K₁ K₂ F c i₁ i₂ j'
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.mapBifunctor.ι_D₂`：ι_D₂ : ιMapBifunctor K₁ K₂ F c i₁ 
i₂ j h ≫ D₂ K₁ K₂ F c j j' = d₂ K₁ K₂ F c i₁ i₂ j'
· 使用引理 `HomologicalComplex.tensor_unit_d₂`：tensor_unit_d₂ (i₁ i₂ j : I) : mapBif
unctor.d₂ K (tensorUnit C c) (curriedTensor C) c i₁ i₂ j = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HomologicalComplex.mapBifunctor.d₁_eq`：d₁_eq {i₁ i₁' : I₁} (h : c₁.Rel i
₁ i₁') (i₂ : I₂) (j : J) (h' : ComplexShape.π c₁ c₂ c ⟨i₁', i₂⟩ = j) : d₁ K₁ K₂ 
F c i₁ i₂ j = ComplexShape.…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `HomologicalComplex.shape`：∀ {ι : Type u_1} {V : Type u} [inst : Category
Theory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] 
{c : ComplexSh…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma rightUnitor'_inv_comm (i j : I) :
    (rightUnitor' K).inv i ≫ (tensorObj K (tensorUnit C c)).d i j =
      K.d i j ≫ (rightUnitor' K).inv j := by
  by_cases hij : c.Rel i j
  · simp only [rightUnitor'_inv, assoc, mapBifunctor.d_eq,
      Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
      tensor_unit_d₂, comp_zero, add_zero]
    rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
    dsimp
    simp only [one_smul, whisker_exchange_assoc, whiskerRight_id, assoc, Iso.inv_hom_id_assoc]
  · simp only [shape _ _ _ hij, comp_zero, zero_comp]

/-- The right unitor for the tensor product of homological complexes. -/
/-
**HomologicalComplex.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `HomologicalComplex`。
形式化陈述：rightUnitor : tensorObj K (tensorUnit C c) ≅ K
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instHasTensorTensorUnit_1`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C
]   [inst_2 : CategoryTheory.Pread…
· 使用定理 `HomologicalComplex.rightUnitor'_inv_comm`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.MonoidalCategory C]   
[inst_2 : CategoryTheory.Pread…

--- 原说明 ---
The right unitor for the tensor product of homological complexes.
-/
noncomputable def rightUnitor :
    tensorObj K (tensorUnit C c) ≅ K :=
  Iso.symm (Hom.isoOfComponents (fun i ↦ (GradedObject.eval i).mapIso (rightUnitor' K).symm)
    (fun _ _ _ ↦ rightUnitor'_inv_comm _ _ _))

end RightUnitor

end Unitor

variable (C c) [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I]

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.monoidalCategoryStruct** 是 Mathlib 中的一个实例，位于命名空间 `Homologic
alComplex`。
形式化陈述：monoidalCategoryStruct : MonoidalCategoryStruct (HomologicalComplex C c) w
here tensorObj K₁ K₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (HomologicalComplex C c) where
  tensorObj K₁ K₂ := tensorObj K₁ K₂
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom f g := tensorHom f g
  tensorUnit := tensorUnit C c
  associator K₁ K₂ K₃ := associator K₁ K₂ K₃
  leftUnitor K := leftUnitor K
  rightUnitor K := rightUnitor K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The structure which allows to construct the monoidal category structure
on `HomologicalComplex C c` from the monoidal category structure on
graded objects. -/
/-
**HomologicalComplex.Monoidal.inducingFunctorData** 是 Mathlib 中的一个定义，位于命名空间 `Hom
ologicalComplex.Monoidal`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.MonoidalCategory C] →       [inst_2 : CategoryTheory.Pread
ditive C] →         [inst_3 : CategoryTheory.Limits.HasZeroObject C] →          
 [inst_4 : (CategoryTheory.MonoidalCategory.curriedTensor C).Additive] →        
     [inst_5 : ∀ (X₁ : C), ((CategoryTheory.MonoidalCategory.curriedTensor C).ob
j X₁).Additive] →               {I : Type u_2} →                 [inst_6 : AddMo
noid I] →                   (c : ComplexShape I) →                     [inst_7 :
 c.TensorSigns] →                       [inst_8 : ∀ (X₁ X₂ : CategoryTheory.Grad
edObject I C), X₁.HasTensor X₂] →                         [inst_9 :             
                ∀ (X₁ : C),                               CategoryTheory.Limits.
PreservesColimit (CategoryTheory.Functor.empty C)                               
  ((CategoryTheory.MonoidalCategory.curriedTensor C).obj X₁)] →                 
          [inst_10 :                               ∀ (X₂ : C),                  
               CategoryTheory.Limits.PreservesColimit (CategoryTheory.Functor.em
pty C)                                   ((CategoryTheory.MonoidalCategory.curri
edTensor C).flip.obj X₂)] →                             [inst_11 :              
                   ∀ (X₁ X₂ X₃ X₄ : CategoryTheory.GradedObject I C), X₁.HasTens
or₄ObjExt X₂ X₃ X₄] →                               [inst_12 :                  
                 ∀ (X₁ X₂ X₃ : CategoryTheory.GradedObject I C), X₁.HasGoodTenso
r₁₂Tensor X₂ X₃] →                                 [inst_13 :                   
                  ∀ (X₁ X₂ X₃ : CategoryTheory.GradedObject I C), X₁.HasGoodTens
orTensor₂₃ X₂ X₃] →                                   [inst_14 : DecidableEq I] 
→                                     CategoryTheory.Monoidal.InducingFunctorDat
a (HomologicalComplex.forget C c)
参数：CategoryTheory.MonoidalCategory.curriedTensor C；CategoryTheory.MonoidalCatego
ry.curriedTensor C；CategoryTheory.MonoidalCategory.curriedTensor C。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C

--- 原说明 ---
The structure which allows to construct the monoidal category structure
on `HomologicalComplex C c` from the monoidal category structure on
graded objects.
-/
noncomputable def Monoidal.inducingFunctorData :
    Monoidal.InducingFunctorData (forget C c) where
  μIso _ _ := Iso.refl _
  εIso := tensorUnitIso C c
  whiskerLeft_eq K₁ K₂ L₂ g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  whiskerRight_eq {K₁ L₁} f K₂ := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  tensorHom_eq {K₁ L₁ K₂ L₂} f g := by
    dsimp [forget]
    rw [comp_id]
    erw [id_comp]
    rfl
  associator_eq K₁ K₂ K₃ := by
    dsimp [forget]
    simp only [tensorHom_id, whiskerRight_tensor, id_whiskerRight,
      id_comp, Iso.inv_hom_id, comp_id, assoc]
    erw [id_whiskerRight]
    rw [id_comp]
    erw [id_comp]
    rfl
  leftUnitor_eq K := by
    dsimp
    erw [id_comp]
    rfl
  rightUnitor_eq K := by
    dsimp
    rw [assoc]
    erw [id_comp]
    rfl
/-
**HomologicalComplex.monoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComp
lex`。
形式化陈述：monoidalCategory : MonoidalCategory (HomologicalComplex C c)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasInitial`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cate
goryTheory.Limits.HasInitial C
-/
noncomputable instance monoidalCategory : MonoidalCategory (HomologicalComplex C c) :=
  Monoidal.induced _ (Monoidal.inducingFunctorData C c)

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomologicalComplex.** 是 Mathlib 中的一个示例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example {D : Type*} [Category* D] [Preadditive D] [MonoidalCategory D]
    [HasZeroObject D] [HasFiniteCoproducts D] [((curriedTensor D).Additive)]
    [∀ (X : D), (((curriedTensor D).obj X).Additive)]
    [∀ (X : D), PreservesFiniteCoproducts ((curriedTensor D).obj X)]
    [∀ (X : D), PreservesFiniteCoproducts ((curriedTensor D).flip.obj X)] :
    MonoidalCategory (ChainComplex D ℕ) := inferInstance

end HomologicalComplex

