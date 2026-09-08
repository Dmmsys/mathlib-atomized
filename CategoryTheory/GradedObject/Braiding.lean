/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
/-!
# The braided and symmetric category structures on graded objects

In this file, we construct the braiding
`GradedObject.Monoidal.braiding : tensorObj X Y ≅ tensorObj Y X`
for two objects `X` and `Y` in `GradedObject I C`, when `I` is a commutative
additive monoid (and suitable coproducts exist in a braided category `C`).

When `C` is a braided category and suitable assumptions are made, we obtain the braided category
structure on `GradedObject I C` and show that it is symmetric if `C` is symmetric.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {I : Type*} [AddCommMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]

namespace GradedObject

namespace Monoidal

variable (X Y Z : GradedObject I C)

section Braided

variable [BraidedCategory C]

set_option backward.isDefEq.respectTransparency.types false in
/-- The braiding `tensorObj X Y ≅ tensorObj Y X` when `X` and `Y` are graded objects
indexed by a commutative additive monoid. -/
/-
**CategoryTheory.GradedObject.Monoidal.braiding** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.GradedObject.Monoidal`。
形式化陈述：braiding [HasTensor X Y] [HasTensor Y X] : tensorObj X Y ≅ tensorObj Y X w
here hom k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The braiding `tensorObj X Y ≅ tensorObj Y X` when `X` and `Y` are graded objects
indexed by a commutative additive monoid.
-/
noncomputable def braiding [HasTensor X Y] [HasTensor Y X] : tensorObj X Y ≅ tensorObj Y X where
  hom k := tensorObjDesc (fun i j hij => (β_ _ _).hom ≫
    ιTensorObj Y X j i k (by simpa only [add_comm j i] using hij))
  inv k := tensorObjDesc (fun i j hij => (β_ _ _).inv ≫
    ιTensorObj X Y j i k (by simpa only [add_comm j i] using hij))

set_option backward.isDefEq.respectTransparency.types false in
variable {Y Z} in
/-
**CategoryTheory.GradedObject.Monoidal.braiding_naturality_right** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：braiding_naturality_right [HasTensor X Y] [HasTensor Y X] [HasTensor X Z] 
[HasTensor Z X] (f : Y ⟶ Z) : whiskerLeft X f ≫ (braiding X Z).hom = (braiding X
 Y).hom ≫ whiskerRight f X
参数：f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorObj_ext`：tensorObj_ext {A : C
} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A) (h : forall (i₁ i₂ : I) (hi : i₁ + i₂ = 
j), ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc`：∀ {I : Type u} [
inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc`：ι_tensorObjDesc {A
 : C} {k : I} (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A)
 (i₁ i₂ : I) (hi : i₁ + i₂ = k) : ιTensorO…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_right_assoc`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoid
alCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma braiding_naturality_right [HasTensor X Y] [HasTensor Y X] [HasTensor X Z] [HasTensor Z X]
    (f : Y ⟶ Z) :
    whiskerLeft X f ≫ (braiding X Z).hom = (braiding X Y).hom ≫ whiskerRight f X := by
  dsimp [braiding]
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
variable {X Y} in
/-
**CategoryTheory.GradedObject.Monoidal.braiding_naturality_left** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：braiding_naturality_left [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z] [
HasTensor Z X] (f : X ⟶ Y) : whiskerRight f Z ≫ (braiding Y Z).hom = (braiding X
 Z).hom ≫ whiskerLeft Z f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorObj_ext`：tensorObj_ext {A : C
} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A) (h : forall (i₁ i₂ : I) (hi : i₁ + i₂ = 
j), ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc`：∀ {I : Type u} [
inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc`：ι_tensorObjDesc {A
 : C} {k : I} (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A)
 (i₁ i₂ : I) (hi : i₁ + i₂ = k) : ιTensorO…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left_assoc`：∀ {C : Ty
pe u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Monoida
lCategory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma braiding_naturality_left [HasTensor Y Z] [HasTensor Z Y] [HasTensor X Z] [HasTensor Z X]
    (f : X ⟶ Y) :
    whiskerRight f Z ≫ (braiding Y Z).hom = (braiding X Z).hom ≫ whiskerLeft Z f := by
  dsimp [braiding]
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GradedObject.Monoidal.hexagon_forward** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：hexagon_forward [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z] [HasTensor
 Z X] [HasTensor X Z] [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)
] [HasTensor (tensorObj Y Z) X] [HasTensor Y (tensorObj Z X)] [HasTensor (tensor
Obj Y X) Z] [HasTensor Y (tensorObj X Z)] [HasGoodTensor₁₂Tensor X Y Z] [HasGood
TensorTensor₂₃ X Y Z] [HasGoodTensor₁₂Tensor Y Z X] [HasGoodTensorTensor₂₃ Y Z X
] [HasGoodTensor₁₂Tensor Y X Z] [HasGoodTensorTensor₂₃ Y X Z] : (associator X Y 
Z).hom ≫ (braiding X (tens
参数：tensorObj X Y；tensorObj Y Z；tensorObj Y Z；tensorObj Z X；tensorObj Y X；tensorO
bj X Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.GradedObject.Monoidal.tensorObj₃'_ext`：∀ {I : Type u} [in
st : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]
   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc`：
∀ {I : Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_eq`：ιTensorObj₃_eq (i₁ 
i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) : ιTensorObj₃
 X₁ X₂ X₃ i₁ i₂ i₃ j h = (X₁ i₁ ◁ ιTensor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_right_hom`：braiding_tenso
r_right_hom (X Y Z : C) : (β_ X (Y otimes Z)).hom = (α_ X Y Z).inv ≫ (β_ X Y).ho
m ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (β_ X Z).hom ≫ (α…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_eq_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_associator_hom`：∀ {I :
 Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{
v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_eq`：∀ {I : Type u} [in
st : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]
   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc`：∀ {I : Type u} [
inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc`：ι_tensorObjDesc {A
 : C} {k : I} (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A)
 (i₁ i₂ : I) (hi : i₁ + i₂ = k) : ιTensorO…
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_id`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (β : Type w) (X : (i : β) → (fun x => C
) i) (i : β),   CategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_tensor_id`：comp_tensor_id (f : W ⟶ 
X) (g : X ⟶ Y) : f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z)
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensor_comp_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {W X Y Z : C}   (f : W ⟶ X) (g : X ⟶ Y…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensor_comp`：id_tensor_comp (f : W ⟶ 
X) (g : X ⟶ Y) : 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ f) ≫ (𝟙 Z otimesₘ g)
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp`：whiskerLeft_comp (W : 
C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W ◁ (f ≫ g) = W ◁ f ≫ W ◁ g
-/
lemma hexagon_forward [HasTensor X Y] [HasTensor Y X] [HasTensor Y Z]
    [HasTensor Z X] [HasTensor X Z]
    [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
    [HasTensor (tensorObj Y Z) X] [HasTensor Y (tensorObj Z X)]
    [HasTensor (tensorObj Y X) Z] [HasTensor Y (tensorObj X Z)]
    [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
    [HasGoodTensor₁₂Tensor Y Z X] [HasGoodTensorTensor₂₃ Y Z X]
    [HasGoodTensor₁₂Tensor Y X Z] [HasGoodTensorTensor₂₃ Y X Z] :
    (associator X Y Z).hom ≫ (braiding X (tensorObj Y Z)).hom ≫ (associator Y Z X).hom =
      whiskerRight (braiding X Y).hom Z ≫ (associator Y X Z).hom ≫
        whiskerLeft Y (braiding X Z).hom := by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl,
    assoc, ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.id_tensorHom,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_right_hom, assoc, assoc, assoc, assoc, Iso.hom_inv_id_assoc,
    MonoidalCategory.tensorHom_id,
    ← ιTensorObj₃'_eq_assoc Y Z X i₂ i₃ i₁ k (by rw [add_comm _ i₁, ← add_assoc, h]) _ rfl,
    ιTensorObj₃'_associator_hom, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc, ι_tensorHom_assoc,
    ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp, ι_tensorObjDesc,
    categoryOfGradedObjects_id, MonoidalCategory.comp_tensor_id, assoc,
    MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id,
    ← ιTensorObj₃'_eq_assoc Y X Z i₂ i₁ i₃ k
      (by rw [add_comm i₂ i₁, h]) (i₁ + i₂) (add_comm i₂ i₁),
    ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_eq Y X Z i₂ i₁ i₃ k (by rw [add_comm i₂ i₁, h]) _ rfl, assoc,
    ι_tensorHom, categoryOfGradedObjects_id, ← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.id_tensorHom,
    ← MonoidalCategory.id_tensor_comp_assoc,
    ι_tensorObjDesc, MonoidalCategory.id_tensor_comp, assoc,
    ← MonoidalCategory.id_tensor_comp_assoc, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp, assoc,
    ← ιTensorObj₃_eq Y Z X i₂ i₃ i₁ k (by rw [add_comm _ i₁, ← add_assoc, h])
      (i₁ + i₃) (add_comm _ _)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GradedObject.Monoidal.hexagon_reverse** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：hexagon_reverse [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X] [HasTensor
 Z Y] [HasTensor X Z] [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)
] [HasTensor Z (tensorObj X Y)] [HasTensor (tensorObj Z X) Y] [HasTensor X (tens
orObj Z Y)] [HasTensor (tensorObj X Z) Y] [HasGoodTensor₁₂Tensor X Y Z] [HasGood
TensorTensor₂₃ X Y Z] [HasGoodTensor₁₂Tensor Z X Y] [HasGoodTensorTensor₂₃ Z X Y
] [HasGoodTensor₁₂Tensor X Z Y] [HasGoodTensorTensor₂₃ X Z Y] : (associator X Y 
Z).inv ≫ (braiding (tensor
参数：tensorObj X Y；tensorObj Y Z；tensorObj X Y；tensorObj Z X；tensorObj Z Y；tensorO
bj X Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorObj₃_ext`：tensorObj₃_ext {j :
 I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A) [H : HasGoodTensorTenso
r₂₃ X₁ X₂ X₃] (h : forall (i₁ i₂ i₃ : I) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc`：∀
 {I : Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_eq`：∀ {I : Type u} [in
st : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]
   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C]   [inst_2 : CategoryTheory.BraidedCate…
· 使用定理 `CategoryTheory.BraidedCategory.braiding_tensor_left_hom`：braiding_tensor
_left_hom (X Y Z : C) : (β_ (X otimes Y) Z).hom = (α_ X Y Z).hom ≫ X ◁ (β_ Y Z).
hom ≫ (α_ X Z Y).inv ≫ (β_ X Z).hom ▷ Y ≫ (α_…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_eq_assoc`：∀ {I : Type u
} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_
1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_associator_inv`：ιTensor
Obj₃_associator_inv [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X
₂ X₃] (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) : ιTens…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_eq`：ιTensorObj₃_eq (i₁ 
i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) : ιTensorObj₃
 X₁ X₂ X₃ i₁ i₂ i₃ j h = (X₁ i₁ ◁ ιTensor…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc`：∀ {I : Type u} [
inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc`：ι_tensorObjDesc {A
 : C} {k : I} (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A)
 (i₁ i₂ : I) (hi : i₁ + i₂ = k) : ιTensorO…
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_id`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (β : Type w) (X : (i : β) → (fun x => C
) i) (i : β),   CategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensor_comp`：id_tensor_comp (f : W ⟶ 
X) (g : X ⟶ Y) : 𝟙 Z otimesₘ f ≫ g = (𝟙 Z otimesₘ f) ≫ (𝟙 Z otimesₘ g)
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.comp_tensor_id_assoc`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory
 C] {W X Y Z : C}   (f : W ⟶ X) (g : X ⟶ Y…
· 使用定理 `CategoryTheory.MonoidalCategory.comp_tensor_id`：comp_tensor_id (f : W ⟶ 
X) (g : X ⟶ Y) : f ≫ g otimesₘ 𝟙 Z = (f otimesₘ 𝟙 Z) ≫ (g otimesₘ 𝟙 Z)
-/
lemma hexagon_reverse [HasTensor X Y] [HasTensor Y Z] [HasTensor Z X]
    [HasTensor Z Y] [HasTensor X Z]
    [HasTensor (tensorObj X Y) Z] [HasTensor X (tensorObj Y Z)]
    [HasTensor Z (tensorObj X Y)] [HasTensor (tensorObj Z X) Y]
    [HasTensor X (tensorObj Z Y)] [HasTensor (tensorObj X Z) Y]
    [HasGoodTensor₁₂Tensor X Y Z] [HasGoodTensorTensor₂₃ X Y Z]
    [HasGoodTensor₁₂Tensor Z X Y] [HasGoodTensorTensor₂₃ Z X Y]
    [HasGoodTensor₁₂Tensor X Z Y] [HasGoodTensorTensor₂₃ X Z Y] :
    (associator X Y Z).inv ≫ (braiding (tensorObj X Y) Z).hom ≫ (associator Z X Y).inv =
      whiskerLeft X (braiding Y Z).hom ≫ (associator X Z Y).inv ≫
        whiskerRight (braiding X Z).hom Y := by
  ext k i₁ i₂ i₃ h
  dsimp [braiding]
  conv_lhs => rw [ιTensorObj₃_associator_inv_assoc, ιTensorObj₃'_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc,
    ι_tensorObjDesc_assoc, assoc, ← MonoidalCategory.tensorHom_id,
    BraidedCategory.braiding_naturality_assoc,
    BraidedCategory.braiding_tensor_left_hom, assoc, assoc, assoc, assoc, Iso.inv_hom_id_assoc,
    MonoidalCategory.id_tensorHom,
    ← ιTensorObj₃_eq_assoc Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h]) _ rfl,
    ιTensorObj₃_associator_inv, Iso.hom_inv_id_assoc]
  conv_rhs => rw [ιTensorObj₃_eq X Y Z i₁ i₂ i₃ k h _ rfl, assoc, ι_tensorHom_assoc,
    ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp, ι_tensorObjDesc,
    categoryOfGradedObjects_id, MonoidalCategory.id_tensor_comp, assoc,
    MonoidalCategory.id_tensorHom, MonoidalCategory.id_tensorHom,
    ← ιTensorObj₃_eq_assoc X Z Y i₁ i₃ i₂ k
      (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) (i₂ + i₃) (add_comm _ _),
    ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq X Z Y i₁ i₃ i₂ k (by rw [add_assoc, add_comm i₃, ← add_assoc, h]) _ rfl,
    assoc, ι_tensorHom, categoryOfGradedObjects_id, ← MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_tensor_id_assoc,
    ι_tensorObjDesc, MonoidalCategory.comp_tensor_id, assoc,
    MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id,
    ← ιTensorObj₃'_eq Z X Y i₃ i₁ i₂ k (by rw [add_assoc, add_comm i₃, h])
      (i₁ + i₃) (add_comm _ _)]

end Braided

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.symmetry** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.GradedObject.Monoidal`。
形式化陈述：symmetry [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X] : (braiding
 X Y).hom ≫ (braiding Y X).hom = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorObj_ext`：tensorObj_ext {A : C
} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A) (h : forall (i₁ i₂ : I) (hi : i₁ + i₂ = 
j), ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorObjDesc`：ι_tensorObjDesc {A
 : C} {k : I} (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A)
 (i₁ i₂ : I) (hi : i₁ + i₂ = k) : ιTensorO…
· 使用定理 `CategoryTheory.SymmetricCategory.symmetry_assoc`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCategory C}  
 [self : CategoryTheory.SymmetricCate…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symmetry [SymmetricCategory C] [HasTensor X Y] [HasTensor Y X] :
    (braiding X Y).hom ≫ (braiding Y X).hom = 𝟙 _ := by
  dsimp [braiding]
  cat_disch

end Monoidal

section Instances

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C)
    ((MonoidalCategory.curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((MonoidalCategory.curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-
**CategoryTheory.GradedObject.braidedCategory** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.GradedObject`。
形式化陈述：braidedCategory [BraidedCategory C] : BraidedCategory (GradedObject I C) w
here braiding X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance braidedCategory [BraidedCategory C] :
    BraidedCategory (GradedObject I C) where
  braiding X Y := Monoidal.braiding X Y
  braiding_naturality_left _ _ := Monoidal.braiding_naturality_left _ _
  braiding_naturality_right _ _ _ _ := Monoidal.braiding_naturality_right _ _
  hexagon_forward _ _ _ := Monoidal.hexagon_forward _ _ _
  hexagon_reverse _ _ _ := Monoidal.hexagon_reverse _ _ _
/-
**CategoryTheory.GradedObject.symmetricCategory** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.GradedObject`。
形式化陈述：symmetricCategory [SymmetricCategory C] : SymmetricCategory (GradedObject 
I C) where symmetry _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance symmetricCategory [SymmetricCategory C] :
    SymmetricCategory (GradedObject I C) where
  symmetry _ _ := Monoidal.symmetry _ _

/-!
The braided/symmetric monoidal category structure on `GradedObject ℕ C` can
be inferred from the assumptions `[HasFiniteCoproducts C]`,
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).obj X)]` and
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)]`.
This requires importing `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`.
-/

end Instances

end GradedObject

end CategoryTheory

