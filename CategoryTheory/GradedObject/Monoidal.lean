/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.GradedObject.Unitor
public import Mathlib.Data.Fintype.Prod

/-!
# The monoidal category structures on graded objects

Assuming that `C` is a monoidal category and that `I` is an additive monoid,
we introduce a partially defined tensor product on the category `GradedObject I C`:
given `X₁` and `X₂` two objects in `GradedObject I C`, we define
`GradedObject.Monoidal.tensorObj X₁ X₂` under the assumption `HasTensor X₁ X₂`
that the coproduct of `X₁ i ⊗ X₂ j` for `i + j = n` exists for any `n : I`.

Under suitable assumptions about the existence of coproducts and the
preservation of certain coproducts by the tensor products in `C`, we
obtain a monoidal category structure on `GradedObject I C`.
In particular, if `C` has finite coproducts to which the tensor
product commutes, we obtain a monoidal category structure on `GradedObject ℕ C`.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits MonoidalCategory Category

variable {I : Type u} [AddMonoid I] {C : Type*} [Category* C] [MonoidalCategory C]

namespace GradedObject

/-- The tensor product of two graded objects `X₁` and `X₂` exists if for any `n`,
the coproduct of the objects `X₁ i ⊗ X₂ j` for `i + j = n` exists. -/
/-
**CategoryTheory.GradedObject.HasTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.GradedObject`。
形式化陈述：HasTensor (X₁ X₂ : GradedObject I C) : Prop
参数：X₁ X₂ : GradedObject I C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two graded objects `X₁` and `X₂` exists if for any `n`,
the coproduct of the objects `X₁ i ⊗ X₂ j` for `i + j = n` exists.
-/
abbrev HasTensor (X₁ X₂ : GradedObject I C) : Prop :=
  HasMap (((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂) (fun ⟨i, j⟩ => i + j)
/-
**CategoryTheory.GradedObject.hasTensor_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.GradedObject`。
形式化陈述：hasTensor_of_iso {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ 
≅ Y₂) [HasTensor X₁ X₂] : HasTensor Y₁ Y₂
参数：e₁ : X₁ ≅ Y₁；e₂ : X₂ ≅ Y₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hasMap_of_iso`：hasMap_of_iso (e : X ≅ Y) (p 
: I -> J) [HasMap X p] : HasMap Y p
-/
lemma hasTensor_of_iso {X₁ X₂ Y₁ Y₂ : GradedObject I C}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) [HasTensor X₁ X₂] :
    HasTensor Y₁ Y₂ := by
  let e : ((mapBifunctor (curriedTensor C) I I).obj X₁).obj X₂ ≅
    ((mapBifunctor (curriedTensor C) I I).obj Y₁).obj Y₂ := isoMk _ _
      (fun ⟨i, j⟩ ↦ (eval i).mapIso e₁ ⊗ᵢ (eval j).mapIso e₂)
  exact hasMap_of_iso e _

namespace Monoidal

/-- The tensor product of two graded objects. -/
/-
**CategoryTheory.GradedObject.Monoidal.tensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] : GradedObject I C
参数：X₁ X₂ : GradedObject I C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two graded objects.
-/
noncomputable abbrev tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] :
    GradedObject I C :=
  mapBifunctorMapObj (curriedTensor C) (fun ⟨i, j⟩ => i + j) X₁ X₂

section

variable (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂]

/-- The inclusion of a summand in a tensor product of two graded objects. -/
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a summand in a tensor product of two graded objects.
-/
noncomputable def ιTensorObj (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    X₁ i₁ ⊗ X₂ i₂ ⟶ tensorObj X₁ X₂ i₁₂ :=
  ιMapBifunctorMapObj (curriedTensor C) _ _ _ _ _ _ h

variable {X₁ X₂}

@[ext]
/-
**CategoryTheory.GradedObject.Monoidal.tensorObj_ext** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorObj_ext {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A) (h : forall (i
₁ i₂ : I) (hi : i₁ + i₂ = j), ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂
 i₁ i₂ j hi ≫ g) : f = g
参数：f g : tensorObj X₁ X₂ j ⟶ A；h : forall (i₁ i₂ : I) (hi : i₁ + i₂ = j), ιTenso
rObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.mapObj_ext`：mapObj_ext {A : C} {j : J} (f g 
: X.mapObj p j ⟶ A) (hfg : forall (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫
 f = X.ιMapObj p i j hij ≫ g…
-/
lemma tensorObj_ext {A : C} {j : I} (f g : tensorObj X₁ X₂ j ⟶ A)
    (h : ∀ (i₁ i₂ : I) (hi : i₁ + i₂ = j),
      ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ f = ιTensorObj X₁ X₂ i₁ i₂ j hi ≫ g) : f = g := by
  apply mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

/-- Constructor for morphisms from a tensor product of two graded objects. -/
/-
**CategoryTheory.GradedObject.Monoidal.tensorObjDesc** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorObjDesc {A : C} {k : I} (f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X
₁ i₁ otimes X₂ i₂ ⟶ A) : tensorObj X₁ X₂ k ⟶ A
参数：f : forall (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ otimes X₂ i₂ ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from a tensor product of two graded objects.
-/
noncomputable def tensorObjDesc {A : C} {k : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ ⊗ X₂ i₂ ⟶ A) : tensorObj X₁ X₂ k ⟶ A :=
  mapBifunctorMapObjDesc f

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_tensorObjDesc {A : C} {k : I}
    (f : ∀ (i₁ i₂ : I) (_ : i₁ + i₂ = k), X₁ i₁ ⊗ X₂ i₂ ⟶ A) (i₁ i₂ : I) (hi : i₁ + i₂ = k) :
    ιTensorObj X₁ X₂ i₁ i₂ k hi ≫ tensorObjDesc f = f i₁ i₂ hi := by
  apply ι_mapBifunctorMapObjDesc

end

/-- The morphism `tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂` induced by morphisms of graded
objects `f : X₁ ⟶ X₂` and `g : Y₁ ⟶ Y₂`. -/
/-
**CategoryTheory.GradedObject.Monoidal.tensorHom** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GradedObject.Monoidal`。
形式化陈述：tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [Ha
sTensor X₁ Y₁] [HasTensor X₂ Y₂] : tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂` induced by morphisms of graded
objects `f : X₁ ⟶ X₂` and `g : Y₁ ⟶ Y₂`.
-/
noncomputable def tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ⟶ tensorObj X₂ Y₂ :=
  mapBifunctorMapMap _ _ f g

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_tensorHom {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = i₁₂) :
    ιTensorObj X₁ Y₁ i₁ i₂ i₁₂ h ≫ tensorHom f g i₁₂ =
      (f i₁ ⊗ₘ g i₂) ≫ ιTensorObj X₂ Y₂ i₁ i₂ i₁₂ h := by
  rw [tensorHom_def, assoc]
  apply ι_mapBifunctorMapMap

/-- The morphism `tensorObj X Y₁ ⟶ tensorObj X Y₂` induced by a morphism of graded objects
`φ : Y₁ ⟶ Y₂`. -/
/-
**CategoryTheory.GradedObject.Monoidal.whiskerLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.GradedObject.Monoidal`。
形式化陈述：whiskerLeft (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂
) [HasTensor X Y₁] [HasTensor X Y₂] : tensorObj X Y₁ ⟶ tensorObj X Y₂
参数：X : GradedObject I C；φ : Y₁ ⟶ Y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `tensorObj X Y₁ ⟶ tensorObj X Y₂` induced by a morphism of graded o
bjects
`φ : Y₁ ⟶ Y₂`.
-/
noncomputable abbrev whiskerLeft (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂)
    [HasTensor X Y₁] [HasTensor X Y₂] : tensorObj X Y₁ ⟶ tensorObj X Y₂ :=
  tensorHom (𝟙 X) φ

/-- The morphism `tensorObj X₁ Y ⟶ tensorObj X₂ Y` induced by a morphism of graded objects
`φ : X₁ ⟶ X₂`. -/
/-
**CategoryTheory.GradedObject.Monoidal.whiskerRight** 是 Mathlib 中的一个缩写定义，位于命名空间 
`CategoryTheory.GradedObject.Monoidal`。
形式化陈述：whiskerRight {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I 
C) [HasTensor X₁ Y] [HasTensor X₂ Y] : tensorObj X₁ Y ⟶ tensorObj X₂ Y
参数：φ : X₁ ⟶ X₂；Y : GradedObject I C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `tensorObj X₁ Y ⟶ tensorObj X₂ Y` induced by a morphism of graded o
bjects
`φ : X₁ ⟶ X₂`.
-/
noncomputable abbrev whiskerRight {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C)
    [HasTensor X₁ Y] [HasTensor X₂ Y] : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom φ (𝟙 Y)

@[simp]
/-
**CategoryTheory.GradedObject.Monoidal.id_tensorHom_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：id_tensorHom_id (X Y : GradedObject I C) [HasTensor X Y] : tensorHom (𝟙 X)
 (𝟙 Y) = 𝟙 _
参数：X Y : GradedObject I C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.GradedObject.mapMap_id`：mapMap_id : mapMap (𝟙 X) p = 𝟙 _
-/
lemma id_tensorHom_id (X Y : GradedObject I C) [HasTensor X Y] :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 _ := by
  dsimp [tensorHom, mapBifunctorMapMap]
  simp only [Functor.map_id, NatTrans.id_app, comp_id, mapMap_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.GradedObject.Monoidal.tensorHom_comp_tensorHom** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorHom_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶
 X₂) (f₂ : X₂ ⟶ X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁] [HasTensor X
₂ Y₂] [HasTensor X₃ Y₃] : tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ = tensorHom (f₁ ≫ f₂
) (g₁ ≫ g₂)
参数：f₁ : X₁ ⟶ X₂；f₂ : X₂ ⟶ X₃；g₁ : Y₁ ⟶ Y₂；g₂ : Y₂ ⟶ Y₃。
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
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc`：∀ {C : T
ype u} {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCat
egory C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorHom_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₃ Y₃] :
    tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ = tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) := by
  ext
  simp

/-- The isomorphism `tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂` induced by isomorphisms of graded
objects `e : X₁ ≅ X₂` and `e' : Y₁ ≅ Y₂`. -/
@[simps]
/-
**CategoryTheory.GradedObject.Monoidal.tensorIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GradedObject.Monoidal`。
形式化陈述：tensorIso {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂) [H
asTensor X₁ Y₁] [HasTensor X₂ Y₂] : tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂ where hom
参数：e : X₁ ≅ X₂；e' : Y₁ ≅ Y₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂` induced by isomorphisms of g
raded
objects `e : X₁ ≅ X₂` and `e' : Y₁ ≅ Y₂`.
-/
noncomputable def tensorIso {X₁ X₂ Y₁ Y₂ : GradedObject I C} (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] :
    tensorObj X₁ Y₁ ≅ tensorObj X₂ Y₂ where
  hom := tensorHom e.hom e'.hom
  inv := tensorHom e.inv e'.inv
  hom_inv_id := by simp [tensorHom_comp_tensorHom]
  inv_hom_id := by simp [tensorHom_comp_tensorHom]
/-
**CategoryTheory.GradedObject.Monoidal.tensorHom_def** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorHom_def {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
 [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₂ Y₁] : tensorHom f g = whisker
Right f Y₁ ≫ whiskerLeft X₂ g
参数：f : X₁ ⟶ X₂；g : Y₁ ⟶ Y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorHom_comp_tensorHom`：tensorHom
_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶
 X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma tensorHom_def {X₁ X₂ Y₁ Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂)
    [HasTensor X₁ Y₁] [HasTensor X₂ Y₂] [HasTensor X₂ Y₁] :
    tensorHom f g = whiskerRight f Y₁ ≫ whiskerLeft X₂ g := by
  rw [tensorHom_comp_tensorHom, id_comp, comp_id]

/-- This is the addition map `I × I × I → I` for an additive monoid `I`. -/
/-
**CategoryTheory.GradedObject.Monoidal.r** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the addition map `I × I × I → I` for an additive monoid `I`.
-/
def r₁₂₃ : I × I × I → I := fun ⟨i, j, k⟩ => i + j + k

/-- Auxiliary definition for `associator`. -/
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `associator`.
-/
@[reducible] def ρ₁₂ : BifunctorComp₁₂IndexData (r₁₂₃ : _ → I) where
  I₁₂ := I
  p := fun ⟨i₁, i₂⟩ => i₁ + i₂
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq := fun _ => rfl

/-- Auxiliary definition for `associator`. -/
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `associator`.
-/
@[reducible] def ρ₂₃ : BifunctorComp₂₃IndexData (r₁₂₃ : _ → I) where
  I₂₃ := I
  p := fun ⟨i₂, i₃⟩ => i₂ + i₃
  q := fun ⟨i₁₂, i₃⟩ => i₁₂ + i₃
  hpq _ := (add_assoc _ _ _).symm

variable (I) in
/-- Auxiliary definition for `associator`. -/
@[reducible]
/-
**CategoryTheory.GradedObject.Monoidal.triangleIndexData** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：triangleIndexData : TriangleIndexData (r₁₂₃ : _ -> I) (fun ⟨i₁, i₃⟩ => i₁ 
+ i₃) where p₁₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `associator`.
-/
def triangleIndexData : TriangleIndexData (r₁₂₃ : _ → I) (fun ⟨i₁, i₃⟩ => i₁ + i₃) where
  p₁₂ := fun ⟨i₁, i₂⟩ => i₁ + i₂
  p₂₃ := fun ⟨i₂, i₃⟩ => i₂ + i₃
  hp₁₂ := fun _ => rfl
  hp₂₃ := fun _ => (add_assoc _ _ _).symm
  h₁ := add_zero
  h₃ := zero_add

/-- Given three graded objects `X₁`, `X₂`, `X₃` in `GradedObject I C`, this is the
assumption that for all `i₁₂ : I` and `i₃ : I`, the tensor product functor `- ⊗ X₃ i₃`
commutes with the coproduct of the objects `X₁ i₁ ⊗ X₂ i₂` such that `i₁ + i₂ = i₁₂`. -/
/-
**CategoryTheory.GradedObject.Monoidal._root_.CategoryTheory.GradedObject.HasGoo
dTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three graded objects `X₁`, `X₂`, `X₃` in `GradedObject I C`, this is the
assumption that for all `i₁₂ : I` and `i₃ : I`, the tensor product functor `- ⊗ 
X₃ i₃`
commutes with the coproduct of the objects `X₁ i₁ ⊗ X₂ i₂` such that `i₁ + i₂ = 
i₁₂`.
-/
abbrev _root_.CategoryTheory.GradedObject.HasGoodTensor₁₂Tensor (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₁₂Obj (curriedTensor C) (curriedTensor C) ρ₁₂ X₁ X₂ X₃

/-- Given three graded objects `X₁`, `X₂`, `X₃` in `GradedObject I C`, this is the
assumption that for all `i₁ : I` and `i₂₃ : I`, the tensor product functor `X₁ i₁ ⊗ -`
commutes with the coproduct of the objects `X₂ i₂ ⊗ X₃ i₃` such that `i₂ + i₃ = i₂₃`. -/
/-
**CategoryTheory.GradedObject.Monoidal._root_.CategoryTheory.GradedObject.HasGoo
dTensorTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.GradedObject.Monoidal`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given three graded objects `X₁`, `X₂`, `X₃` in `GradedObject I C`, this is the
assumption that for all `i₁ : I` and `i₂₃ : I`, the tensor product functor `X₁ i
₁ ⊗ -`
commutes with the coproduct of the objects `X₂ i₂ ⊗ X₃ i₃` such that `i₂ + i₃ = 
i₂₃`.
-/
abbrev _root_.CategoryTheory.GradedObject.HasGoodTensorTensor₂₃ (X₁ X₂ X₃ : GradedObject I C) :=
  HasGoodTrifunctor₂₃Obj (curriedTensor C) (curriedTensor C) ρ₂₃ X₁ X₂ X₃

section

variable (Z : C) (X₁ X₂ X₃ : GradedObject I C)
  {Y₁ Y₂ Y₃ : GradedObject I C}

section
variable [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)]

/-- The inclusion `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j`
when `i₁ + i₂ + i₃ = j`. -/
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j`
when `i₁ + i₂ + i₃ = j`.
-/
noncomputable def ιTensorObj₃ (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj X₁ (tensorObj X₂ X₃) j :=
  X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ _ rfl ≫ ιTensorObj X₁ (tensorObj X₂ X₃) i₁ (i₂ + i₃) j
    (by rw [← add_assoc, h])

@[reassoc]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₃_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (X₁ i₁ ◁ ιTensorObj X₂ X₃ i₂ i₃ i₂₃ h') ≫
        ιTensorObj X₁ (tensorObj X₂ X₃) i₁ i₂₃ j (by rw [← h', ← add_assoc, h]) := by
  subst h'
  rfl

variable {X₁ X₂ X₃}

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₃_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom f₁ (tensorHom f₂ f₃) j =
      (f₁ i₁ ⊗ₘ f₂ i₂ ⊗ₘ f₃ i₃) ≫ ιTensorObj₃ Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl,
    ιTensorObj₃_eq _ _ _ i₁ i₂ i₃ j h _ rfl, assoc, ι_tensorHom,
    ← id_tensorHom, ← id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc, ι_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp, comp_id]

@[ext (iff := false)]
/-
**CategoryTheory.GradedObject.Monoidal.tensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] : GradedObject I C
参数：X₁ X₂ : GradedObject I C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj₃_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (hi : i₁ + i₂ + i₃ = j),
      ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ f = ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j hi ≫ g) :
      f = g := by
  apply mapBifunctorBifunctor₂₃MapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

end

section
variable [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor Y₁ Y₂]
  [HasTensor (tensorObj Y₁ Y₂) Y₃]

/-- The inclusion `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j`
when `i₁ + i₂ + i₃ = j`. -/
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j`
when `i₁ + i₂ + i₃ = j`.
-/
noncomputable def ιTensorObj₃' (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    (X₁ i₁ ⊗ X₂ i₂) ⊗ X₃ i₃ ⟶ tensorObj (tensorObj X₁ X₂) X₃ j :=
  (ιTensorObj X₁ X₂ i₁ i₂ (i₁ + i₂) rfl ▷ X₃ i₃) ≫
    ιTensorObj (tensorObj X₁ X₂) X₃ (i₁ + i₂) i₃ j h

@[reassoc]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₃'_eq (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₁₂ : I)
    (h' : i₁ + i₂ = i₁₂) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h =
      (ιTensorObj X₁ X₂ i₁ i₂ i₁₂ h' ▷ X₃ i₃) ≫
        ιTensorObj (tensorObj X₁ X₂) X₃ i₁₂ i₃ j (by rw [← h', h]) := by
  subst h'
  rfl

variable {X₁ X₂ X₃}

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₃'_tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ tensorHom (tensorHom f₁ f₂) f₃ j =
      ((f₁ i₁ ⊗ₘ f₂ i₂) ⊗ₘ f₃ i₃) ≫ ιTensorObj₃' Y₁ Y₂ Y₃ i₁ i₂ i₃ j h := by
  rw [ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl,
    ιTensorObj₃'_eq _ _ _ i₁ i₂ i₃ j h _ rfl, assoc, ι_tensorHom,
    ← tensorHom_id, ← tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc, id_comp,
    ι_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc, comp_id]

@[ext (iff := false)]
/-
**CategoryTheory.GradedObject.Monoidal.tensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] : GradedObject I C
参数：X₁ X₂ : GradedObject I C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj₃'_ext {j : I} {A : C} (f g : tensorObj (tensorObj X₁ X₂) X₃ j ⟶ A)
    [H : HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ f = ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ g) :
      f = g := by
  apply mapBifunctor₁₂BifunctorMapObj_ext (H := H)
  intro i₁ i₂ i₃ hi
  exact h i₁ i₂ i₃ hi

end

section
variable [HasTensor X₁ X₂] [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₂ X₃]
  [HasTensor X₁ (tensorObj X₂ X₃)]

/-- The associator isomorphism for graded objects. -/
/-
**CategoryTheory.GradedObject.Monoidal.associator** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GradedObject.Monoidal`。
形式化陈述：associator [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X
₃] : tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator isomorphism for graded objects.
-/
noncomputable def associator [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃] :
    tensorObj (tensorObj X₁ X₂) X₃ ≅ tensorObj X₁ (tensorObj X₂ X₃) :=
  mapBifunctorAssociator (MonoidalCategory.curriedAssociatorNatIso C) ρ₁₂ ρ₂₃ X₁ X₂ X₃

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₃'_associator_hom
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).hom j =
      (α_ _ _ _).hom ≫ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorAssociator_hom (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₃_associator_inv
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) :
    ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h ≫ (associator X₁ X₂ X₃).inv j =
      (α_ _ _ _).inv ≫ ιTensorObj₃' X₁ X₂ X₃ i₁ i₂ i₃ j h :=
  ι_mapBifunctorAssociator_inv (MonoidalCategory.curriedAssociatorNatIso C)
    ρ₁₂ ρ₂₃ X₁ X₂ X₃ i₁ i₂ i₃ j h

variable {X₁ X₂ X₃}

set_option backward.isDefEq.respectTransparency.types false in
variable [HasTensor Y₁ Y₂] [HasTensor (tensorObj Y₁ Y₂) Y₃] [HasTensor Y₂ Y₃]
  [HasTensor Y₁ (tensorObj Y₂ Y₃)] in
/-
**CategoryTheory.GradedObject.Monoidal.associator_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) [HasGoo
dTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃] [HasGoodTensor₁₂Tenso
r Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] : tensorHom (tensorHom f₁ f₂) f₃ ≫ 
(associator Y₁ Y₂ Y₃).hom = (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom 
f₂ f₃)
参数：f₁ : X₁ ⟶ Y₁；f₂ : X₂ ⟶ Y₂；f₃ : X₃ ⟶ Y₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.GradedObject.Monoidal.tensorObj₃'_ext`：∀ {I : Type u} [in
st : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]
   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_tensorHom_assoc`：∀ {I 
: Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.
{v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_conjugation`：associator_conju
gation {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') : (f otimesₘ 
g) otimesₘ h = (α_ X Y Z).hom ≫ (f otimesₘ g…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_associator_hom`：∀ {I :
 Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{
v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_associator_hom_assoc`：
∀ {I : Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Cate
gory.{v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_tensorHom`：ιTensorObj₃_
tensorHom (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (i₁ i₂ i₃ j : I) (h : i₁ 
+ i₂ + i₃ = j) : ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma associator_naturality (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃)
    [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasGoodTensor₁₂Tensor Y₁ Y₂ Y₃] [HasGoodTensorTensor₂₃ Y₁ Y₂ Y₃] :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
        cat_disch

end

/-- Given `Z : C` and three graded objects `X₁`, `X₂` and `X₃` in `GradedObject I C`,
this typeclass expresses that functor `Z ⊗ _` commutes with the coproduct of
the objects `X₁ i₁ ⊗ (X₂ i₂ ⊗ X₃ i₃)` such that `i₁ + i₂ + i₃ = j` for a certain `j`.
See lemma `left_tensor_tensorObj₃_ext`. -/
/-
**CategoryTheory.GradedObject.Monoidal._root_.CategoryTheory.GradedObject.HasLef
tTensor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Z : C` and three graded objects `X₁`, `X₂` and `X₃` in `GradedObject I C`
,
this typeclass expresses that functor `Z ⊗ _` commutes with the coproduct of
the objects `X₁ i₁ ⊗ (X₂ i₂ ⊗ X₃ i₃)` such that `i₁ + i₂ + i₃ = j` for a certain
 `j`.
See lemma `left_tensor_tensorObj₃_ext`.
-/
abbrev _root_.CategoryTheory.GradedObject.HasLeftTensor₃ObjExt (j : I) := PreservesColimit
  (Discrete.functor fun (i : { i : (I × I × I) | i.1 + i.2.1 + i.2.2 = j }) ↦
    (((mapTrifunctor (bifunctorComp₂₃ (curriedTensor C)
      (curriedTensor C)) I I I).obj X₁).obj X₂).obj X₃ i)
    ((curriedTensor C).obj Z)

variable {X₁ X₂ X₃}
variable [HasTensor X₂ X₃] [HasTensor X₁ (tensorObj X₂ X₃)]

@[ext (iff := false)]
/-
**CategoryTheory.GradedObject.Monoidal.left_tensor_tensorObj** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma left_tensor_tensorObj₃_ext {j : I} {A : C} (Z : C)
    (f g : Z ⊗ tensorObj X₁ (tensorObj X₂ X₃) j ⟶ A)
    [H : HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [hZ : HasLeftTensor₃ObjExt Z X₁ X₂ X₃ j]
    (h : ∀ (i₁ i₂ i₃ : I) (h : i₁ + i₂ + i₃ = j),
      (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ f =
        (_ ◁ ιTensorObj₃ X₁ X₂ X₃ i₁ i₂ i₃ j h) ≫ g) : f = g := by
    refine (@isColimitOfPreserves C _ C _ _ _ _ ((curriedTensor C).obj Z) _
      (isColimitCofan₃MapBifunctorBifunctor₂₃MapObj (H := H) (j := j)) hZ).hom_ext ?_
    intro ⟨⟨i₁, i₂, i₃⟩, hi⟩
    exact h _ _ _ hi

end

section

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₃ X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]

/-- The inclusion
`X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j`
when `i₁ + i₂ + i₃ + i₄ = j`. -/
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion
`X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j
`
when `i₁ + i₂ + i₃ + i₄ = j`.
-/
noncomputable def ιTensorObj₄ (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) :
    X₁ i₁ ⊗ X₂ i₂ ⊗ X₃ i₃ ⊗ X₄ i₄ ⟶ tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j :=
  (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ rfl) ≫
    ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ (i₂ + i₃ + i₄) j
      (by rw [← h, ← add_assoc, ← add_assoc])
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιTensorObj₄_eq (i₁ i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I)
    (hi : i₂ + i₃ + i₄ = i₂₃₄) :
    ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h =
      (_ ◁ ιTensorObj₃ X₂ X₃ X₄ i₂ i₃ i₄ _ hi) ≫
        ιTensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) i₁ i₂₃₄ j
          (by rw [← hi, ← add_assoc, ← add_assoc, h]) := by
  subst hi
  rfl

/-- Given four graded objects, this is the condition
`HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄` for all indices `i₁` and `i₂₃₄`,
see the lemma `tensorObj₄_ext`. -/
/-
**CategoryTheory.GradedObject.Monoidal._root_.CategoryTheory.GradedObject.HasTen
sor** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given four graded objects, this is the condition
`HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄` for all indices `i₁` and `i₂₃₄`,
see the lemma `tensorObj₄_ext`.
-/
abbrev _root_.CategoryTheory.GradedObject.HasTensor₄ObjExt :=
  ∀ (i₁ i₂₃₄ : I), HasLeftTensor₃ObjExt (X₁ i₁) X₂ X₃ X₄ i₂₃₄

variable {X₁ X₂ X₃ X₄}

@[ext (iff := false)]
/-
**CategoryTheory.GradedObject.Monoidal.tensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorObj (X₁ X₂ : GradedObject I C) [HasTensor X₁ X₂] : GradedObject I C
参数：X₁ X₂ : GradedObject I C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj₄_ext {j : I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j ⟶ A)
    [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
    [H : HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (h : ∀ (i₁ i₂ i₃ i₄ : I) (h : i₁ + i₂ + i₃ + i₄ = j),
      ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h ≫ f =
        ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h ≫ g) : f = g := by
  apply tensorObj_ext
  intro i₁ i₂₃₄ h'
  apply left_tensor_tensorObj₃_ext
  intro i₂ i₃ i₄ h''
  have hj : i₁ + i₂ + i₃ + i₄ = j := by simp only [← h', ← h'', add_assoc]
  simpa only [assoc, ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j hj i₂₃₄ h''] using h i₁ i₂ i₃ i₄ hj

end

section Pentagon

variable (X₁ X₂ X₃ X₄ : GradedObject I C)
  [HasTensor X₁ X₂] [HasTensor X₂ X₃] [HasTensor X₃ X₄]
  [HasTensor (tensorObj X₁ X₂) X₃] [HasTensor X₁ (tensorObj X₂ X₃)]
  [HasTensor (tensorObj X₂ X₃) X₄] [HasTensor X₂ (tensorObj X₃ X₄)]
  [HasTensor (tensorObj (tensorObj X₁ X₂) X₃) X₄]
  [HasTensor (tensorObj X₁ (tensorObj X₂ X₃)) X₄]
  [HasTensor X₁ (tensorObj (tensorObj X₂ X₃) X₄)]
  [HasTensor X₁ (tensorObj X₂ (tensorObj X₃ X₄))]
  [HasTensor (tensorObj X₁ X₂) (tensorObj X₃ X₄)]
  [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasGoodTensor₁₂Tensor X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensorTensor₂₃ X₁ (tensorObj X₂ X₃) X₄]
  [HasGoodTensor₁₂Tensor X₂ X₃ X₄] [HasGoodTensorTensor₂₃ X₂ X₃ X₄]
  [HasGoodTensor₁₂Tensor (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensorTensor₂₃ (tensorObj X₁ X₂) X₃ X₄]
  [HasGoodTensor₁₂Tensor X₁ X₂ (tensorObj X₃ X₄)]
  [HasGoodTensorTensor₂₃ X₁ X₂ (tensorObj X₃ X₄)]
  [HasTensor₄ObjExt X₁ X₂ X₃ X₄]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.GradedObject.Monoidal.pentagon_inv** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GradedObject.Monoidal`。
形式化陈述：pentagon_inv : tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).inv ≫ (associator X₁
 (tensorObj X₂ X₃) X₄).inv ≫ tensorHom (associator X₁ X₂ X₃).inv (𝟙 X₄) = (assoc
iator X₁ X₂ (tensorObj X₃ X₄)).inv ≫ (associator (tensorObj X₁ X₂) X₃ X₄).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorObj₄_ext`：tensorObj₄_ext {j :
 I} {A : C} (f g : tensorObj X₁ (tensorObj X₂ (tensorObj X₃ X₄)) j ⟶ A) [HasGood
TensorTensor₂₃ X₂ X₃ X₄] [H : HasTensor₄O…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₄_eq`：ιTensorObj₄_eq (i₁ 
i₂ i₃ i₄ j : I) (h : i₁ + i₂ + i₃ + i₄ = j) (i₂₃₄ : I) (hi : i₂ + i₃ + i₄ = i₂₃₄
) : ιTensorObj₄ X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom_assoc`：∀ {I : Type u} [
inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} 
C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerLeft_comp_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] (W : C)   {X Y Z : C} (f : X ⟶ Y) (g :…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_associator_inv`：ιTensor
Obj₃_associator_inv [HasGoodTensor₁₂Tensor X₁ X₂ X₃] [HasGoodTensorTensor₂₃ X₁ X
₂ X₃] (i₁ i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) : ιTens…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_eq`：∀ {I : Type u} [in
st : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]
   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_eq_assoc`：∀ {I : Type u
} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_
1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc`：∀
 {I : Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Categ
ory.{v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃'_eq_assoc`：∀ {I : Type 
u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u
_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ι_tensorHom`：ι_tensorHom {X₁ X₂ Y₁ 
Y₂ : GradedObject I C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [HasTensor X₁ Y₁] [HasTensor 
X₂ Y₂] (i₁ i₂ i₁₂ : I) (h : i₁ + i₂ = …
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_assoc_symm_assoc`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCate
gory C] (X : C) {Y Y' : C}   (f : Y ⟶ Y') (Z :…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.MonoidalCategory.comp_whiskerRight_assoc`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {W X Y : C}   (f : W ⟶ X) (g : X ⟶ Y) …
· 使用引理 `CategoryTheory.GradedObject.Monoidal.ιTensorObj₃_eq`：ιTensorObj₃_eq (i₁ 
i₂ i₃ j : I) (h : i₁ + i₂ + i₃ = j) (i₂₃ : I) (h' : i₂ + i₃ = i₂₃) : ιTensorObj₃
 X₁ X₂ X₃ i₁ i₂ i₃ j h = (X₁ i₁ ◁ ιTensor…
· 使用定理 `CategoryTheory.MonoidalCategory.pentagon_inv_assoc`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C
] {W X Y Z Z_1 : C}   (h :     CategoryT…
· 使用定理 `CategoryTheory.MonoidalCategory.associator_inv_naturality_right_assoc`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory
.MonoidalCategory C] (X Y : C)   {Z Z' : C} (f : Z ⟶ Z') {Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whisker_exchange_assoc`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {W X Y Z : C}   (f : W ⟶ X) (g : Y ⟶ Z…
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_tensor_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {X X' : C}   (f : X ⟶ X') (Y Z : C) {Z…
-/
lemma pentagon_inv :
    tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).inv ≫ (associator X₁ (tensorObj X₂ X₃) X₄).inv ≫
        tensorHom (associator X₁ X₂ X₃).inv (𝟙 X₄) =
    (associator X₁ X₂ (tensorObj X₃ X₄)).inv ≫ (associator (tensorObj X₁ X₂) X₃ X₄).inv := by
  ext j i₁ i₂ i₃ i₄ h
  dsimp only [categoryOfGradedObjects_comp]
  conv_lhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ j h _ rfl, assoc, ι_tensorHom_assoc]
    dsimp only [categoryOfGradedObjects_id, id_eq, eq_mpr_eq_cast, cast_eq]
    rw [id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc, ιTensorObj₃_associator_inv,
      ιTensorObj₃'_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, MonoidalCategory.whiskerLeft_comp_assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) _ rfl, ιTensorObj₃_associator_inv_assoc,
      ιTensorObj₃'_eq_assoc X₁ (tensorObj X₂ X₃) X₄ i₁ (i₂ + i₃) i₄ j
        (by simp only [← add_assoc, h]) (i₁ + i₂ + i₃) (by rw [add_assoc]), ι_tensorHom]
    dsimp only [id_eq, eq_mpr_eq_cast, categoryOfGradedObjects_id]
    rw [tensorHom_id, whisker_assoc_symm_assoc, Iso.hom_inv_id_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl, ιTensorObj₃_associator_inv,
      MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.pentagon_inv_assoc]
  conv_rhs =>
    rw [ιTensorObj₄_eq X₁ X₂ X₃ X₄ i₁ i₂ i₃ i₄ _ _ _ rfl,
      ιTensorObj₃_eq X₂ X₃ X₄ i₂ i₃ i₄ _ rfl _ rfl, assoc,
      MonoidalCategory.whiskerLeft_comp_assoc,
      ← ιTensorObj₃_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) (i₂ + i₃ + i₄) (by rw [add_assoc]),
      ιTensorObj₃_associator_inv_assoc, associator_inv_naturality_right_assoc,
      ιTensorObj₃'_eq_assoc X₁ X₂ (tensorObj X₃ X₄) i₁ i₂ (i₃ + i₄) j
        (by rw [← add_assoc, h]) _ rfl, whisker_exchange_assoc,
      ← ιTensorObj₃_eq_assoc (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ιTensorObj₃_associator_inv, whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
      ιTensorObj₃'_eq (tensorObj X₁ X₂) X₃ X₄ (i₁ + i₂) i₃ i₄ j h _ rfl,
      ← MonoidalCategory.comp_whiskerRight_assoc,
      ← ιTensorObj₃'_eq X₁ X₂ X₃ i₁ i₂ i₃ _ rfl _ rfl]
/-
**CategoryTheory.GradedObject.Monoidal.pentagon** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.GradedObject.Monoidal`。
形式化陈述：pentagon : tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫ (associator X₁ (te
nsorObj X₂ X₃) X₄).hom ≫ tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom = (associato
r (tensorObj X₁ X₂) X₃ X₄).hom ≫ (associator X₁ X₂ (tensorObj X₃ X₄)).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.GradedObject.Monoidal.pentagon_inv_assoc`：∀ {I : Type u} 
[inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.GradedObject.Monoidal.tensorHom_comp_tensorHom_assoc`：∀ {
I : Type u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Categor
y.{v_1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.id_tensorHom_id`：id_tensorHom_id (X
 Y : GradedObject I C) [HasTensor X Y] : tensorHom (𝟙 X) (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.GradedObject.Monoidal.tensorHom_comp_tensorHom`：tensorHom
_comp_tensorHom {X₁ X₂ X₃ Y₁ Y₂ Y₃ : GradedObject I C} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶
 X₃) (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) [HasTensor X₁ Y₁…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pentagon : tensorHom (associator X₁ X₂ X₃).hom (𝟙 X₄) ≫
    (associator X₁ (tensorObj X₂ X₃) X₄).hom ≫ tensorHom (𝟙 X₁) (associator X₂ X₃ X₄).hom =
    (associator (tensorObj X₁ X₂) X₃ X₄).hom ≫ (associator X₁ X₂ (tensorObj X₃ X₄)).hom := by
  rw [← cancel_epi (associator (tensorObj X₁ X₂) X₃ X₄).inv,
    ← cancel_epi (associator X₁ X₂ (tensorObj X₃ X₄)).inv, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, ← pentagon_inv_assoc]
  simp [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc]

end Pentagon

section TensorUnit

variable [DecidableEq I] [HasInitial C]

/-- The unit of the tensor product on graded objects is `(single₀ I).obj (𝟙_ C)`. -/
/-
**CategoryTheory.GradedObject.Monoidal.tensorUnit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorUnit : GradedObject I C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit of the tensor product on graded objects is `(single₀ I).obj (𝟙_ C)`.
-/
noncomputable def tensorUnit : GradedObject I C := (single₀ I).obj (𝟙_ C)

/-- The canonical isomorphism `tensorUnit 0 ≅ 𝟙_ C` -/
/-
**CategoryTheory.GradedObject.Monoidal.tensorUnit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GradedObject.Monoidal`。
形式化陈述：tensorUnit : GradedObject I C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `tensorUnit 0 ≅ 𝟙_ C`
-/
noncomputable def tensorUnit₀ : (tensorUnit : GradedObject I C) 0 ≅ 𝟙_ C :=
  singleObjApplyIso (0 : I) (𝟙_ C)

/-- `tensorUnit i` is an initial object when `i ≠ 0`. -/
/-
**CategoryTheory.GradedObject.Monoidal.isInitialTensorUnitApply** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：isInitialTensorUnitApply (i : I) (hi : i != 0) : IsInitial ((tensorUnit : 
GradedObject I C) i)
参数：i : I；hi : i != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`tensorUnit i` is an initial object when `i ≠ 0`.
-/
noncomputable def isInitialTensorUnitApply (i : I) (hi : i ≠ 0) :
    IsInitial ((tensorUnit : GradedObject I C) i) :=
  isInitialSingleObjApply _ _ _ hi

end TensorUnit

section LeftUnitor

variable [DecidableEq I] [HasInitial C]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  (X X' : GradedObject I C)

/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTensor tensorUnit X :=
  mapBifunctorLeftUnitor_hasMap _ _ (leftUnitorNatIso C) _ zero_add _
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj
    ((single₀ I).obj (𝟙_ C))).obj X) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
  inferInstanceAs <| HasTensor tensorUnit X

/-- The left unitor isomorphism for graded objects. -/
/-
**CategoryTheory.GradedObject.Monoidal.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.GradedObject.Monoidal`。
形式化陈述：leftUnitor : tensorObj tensorUnit X ≅ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasMapProdObjFunctorMapBifuncto
rCurriedTensorSingle₀TensorUnit`：∀ {I : Type u} [inst : AddMonoid I] {C : Type u
_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]   [inst_2 : CategoryTheory.M
onoidalCatego…

--- 原说明 ---
The left unitor isomorphism for graded objects.
-/
noncomputable def leftUnitor : tensorObj tensorUnit X ≅ X :=
    mapBifunctorLeftUnitor (curriedTensor C) (𝟙_ C)
      (leftUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) zero_add X
/-
**CategoryTheory.GradedObject.Monoidal.leftUnitor_inv_apply** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：leftUnitor_inv_apply (i : I) : (leftUnitor X).inv i = (fun_ (X i)).inv ≫ t
ensorUnit₀.inv ▷ (X i) ≫ ιTensorObj tensorUnit X 0 i i (zero_add i)
参数：i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit`：∀ {I : Typ
e u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
-/
lemma leftUnitor_inv_apply (i : I) :
    (leftUnitor X).inv i = (λ_ (X i)).inv ≫ tensorUnit₀.inv ▷ (X i) ≫
      ιTensorObj tensorUnit X 0 i i (zero_add i) := rfl

variable {X X'}

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.leftUnitor_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：leftUnitor_naturality (φ : X ⟶ X') : tensorHom (𝟙 (tensorUnit)) φ ≫ (leftU
nitor X').hom = (leftUnitor X).hom ≫ φ
参数：φ : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorLeftUnitor_naturality`：mapBifunc
torLeftUnitor_naturality : mapBifunctorMapMap F p (𝟙 _) φ ≫ (mapBifunctorLeftUni
tor F X e p hp Y').hom = (mapBifunctorLeftUnitor F …
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit`：∀ {I : Typ
e u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
-/
lemma leftUnitor_naturality (φ : X ⟶ X') :
    tensorHom (𝟙 (tensorUnit)) φ ≫ (leftUnitor X').hom =
      (leftUnitor X).hom ≫ φ := by
  apply mapBifunctorLeftUnitor_naturality

end LeftUnitor

section RightUnitor

variable [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  (X X' : GradedObject I C)

/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTensor X tensorUnit :=
  mapBifunctorRightUnitor_hasMap (curriedTensor C) _
    (rightUnitorNatIso C) _ add_zero _
/-
**CategoryTheory.GradedObject.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.GradedObject.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasMap (((mapBifunctor (curriedTensor C) I I).obj X).obj
    ((single₀ I).obj (𝟙_ C))) (fun ⟨i₁, i₂⟩ => i₁ + i₂) :=
  inferInstanceAs <| HasTensor X tensorUnit

/-- The right unitor isomorphism for graded objects. -/
/-
**CategoryTheory.GradedObject.Monoidal.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.GradedObject.Monoidal`。
形式化陈述：rightUnitor : tensorObj X tensorUnit ≅ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasMapProdObjFunctorMapBifuncto
rCurriedTensorSingle₀TensorUnit_1`：∀ {I : Type u} [inst : AddMonoid I] {C : Type
 u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]   [inst_2 : CategoryTheory
.MonoidalCatego…

--- 原说明 ---
The right unitor isomorphism for graded objects.
-/
noncomputable def rightUnitor : tensorObj X tensorUnit ≅ X :=
    mapBifunctorRightUnitor (curriedTensor C) (𝟙_ C)
      (rightUnitorNatIso C) (fun (⟨i₁, i₂⟩ : I × I) => i₁ + i₂) add_zero X
/-
**CategoryTheory.GradedObject.Monoidal.rightUnitor_inv_apply** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：rightUnitor_inv_apply (i : I) : (rightUnitor X).inv i = (ρ_ (X i)).inv ≫ (
X i) ◁ tensorUnit₀.inv ≫ ιTensorObj X tensorUnit i 0 i (add_zero i)
参数：i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit_1`：∀ {I : T
ype u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_
1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
-/
lemma rightUnitor_inv_apply (i : I) :
    (rightUnitor X).inv i = (ρ_ (X i)).inv ≫ (X i) ◁ tensorUnit₀.inv ≫
      ιTensorObj X tensorUnit i 0 i (add_zero i) := rfl

variable {X X'}

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.Monoidal.rightUnitor_naturality** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.GradedObject.Monoidal`。
形式化陈述：rightUnitor_naturality (φ : X ⟶ X') : tensorHom φ (𝟙 (tensorUnit)) ≫ (righ
tUnitor X').hom = (rightUnitor X).hom ≫ φ
参数：φ : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.mapBifunctorRightUnitor_naturality`：mapBifun
ctorRightUnitor_naturality : mapBifunctorMapMap F p φ (𝟙 _) ≫ (mapBifunctorRight
Unitor F Y e p hp X').hom = (mapBifunctorRightUnitor…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit_1`：∀ {I : T
ype u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_
1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
-/
lemma rightUnitor_naturality (φ : X ⟶ X') :
    tensorHom φ (𝟙 (tensorUnit)) ≫ (rightUnitor X').hom =
      (rightUnitor X).hom ≫ φ := by
  apply mapBifunctorRightUnitor_naturality

end RightUnitor

section Triangle

variable [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C)
    ((curriedTensor C).flip.obj X₂)]
  (X₁ X₃ : GradedObject I C) [HasTensor X₁ X₃]
  [HasTensor (tensorObj X₁ tensorUnit) X₃] [HasTensor X₁ (tensorObj tensorUnit X₃)]
  [HasGoodTensor₁₂Tensor X₁ tensorUnit X₃] [HasGoodTensorTensor₂₃ X₁ tensorUnit X₃]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GradedObject.Monoidal.triangle** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.GradedObject.Monoidal`。
形式化陈述：triangle : (associator X₁ tensorUnit X₃).hom ≫ tensorHom (𝟙 X₁) (leftUnito
r X₃).hom = tensorHom (rightUnitor X₁).hom (𝟙 X₃)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit_1`：∀ {I : T
ype u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_
1, u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasTensorTensorUnit`：∀ {I : Typ
e u} [inst : AddMonoid I] {C : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} C]   [inst_2 : CategoryTheory.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasMapProdObjFunctorMapBifuncto
rCurriedTensorSingle₀TensorUnit_1`：∀ {I : Type u} [inst : AddMonoid I] {C : Type
 u_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]   [inst_2 : CategoryTheory
.MonoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.Monoidal.instHasMapProdObjFunctorMapBifuncto
rCurriedTensorSingle₀TensorUnit`：∀ {I : Type u} [inst : AddMonoid I] {C : Type u
_1} [inst_1 : CategoryTheory.Category.{v_1, u_1} C]   [inst_2 : CategoryTheory.M
onoidalCatego…
· 使用定理 `CategoryTheory.GradedObject.TriangleIndexData.h₃`：∀ {I₁ : Type u_1} {I₂ 
: Type u_2} {I₃ : Type u_3} {J : Type u_4} [inst : Zero I₂] {r : I₁ × I₂ × I₃ → 
J}   {π : I₁ × I₃ → J} (self : Categor…
· 使用定理 `CategoryTheory.GradedObject.TriangleIndexData.h₁`：∀ {I₁ : Type u_1} {I₂ 
: Type u_2} {I₃ : Type u_3} {J : Type u_4} [inst : Zero I₂] {r : I₁ × I₂ × I₃ → 
J}   {π : I₁ × I₃ → J} (self : Categor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `CategoryTheory.GradedObject.mapBifunctor_triangle`：mapBifunctor_triangle
 (triangle : forall (X₁ : C₁) (X₃ : C₃), ((associator.hom.app X₁).app X₂).app X₃
 ≫ (G.obj X₁).map (e₂.hom.app X₃) = (G.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.triangle`：∀ {C : Type u} {𝒞 : CategoryTh
eory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y : C),   
CategoryTheory.CategoryStruct.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma triangle :
    (associator X₁ tensorUnit X₃).hom ≫ tensorHom (𝟙 X₁) (leftUnitor X₃).hom =
      tensorHom (rightUnitor X₁).hom (𝟙 X₃) := by
  convert!
    mapBifunctor_triangle (curriedAssociatorNatIso C) (𝟙_ C) (rightUnitorNatIso C)
      (leftUnitorNatIso C) (triangleIndexData I) X₁ X₃ (by simp)
  all_goals assumption

end Triangle

end Monoidal

section

variable
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [DecidableEq I] [HasInitial C]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-
**CategoryTheory.GradedObject.monoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.GradedObject`。
形式化陈述：monoidalCategory : MonoidalCategory (GradedObject I C) where tensorObj X Y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.Monoidal.leftUnitor_naturality`：leftUnitor_n
aturality (φ : X ⟶ X') : tensorHom (𝟙 (tensorUnit)) φ ≫ (leftUnitor X').hom = (l
eftUnitor X).hom ≫ φ
· 使用引理 `CategoryTheory.GradedObject.Monoidal.rightUnitor_naturality`：rightUnitor
_naturality (φ : X ⟶ X') : tensorHom φ (𝟙 (tensorUnit)) ≫ (rightUnitor X').hom =
 (rightUnitor X).hom ≫ φ
-/
noncomputable instance monoidalCategory : MonoidalCategory (GradedObject I C) where
  tensorObj X Y := Monoidal.tensorObj X Y
  tensorHom f g := Monoidal.tensorHom f g
  tensorHom_def f g := Monoidal.tensorHom_def f g
  whiskerLeft X _ _ φ := Monoidal.whiskerLeft X φ
  whiskerRight {_ _ φ Y} := Monoidal.whiskerRight φ Y
  tensorUnit := Monoidal.tensorUnit
  associator X₁ X₂ X₃ := Monoidal.associator X₁ X₂ X₃
  associator_naturality f₁ f₂ f₃ := Monoidal.associator_naturality f₁ f₂ f₃
  leftUnitor X := Monoidal.leftUnitor X
  leftUnitor_naturality := Monoidal.leftUnitor_naturality
  rightUnitor X := Monoidal.rightUnitor X
  rightUnitor_naturality := Monoidal.rightUnitor_naturality
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := Monoidal.tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  pentagon X₁ X₂ X₃ X₄ := Monoidal.pentagon X₁ X₂ X₃ X₄
  triangle X₁ X₂ := Monoidal.triangle X₁ X₂

end

section

/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Finite ((fun (i : ℕ × ℕ) => i.1 + i.2) ⁻¹' {n}) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂⟩, (hi : i₁ + i₂ = n)⟩ =>
    ((⟨i₁, by lia⟩, ⟨i₂, by lia⟩) : Fin (n + 1) × Fin (n + 1))) ?_
  rintro ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h
  simpa using h

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : Finite ({ i : (ℕ × ℕ × ℕ) | i.1 + i.2.1 + i.2.2 = n }) := by
  refine Finite.of_injective (fun ⟨⟨i₁, i₂, i₃⟩, (hi : i₁ + i₂ + i₃ = n)⟩ =>
    (⟨⟨i₁, by lia⟩, ⟨i₂, by lia⟩, ⟨i₃, by lia⟩⟩ :
      Fin (n + 1) × Fin (n + 1) × Fin (n + 1))) ?_
  intro _ _ h
  exact Subtype.ext (congrArg (fun x => (x.1.1, x.2.1.1, x.2.2.1)) h)

/-!
The monoidal category structure on `GradedObject ℕ C` can be inferred
from the assumptions `[HasFiniteCoproducts C]`,
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).obj X)]` and
`[∀ (X : C), PreservesFiniteCoproducts ((curriedTensor C).flip.obj X)]`.
This requires importing `Mathlib/CategoryTheory/Limits/Preserves/Finite.lean`.
-/

end

end GradedObject

end CategoryTheory

