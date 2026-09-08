/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# Opposite categories

We provide a category instance on `Cᵒᵖ`.
The morphisms `X ⟶ Y` are defined to be the morphisms `unop Y ⟶ unop X` in `C`.

Here `Cᵒᵖ` is an irreducible typeclass synonym for `C`
(it is the same one used in the algebra library).

We also provide various mechanisms for constructing opposite morphisms, functors,
and natural transformations.

Unfortunately, because we do not have a definitional equality `op (op X) = X`,
there are quite a few variations that are needed in practice.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category theory universes].
open Opposite

variable {C : Type u₁}

section Quiver

variable [Quiver.{v₁} C]

@[to_dual self]
/-
**Quiver.Hom.op_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Quiver.Hom.op : (X ⟶ Y) 
-> (Opposite.op Y ⟶ Opposite.op X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Quiver.Hom.op_inj {X Y : C} :
    Function.Injective (Quiver.Hom.op : (X ⟶ Y) → (Opposite.op Y ⟶ Opposite.op X)) := fun _ _ H =>
  congr_arg Quiver.Hom.unop H

@[to_dual self]
/-
**Quiver.Hom.unop_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injective (Quiver.Hom.unop : (X
 ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Quiver.Hom.unop_inj {X Y : Cᵒᵖ} :
    Function.Injective (Quiver.Hom.unop : (X ⟶ Y) → (Opposite.unop Y ⟶ Opposite.unop X)) :=
  fun _ _ H => congr_arg Quiver.Hom.op H

@[simp, to_dual self]
/-
**Quiver.Hom.unop_op** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quiver.Hom.unop_op {X Y : C} (f : X ⟶ Y) : f.op.unop = f :=
  rfl

@[simp, to_dual self]
/-
**Quiver.Hom.unop_op'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.Hom.unop_op' {X Y : Cᵒᵖ} {x} : @Quiver.Hom.unop C _ X Y no_index (O
pposite.op (unop
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quiver.Hom.unop_op' {X Y : Cᵒᵖ} {x} :
    @Quiver.Hom.unop C _ X Y no_index (Opposite.op (unop := x)) = x := rfl

@[simp, to_dual self]
/-
**Quiver.Hom.op_unop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.op = f :=
  rfl

@[simp, to_dual self]
/-
**Quiver.Hom.unop_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quiver.Hom.unop_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) : Quiver.Hom.unop { unop
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quiver.Hom.unop_mk {X Y : Cᵒᵖ} (f : X ⟶ Y) : Quiver.Hom.unop { unop := f } = f :=
  rfl

end Quiver

namespace CategoryTheory

section

variable [CategoryStruct.{v₁} C]

/-- The opposite `CategoryStruct`. -/
/-
**CategoryTheory.CategoryStruct.opposite** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.CategoryStruct`。
形式化陈述：{C : Type u₁} → [CategoryTheory.CategoryStruct.{v₁, u₁} C] → CategoryTheor
y.CategoryStruct.{v₁, u₁} Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite `CategoryStruct`.
-/
instance CategoryStruct.opposite : CategoryStruct.{v₁} Cᵒᵖ where
  comp f g := (g.unop ≫ f.unop).op
  id X := (𝟙 (unop X)).op

@[simp]
/-
**CategoryTheory.unop_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X) :=
  rfl

@[simp]
/-
**CategoryTheory.op_id_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_id_unop {X : Cᵒᵖ} : (𝟙 (unop X)).op = 𝟙 X :=
  rfl

@[simp, grind _=_, to_dual self]
/-
**CategoryTheory.op_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).op = g.op ≫ f.op :=
  rfl

@[simp]
/-
**CategoryTheory.op_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_id {X : C} : (𝟙 X).op = 𝟙 (op X) :=
  rfl

@[simp, to_dual self]
/-
**CategoryTheory.unop_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ 
f.unop
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g).unop = g.unop ≫ f.unop :=
  rfl

@[simp]
/-
**CategoryTheory.unop_id_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_id_op {X : C} : (𝟙 (op X)).unop = 𝟙 X :=
  rfl

-- This lemma is needed to prove `Category.opposite` below.
@[to_dual self]
/-
**CategoryTheory.op_comp_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_comp_unop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) : (g.unop ≫ f.unop).op 
= f ≫ g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_comp_unop {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) : (g.unop ≫ f.unop).op = f ≫ g :=
  rfl

end

open CategoryTheory.Functor

variable [Category.{v₁} C]

/-- The opposite category. -/
@[stacks 001M]
/-
**CategoryTheory.Category.opposite** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat
egory`。
形式化陈述：{C : Type u₁} → [CategoryTheory.Category.{v₁, u₁} C] → CategoryTheory.Cate
gory.{v₁, u₁} Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite category.
-/
instance Category.opposite : Category.{v₁} Cᵒᵖ where
  __ := CategoryStruct.opposite
  comp_id f := by rw [← op_comp_unop, unop_id, id_comp, Quiver.Hom.op_unop]
  id_comp f := by rw [← op_comp_unop, unop_id, comp_id, Quiver.Hom.op_unop]
  assoc f g h := by simp only [← op_comp_unop, Quiver.Hom.unop_op, assoc]

-- Note: these need to be proven manually as the original lemmas are only stated in terms
-- of `CategoryStruct`s!
@[to_dual none]
/-
**CategoryTheory.op_comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_comp_assoc {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z
'} : (f ≫ g).op ≫ h = g.op ≫ f.op ≫ h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem op_comp_assoc {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : Cᵒᵖ} {h : op X ⟶ Z'} :
    (f ≫ g).op ≫ h = g.op ≫ f.op ≫ h := by
  simp only [op_comp, Category.assoc]

@[to_dual none]
/-
**CategoryTheory.unop_comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_comp_assoc {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : C} {h : unop X
 ⟶ Z'} : (f ≫ g).unop ≫ h = g.unop ≫ f.unop ≫ h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unop_comp_assoc {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z} {Z' : C} {h : unop X ⟶ Z'} :
    (f ≫ g).unop ≫ h = g.unop ≫ f.unop ≫ h := by
  simp only [unop_comp, Category.assoc]

section

variable (C)

/-- The functor from the double-opposite of a category to the underlying category. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.unopUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：unopUnop : Cᵒᵖᵒᵖ ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from the double-opposite of a category to the underlying category.
-/
def unopUnop : Cᵒᵖᵒᵖ ⥤ C where
  obj X := unop (unop X)
  map f := f.unop.unop

/-- The functor from a category to its double-opposite. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.opOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：opOp : C ⥤ Cᵒᵖᵒᵖ where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from a category to its double-opposite.
-/
def opOp : C ⥤ Cᵒᵖᵒᵖ where
  obj X := op (op X)
  map f := f.op.op

/-- The double opposite category is equivalent to the original. -/
@[simps]
/-
**CategoryTheory.opOpEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：opOpEquivalence : Cᵒᵖᵒᵖ ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The double opposite category is equivalent to the original.
-/
def opOpEquivalence : Cᵒᵖᵒᵖ ≌ C where
  functor := unopUnop C
  inverse := opOp C
  unitIso := Iso.refl (𝟭 Cᵒᵖᵒᵖ)
  counitIso := Iso.refl (opOp C ⋙ unopUnop C)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (opOp C).IsEquivalence :=
  (opOpEquivalence C).isEquivalence_inverse
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (unopUnop C).IsEquivalence :=
  (opOpEquivalence C).isEquivalence_functor

end

/-- If `f` is an isomorphism, so is `f.op` -/
@[to_dual self]
/-
**CategoryTheory.isIso_op** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_op {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.op
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X

--- 原说明 ---
If `f` is an isomorphism, so is `f.op`
-/
instance isIso_op {X Y : C} (f : X ⟶ Y) [IsIso f] : IsIso f.op :=
  ⟨⟨(inv f).op, ⟨Quiver.Hom.unop_inj (by simp), Quiver.Hom.unop_inj (by simp)⟩⟩⟩

/-- If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
@[to_dual self]
/-
**CategoryTheory.isIso_of_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.op] : IsIso f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X

--- 原说明 ---
If `f.op` is an isomorphism `f` must be too.
(This cannot be an instance as it would immediately loop!)
-/
theorem isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.op] : IsIso f :=
  ⟨⟨(inv f.op).unop, ⟨Quiver.Hom.op_inj (by simp), Quiver.Hom.op_inj (by simp)⟩⟩⟩

@[to_dual self]
/-
**CategoryTheory.isIso_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso f.op ↔ IsIso f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.isIso_of_op`：isIso_of_op {X Y : C} (f : X ⟶ Y) [IsIso f.o
p] : IsIso f
-/
theorem isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso f.op ↔ IsIso f :=
  ⟨fun _ => isIso_of_op _, fun _ => inferInstance⟩

@[to_dual self]
/-
**CategoryTheory.isIso_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso f.unop ↔ IsIso f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isIso_op_iff`：isIso_op_iff {X Y : C} (f : X ⟶ Y) : IsIso 
f.op ↔ IsIso f
· 使用定理 `Quiver.Hom.op_unop`：Quiver.Hom.op_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) : f.unop.
op = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso f.unop ↔ IsIso f := by
  rw [← isIso_op_iff f.unop, Quiver.Hom.op_unop]

@[to_dual self]
/-
**CategoryTheory.isIso_unop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：isIso_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unop
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.isIso_unop_iff`：isIso_unop_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : 
IsIso f.unop ↔ IsIso f
-/
instance isIso_unop {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : IsIso f.unop :=
  (isIso_unop_iff _).2 inferInstance

@[simp, push ←, to_dual self]
/-
**CategoryTheory.op_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).op = inv f.op
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
-/
theorem op_inv {X Y : C} (f : X ⟶ Y) [IsIso f] : (inv f).op = inv f.op := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← op_comp, IsIso.inv_hom_id, op_id]

@[simp, push ←, to_dual self]
/-
**CategoryTheory.unop_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (inv f).unop = inv f.unop
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.unop_id`：unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X)
-/
theorem unop_inv {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso f] : (inv f).unop = inv f.unop := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← unop_comp, IsIso.inv_hom_id, unop_id]

namespace Functor

section

variable {D : Type u₂} [Category.{v₂} D]

/-- The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these. -/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C D → CategoryTheory.Functor Cᵒᵖ Dᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a functor, i.e. considering a functor `F : C ⥤ D` as a functor `
Cᵒᵖ ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made between these.
-/
protected def op (F : C ⥤ D) : Cᵒᵖ ⥤ Dᵒᵖ where
  obj X := op (F.obj (unop X))
  map f := (F.map f.unop).op

/-- Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`.
In informal mathematics no distinction is made between these.
-/
@[simps, implicit_reducible]
/-
**CategoryTheory.Functor.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor Cᵒᵖ Dᵒᵖ → CategoryTheory.Functor C D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : Cᵒᵖ ⥤ Dᵒᵖ` we can take the "unopposite" functor `F : C ⥤ D`
.
In informal mathematics no distinction is made between these.
-/
protected def unop (F : Cᵒᵖ ⥤ Dᵒᵖ) : C ⥤ D where
  obj X := unop (F.obj (op X))
  map f := (F.map f.op).unop

/-- The isomorphism between `F.op.unop` and `F`. -/
@[simps!]
/-
**CategoryTheory.Functor.opUnopIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：opUnopIso (F : C ⥤ D) : F.op.unop ≅ F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `F.op.unop` and `F`.
-/
def opUnopIso (F : C ⥤ D) : F.op.unop ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The isomorphism between `F.unop.op` and `F`. -/
@[simps!]
/-
**CategoryTheory.Functor.unopOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：unopOpIso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `F.unop.op` and `F`.
-/
def unopOpIso (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

variable (C D)

/-- Taking the opposite of a functor is functorial.
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.opHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking the opposite of a functor is functorial.
-/
def opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ where
  obj F := (unop F).op
  map α :=
    { app := fun X => (α.unop.app (unop X)).op
      naturality := fun _ _ f => Quiver.Hom.unop_inj (α.unop.naturality f.unop).symm }

/-- Take the "unopposite" of a functor is functorial.
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.opInv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：opInv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the "unopposite" of a functor is functorial.
-/
def opInv : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (C ⥤ D)ᵒᵖ where
  obj F := op F.unop
  map α :=
    Quiver.Hom.op
      { app := fun X => (α.app (op X)).unop
        naturality := fun _ _ f => Quiver.Hom.op_inj <| (α.naturality f.op).symm }

variable {C D}

section Compositions

variable {E : Type*} [Category* E]

/-- Compatibility of `Functor.op` with respect to functor composition. -/
@[simps!]
/-
**CategoryTheory.Functor.opComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：opComp (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op ≅ F.op ⋙ G.op
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compatibility of `Functor.op` with respect to functor composition.
-/
def opComp (F : C ⥤ D) (G : D ⥤ E) : (F ⋙ G).op ≅ F.op ⋙ G.op := Iso.refl _

/-- Compatibility of `Functor.unop` with respect to functor composition. -/
@[simps!]
/-
**CategoryTheory.Functor.unopComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：unopComp (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ) : (F ⋙ G).unop ≅ F.unop ⋙ G.unop
参数：F : Cᵒᵖ ⥤ Dᵒᵖ；G : Dᵒᵖ ⥤ Eᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compatibility of `Functor.unop` with respect to functor composition.
-/
def unopComp (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Eᵒᵖ) : (F ⋙ G).unop ≅ F.unop ⋙ G.unop := Iso.refl _

variable (C) in
/-- `Functor.op` transforms identity functors to identity functors. -/
@[simps!]
/-
**CategoryTheory.Functor.opId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`
。
形式化陈述：opId : (𝟭 C).op ≅ 𝟭 (Cᵒᵖ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.op` transforms identity functors to identity functors.
-/
def opId : (𝟭 C).op ≅ 𝟭 (Cᵒᵖ) := Iso.refl _

variable (C) in
/-- `Functor.unop` transforms identity functors to identity functors. -/
@[simps!]
/-
**CategoryTheory.Functor.unopId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：unopId : (𝟭 Cᵒᵖ).unop ≅ 𝟭 C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.unop` transforms identity functors to identity functors.
-/
def unopId : (𝟭 Cᵒᵖ).unop ≅ 𝟭 C := Iso.refl _

end Compositions

/--
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a functor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.leftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor C Dᵒᵖ → CategoryTheory.Functor Cᵒᵖ D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another variant of the opposite of functor, turning a functor `C ⥤ Dᵒᵖ` into a f
unctor `Cᵒᵖ ⥤ D`.
In informal mathematics no distinction is made.
-/
protected def leftOp (F : C ⥤ Dᵒᵖ) : Cᵒᵖ ⥤ D where
  obj X := unop (F.obj (unop X))
  map f := (F.map f.unop).unop

/--
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a functor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.rightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.F
unctor Cᵒᵖ D → CategoryTheory.Functor C Dᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another variant of the opposite of functor, turning a functor `Cᵒᵖ ⥤ D` into a f
unctor `C ⥤ Dᵒᵖ`.
In informal mathematics no distinction is made.
-/
protected def rightOp (F : Cᵒᵖ ⥤ D) : C ⥤ Dᵒᵖ where
  obj X := op (F.obj (op X))
  map f := (F.map f.op).op
/-
**CategoryTheory.Functor.rightOp_map_unop** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：rightOp_map_unop {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y) : (F.rightOp.map f).unop 
= F.map f.op
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightOp_map_unop {F : Cᵒᵖ ⥤ D} {X Y} (f : X ⟶ Y) :
    (F.rightOp.map f).unop = F.map f.op := rfl
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ D} [Full F] : Full F.op where
  map_surjective f := ⟨(F.preimage f.unop).op, by simp⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ D} [Faithful F] : Faithful F.op where
  map_injective h := Quiver.Hom.unop_inj <| by simpa using map_injective F (Quiver.Hom.op_inj h)

/-- The opposite of a fully faithful functor is fully faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C D} → F.FullyFaithful → F.op.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a fully faithful functor is fully faithful.
-/
protected def FullyFaithful.op {F : C ⥤ D} (hF : F.FullyFaithful) : F.op.FullyFaithful where
  preimage {X Y} f := .op <| hF.preimage f.unop

/-- A functor is fully faithful when its opposite is fully faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor Cᵒᵖ Dᵒᵖ} → F.FullyFaithful → F.unop.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is fully faithful when its opposite is fully faithful.
-/
protected def FullyFaithful.unop {F : Cᵒᵖ ⥤ Dᵒᵖ} (hF : F.FullyFaithful) :
    F.unop.FullyFaithful where
  preimage {X Y} f := (hF.preimage f.op).unop

/-- If F is faithful then the `rightOp` of F is also faithful. -/
/-
**CategoryTheory.Functor.rightOp_faithful** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：rightOp_faithful {F : Cᵒᵖ ⥤ D} [Faithful F] : Faithful F.rightOp where map
_injective h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))

--- 原说明 ---
If F is faithful then the `rightOp` of F is also faithful.
-/
instance rightOp_faithful {F : Cᵒᵖ ⥤ D} [Faithful F] : Faithful F.rightOp where
  map_injective h := Quiver.Hom.op_inj (map_injective F (Quiver.Hom.op_inj h))

/-- If F is faithful then the `leftOp` of F is also faithful. -/
/-
**CategoryTheory.Functor.leftOp_faithful** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：leftOp_faithful {F : C ⥤ Dᵒᵖ} [Faithful F] : Faithful F.leftOp where map_i
njective h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))

--- 原说明 ---
If F is faithful then the `leftOp` of F is also faithful.
-/
instance leftOp_faithful {F : C ⥤ Dᵒᵖ} [Faithful F] : Faithful F.leftOp where
  map_injective h := Quiver.Hom.unop_inj (map_injective F (Quiver.Hom.unop_inj h))
/-
**CategoryTheory.Functor.rightOp_full** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：rightOp_full {F : Cᵒᵖ ⥤ D} [Full F] : Full F.rightOp where map_surjective 
f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance rightOp_full {F : Cᵒᵖ ⥤ D} [Full F] : Full F.rightOp where
  map_surjective f := ⟨(F.preimage f.unop).unop, by simp⟩
/-
**CategoryTheory.Functor.leftOp_full** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：leftOp_full {F : C ⥤ Dᵒᵖ} [Full F] : Full F.leftOp where map_surjective f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance leftOp_full {F : C ⥤ Dᵒᵖ} [Full F] : Full F.leftOp where
  map_surjective f := ⟨(F.preimage f.op).op, by simp⟩

/-- The opposite of a fully faithful functor is fully faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.leftOp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor C Dᵒᵖ} → F.FullyFaithful → F.leftOp.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a fully faithful functor is fully faithful.
-/
protected def FullyFaithful.leftOp {F : C ⥤ Dᵒᵖ} (hF : F.FullyFaithful) :
    F.leftOp.FullyFaithful where
  preimage {X Y} f := .op <| hF.preimage f.op

/-- The opposite of a fully faithful functor is fully faithful. -/
/-
**CategoryTheory.Functor.FullyFaithful.rightOp** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.FullyFaithful`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F : Cat
egoryTheory.Functor Cᵒᵖ D} → F.FullyFaithful → F.rightOp.FullyFaithful
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a fully faithful functor is fully faithful.
-/
protected def FullyFaithful.rightOp {F : Cᵒᵖ ⥤ D} (hF : F.FullyFaithful) :
    F.rightOp.FullyFaithful where
  preimage {X Y} f := .unop <| hF.preimage f.unop

/-- Compatibility of `Functor.rightOp` with respect to functor composition. -/
@[simps!]
/-
**CategoryTheory.Functor.rightOpComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：rightOpComp {E : Type*} [Category* E] (F : Cᵒᵖ ⥤ D) (G : D ⥤ E) : (F ⋙ G).
rightOp ≅ F.rightOp ⋙ G.op
参数：F : Cᵒᵖ ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compatibility of `Functor.rightOp` with respect to functor composition.
-/
def rightOpComp {E : Type*} [Category* E] (F : Cᵒᵖ ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).rightOp ≅ F.rightOp ⋙ G.op :=
  Iso.refl _

/-- Compatibility of `Functor.leftOp` with respect to functor composition. -/
@[simps!]
/-
**CategoryTheory.Functor.leftOpComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：leftOpComp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ Eᵒᵖ) : (F ⋙ G).l
eftOp ≅ F.op ⋙ G.leftOp
参数：F : C ⥤ D；G : D ⥤ Eᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compatibility of `Functor.leftOp` with respect to functor composition.
-/
def leftOpComp {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ Eᵒᵖ) :
    (F ⋙ G).leftOp ≅ F.op ⋙ G.leftOp :=
  Iso.refl _

section
variable (C)

/-- `Functor.rightOp` sends identity functors to the canonical isomorphism `opOp`. -/
@[simps!]
/-
**CategoryTheory.Functor.rightOpId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：rightOpId : (𝟭 Cᵒᵖ).rightOp ≅ opOp C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.rightOp` sends identity functors to the canonical isomorphism `opOp`.
-/
def rightOpId : (𝟭 Cᵒᵖ).rightOp ≅ opOp C := Iso.refl _

/-- `Functor.leftOp` sends identity functors to the canonical isomorphism `unopUnop`. -/
@[simps!]
/-
**CategoryTheory.Functor.leftOpId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：leftOpId : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.leftOp` sends identity functors to the canonical isomorphism `unopUnop`
.
-/
def leftOpId : (𝟭 Cᵒᵖ).leftOp ≅ unopUnop C := Iso.refl _

end

/-- The isomorphism between `F.leftOp.rightOp` and `F`. -/
@[simps!]
/-
**CategoryTheory.Functor.leftOpRightOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：leftOpRightOpIso (F : C ⥤ Dᵒᵖ) : F.leftOp.rightOp ≅ F
参数：F : C ⥤ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `F.leftOp.rightOp` and `F`.
-/
def leftOpRightOpIso (F : C ⥤ Dᵒᵖ) : F.leftOp.rightOp ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The isomorphism between `F.rightOp.leftOp` and `F`. -/
@[simps!]
/-
**CategoryTheory.Functor.rightOpLeftOpIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：rightOpLeftOpIso (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp ≅ F
参数：F : Cᵒᵖ ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `F.rightOp.leftOp` and `F`.
-/
def rightOpLeftOpIso (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- Whenever possible, it is advisable to use the isomorphism `rightOpLeftOpIso`
instead of this equality of functors. -/
/-
**CategoryTheory.Functor.rightOp_leftOp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：rightOp_leftOp_eq (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp = F
参数：F : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Whenever possible, it is advisable to use the isomorphism `rightOpLeftOpIso`
instead of this equality of functors.
-/
theorem rightOp_leftOp_eq (F : Cᵒᵖ ⥤ D) : F.rightOp.leftOp = F := by
  cases F
  rfl

end

end Functor

namespace NatTrans

variable {D : Type u₂} [Category.{v₂} D]

section

variable {F G : C ⥤ D}

/-- The opposite of a natural transformation. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTrans`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → {F G : CategoryT
heory.Functor C D} → (F ⟶ G) → (G.op ⟶ F.op)
参数：F ⟶ G；G.op ⟶ F.op。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a natural transformation.
-/
protected def op (α : F ⟶ G) : G.op ⟶ F.op where
  app X := (α.app (unop X)).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
/-
**CategoryTheory.NatTrans.op_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatTra
ns`。
形式化陈述：op_id (F : C ⥤ D) : NatTrans.op (𝟙 F) = 𝟙 F.op
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_id (F : C ⥤ D) : NatTrans.op (𝟙 F) = 𝟙 F.op :=
  rfl

@[simp, to_dual self, reassoc]
/-
**CategoryTheory.NatTrans.op_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：op_comp {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) : NatTrans.op (α ≫ β) = NatTra
ns.op β ≫ NatTrans.op α
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_comp {H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.op (α ≫ β) = NatTrans.op β ≫ NatTrans.op α :=
  rfl

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.op_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.NatTrans`。
形式化陈述：op_whiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G) : NatTra
ns.op (whiskerRight α H) = (Functor.opComp _ _).hom ≫ whiskerRight (NatTrans.op 
α) H.op ≫ (Functor.opComp _ _).inv
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.opComp_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_whiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G) :
    NatTrans.op (whiskerRight α H) =
    (Functor.opComp _ _).hom ≫ whiskerRight (NatTrans.op α) H.op ≫ (Functor.opComp _ _).inv := by
  cat_disch

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.op_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：op_whiskerLeft {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G) : NatTran
s.op (whiskerLeft H α) = (Functor.opComp _ _).hom ≫ whiskerLeft H.op (NatTrans.o
p α) ≫ (Functor.opComp _ _).inv
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.opComp_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_whiskerLeft {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G) :
    NatTrans.op (whiskerLeft H α) =
    (Functor.opComp _ _).hom ≫ whiskerLeft H.op (NatTrans.op α) ≫ (Functor.opComp _ _).inv := by
  cat_disch

/-- The "unopposite" of a natural transformation. -/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTran
s`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor Cᵒᵖ Dᵒᵖ} → (F ⟶ G) → (G.unop ⟶ F.unop)
参数：F ⟶ G；G.unop ⟶ F.unop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "unopposite" of a natural transformation.
-/
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) : G.unop ⟶ F.unop where
  app X := (α.app (op X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
/-
**CategoryTheory.NatTrans.unop_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.unop (𝟙 F) = 𝟙 F.unop
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.unop (𝟙 F) = 𝟙 F.unop :=
  rfl

@[simp, to_dual self, reassoc]
/-
**CategoryTheory.NatTrans.unop_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：unop_comp {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (β : G ⟶ H) : NatTrans.unop (α ≫
 β) = NatTrans.unop β ≫ NatTrans.unop α
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_comp {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ⟶ G) (β : G ⟶ H) :
    NatTrans.unop (α ≫ β) = NatTrans.unop β ≫ NatTrans.unop α :=
  rfl

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.unop_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.NatTrans`。
形式化陈述：unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ E
ᵒᵖ} (α : F ⟶ G) : NatTrans.unop (whiskerRight α H) = (Functor.unopComp _ _).hom 
≫ whiskerRight (NatTrans.unop α) H.unop ≫ (Functor.unopComp _ _).inv
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.unopComp_hom_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ⟶ G) :
    NatTrans.unop (whiskerRight α H) =
    (Functor.unopComp _ _).hom ≫ whiskerRight (NatTrans.unop α) H.unop ≫
      (Functor.unopComp _ _).inv := by
  cat_disch

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.unop_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.NatTrans`。
形式化陈述：unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒ
ᵖ} (α : F ⟶ G) : NatTrans.unop (whiskerLeft H α) = (Functor.unopComp _ _).hom ≫ 
whiskerLeft H.unop (NatTrans.unop α) ≫ (Functor.unopComp _ _).inv
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.unopComp_hom_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ⟶ G) :
    NatTrans.unop (whiskerLeft H α) =
    (Functor.unopComp _ _).hom ≫ whiskerLeft H.unop (NatTrans.unop α) ≫
      (Functor.unopComp _ _).inv := by
  cat_disch

/-- Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformation `G ⟶ F`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.removeOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Nat
Trans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → {F G : CategoryT
heory.Functor C D} → (F.op ⟶ G.op) → (G ⟶ F)
参数：F.op ⟶ G.op；G ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `α : F.op ⟶ G.op`,
we can take the "unopposite" of each component obtaining a natural transformatio
n `G ⟶ F`.
-/
protected def removeOp (α : F.op ⟶ G.op) : G ⟶ F where
  app X := (α.app (op X)).unop
  naturality X Y f :=
    Quiver.Hom.op_inj <| by simpa only [Functor.op_map] using! (α.naturality f.op).symm

@[simp]
/-
**CategoryTheory.NatTrans.removeOp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：removeOp_id (F : C ⥤ D) : NatTrans.removeOp (𝟙 F.op) = 𝟙 F
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem removeOp_id (F : C ⥤ D) : NatTrans.removeOp (𝟙 F.op) = 𝟙 F :=
  rfl

/-- Given a natural transformation `α : F.unop ⟶ G.unop`, we can take the opposite of each
component obtaining a natural transformation `G ⟶ F`. -/
@[implicit_reducible, simps, to_dual self]
/-
**CategoryTheory.NatTrans.removeUnop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.N
atTrans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor Cᵒᵖ Dᵒᵖ} → (F.unop ⟶ G.unop) → (G ⟶ F)
参数：F.unop ⟶ G.unop；G ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `α : F.unop ⟶ G.unop`, we can take the opposite o
f each
component obtaining a natural transformation `G ⟶ F`.
-/
protected def removeUnop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F.unop ⟶ G.unop) : G ⟶ F where
  app X := (α.app (unop X)).op
  naturality X Y f :=
    Quiver.Hom.unop_inj <| by simpa only [Functor.unop_map] using! (α.naturality f.unop).symm

@[simp]
/-
**CategoryTheory.NatTrans.removeUnop_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.NatTrans`。
形式化陈述：removeUnop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem removeUnop_id (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatTrans.removeUnop (𝟙 F.unop) = 𝟙 F :=
  rfl

end

section

variable {F G H : C ⥤ Dᵒᵖ}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.leftOp ⟶ F.leftOp`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.leftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTr
ans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor C Dᵒᵖ} → (F ⟶ G) → (G.leftOp ⟶ F.leftOp)
参数：F ⟶ G；G.leftOp ⟶ F.leftOp。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `α : F ⟶ G`, for `F G : C ⥤ Dᵒᵖ`,
taking `unop` of each component gives a natural transformation `G.leftOp ⟶ F.lef
tOp`.
-/
protected def leftOp (α : F ⟶ G) : G.leftOp ⟶ F.leftOp where
  app X := (α.app (unop X)).unop
  naturality X Y f := Quiver.Hom.op_inj (by simp)

@[simp]
/-
**CategoryTheory.NatTrans.leftOp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：leftOp_id : NatTrans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftOp_id : NatTrans.leftOp (𝟙 F : F ⟶ F) = 𝟙 F.leftOp :=
  rfl

@[simp, to_dual self]
/-
**CategoryTheory.NatTrans.leftOp_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：leftOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.leftOp (α ≫ β) = NatTrans.l
eftOp β ≫ NatTrans.leftOp α
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.leftOp (α ≫ β) =
    NatTrans.leftOp β ≫ NatTrans.leftOp α :=
  rfl

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.leftOpWhiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.NatTrans`。
形式化陈述：leftOpWhiskerRight {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G) : (wh
iskerLeft H α).leftOp = (Functor.leftOpComp H G).hom ≫ whiskerLeft _ α.leftOp ≫ 
(Functor.leftOpComp H F).inv
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.leftOpComp_hom_app`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.leftOpComp_inv_app`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftOpWhiskerRight {E : Type*} [Category* E] {H : E ⥤ C} (α : F ⟶ G) :
    (whiskerLeft H α).leftOp = (Functor.leftOpComp H G).hom ≫ whiskerLeft _ α.leftOp ≫
      (Functor.leftOpComp H F).inv := by
  cat_disch

/-- Given a natural transformation `α : F.leftOp ⟶ G.leftOp`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.removeLeftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor C Dᵒᵖ} → (F.leftOp ⟶ G.leftOp) → (G ⟶ F)
参数：F.leftOp ⟶ G.leftOp；G ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `α : F.leftOp ⟶ G.leftOp`, for `F G : C ⥤ Dᵒᵖ`,
taking `op` of each component gives a natural transformation `G ⟶ F`.
-/
protected def removeLeftOp (α : F.leftOp ⟶ G.leftOp) : G ⟶ F where
  app X := (α.app (op X)).op
  naturality X Y f :=
    Quiver.Hom.unop_inj <| by simpa only [Functor.leftOp_map] using! (α.naturality f.op).symm

@[simp]
/-
**CategoryTheory.NatTrans.removeLeftOp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.NatTrans`。
形式化陈述：removeLeftOp_id : NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem removeLeftOp_id : NatTrans.removeLeftOp (𝟙 F.leftOp) = 𝟙 F :=
  rfl

end

section

variable {F G H : Cᵒᵖ ⥤ D}

/-- Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.rightOp ⟶ F.rightOp`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.rightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor Cᵒᵖ D} → (F ⟶ G) → (G.rightOp ⟶ F.rightOp)
参数：F ⟶ G；G.rightOp ⟶ F.rightOp。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `α : F ⟶ G`, for `F G : Cᵒᵖ ⥤ D`,
taking `op` of each component gives a natural transformation `G.rightOp ⟶ F.righ
tOp`.
-/
protected def rightOp (α : F ⟶ G) : G.rightOp ⟶ F.rightOp where
  app _ := (α.app _).op
  naturality X Y f := Quiver.Hom.unop_inj (by simp)

@[simp]
/-
**CategoryTheory.NatTrans.rightOp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.N
atTrans`。
形式化陈述：rightOp_id : NatTrans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightOp_id : NatTrans.rightOp (𝟙 F : F ⟶ F) = 𝟙 F.rightOp :=
  rfl

@[simp, to_dual self]
/-
**CategoryTheory.NatTrans.rightOp_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：rightOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.rightOp (α ≫ β) = NatTrans
.rightOp β ≫ NatTrans.rightOp α
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightOp_comp (α : F ⟶ G) (β : G ⟶ H) : NatTrans.rightOp (α ≫ β) =
    NatTrans.rightOp β ≫ NatTrans.rightOp α :=
  rfl

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.rightOpWhiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.NatTrans`。
形式化陈述：rightOpWhiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G) : (w
hiskerRight α H).rightOp = (Functor.rightOpComp G H).hom ≫ whiskerRight α.rightO
p H.op ≫ (Functor.rightOpComp F H).inv
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.rightOpComp_hom_app`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.rightOpComp_inv_app`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightOpWhiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ⟶ G) :
    (whiskerRight α H).rightOp = (Functor.rightOpComp G H).hom ≫ whiskerRight α.rightOp H.op ≫
      (Functor.rightOpComp F H).inv := by
  cat_disch

/-- Given a natural transformation `α : F.rightOp ⟶ G.rightOp`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
@[implicit_reducible, to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.NatTrans.removeRightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.NatTrans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor Cᵒᵖ D} → (F.rightOp ⟶ G.rightOp) → (G ⟶ F)
参数：F.rightOp ⟶ G.rightOp；G ⟶ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `α : F.rightOp ⟶ G.rightOp`, for `F G : Cᵒᵖ ⥤ D`,
taking `unop` of each component gives a natural transformation `G ⟶ F`.
-/
protected def removeRightOp (α : F.rightOp ⟶ G.rightOp) : G ⟶ F where
  app X := (α.app X.unop).unop
  naturality X Y f :=
    Quiver.Hom.op_inj <| by simpa only [Functor.rightOp_map] using! (α.naturality f.unop).symm

@[simp]
/-
**CategoryTheory.NatTrans.removeRightOp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans`。
形式化陈述：removeRightOp_id : NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem removeRightOp_id : NatTrans.removeRightOp (𝟙 F.rightOp) = 𝟙 F :=
  rfl

end

end NatTrans

namespace Iso

variable {X Y : C}

/-- The opposite isomorphism.
-/
@[simps]
/-
**CategoryTheory.Iso.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(X ≅ Y) → (Opposite.op Y ≅ Opposite.op X)
参数：X ≅ Y；Opposite.op Y ≅ Opposite.op X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite isomorphism.
-/
protected def op (α : X ≅ Y) : op Y ≅ op X where
  hom := α.hom.op
  inv := α.inv.op
  hom_inv_id := Quiver.Hom.unop_inj α.inv_hom_id
  inv_hom_id := Quiver.Hom.unop_inj α.hom_inv_id

/-- The isomorphism obtained from an isomorphism in the opposite category. -/
@[simps]
/-
**CategoryTheory.Iso.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where hom
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism obtained from an isomorphism in the opposite category.
-/
def unop {X Y : Cᵒᵖ} (f : X ≅ Y) : Y.unop ≅ X.unop where
  hom := f.hom.unop
  inv := f.inv.unop
  hom_inv_id := by simp only [← unop_comp, f.inv_hom_id, unop_id]
  inv_hom_id := by simp only [← unop_comp, f.hom_inv_id, unop_id]

@[simp]
/-
**CategoryTheory.Iso.unop_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f
参数：f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
theorem unop_op {X Y : Cᵒᵖ} (f : X ≅ Y) : f.unop.op = f := by (ext; rfl)

@[simp]
/-
**CategoryTheory.Iso.op_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f
参数：f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
-/
theorem op_unop {X Y : C} (f : X ≅ Y) : f.op.unop = f := by (ext; rfl)

variable (X) in
@[simp]
/-
**CategoryTheory.Iso.op_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：op_refl : Iso.op (Iso.refl X) = Iso.refl (op X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_refl : Iso.op (Iso.refl X) = Iso.refl (op X) := rfl

@[simp]
/-
**CategoryTheory.Iso.op_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：op_trans {Z : C} (α : X ≅ Y) (β : Y ≅ Z) : Iso.op (α ≪≫ β) = Iso.op β ≪≫ I
so.op α
参数：α : X ≅ Y；β : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_trans {Z : C} (α : X ≅ Y) (β : Y ≅ Z) :
    Iso.op (α ≪≫ β) = Iso.op β ≪≫ Iso.op α :=
  rfl

@[simp]
/-
**CategoryTheory.Iso.op_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：op_symm (α : X ≅ Y) : Iso.op α.symm = (Iso.op α).symm
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_symm (α : X ≅ Y) : Iso.op α.symm = (Iso.op α).symm := rfl

@[simp]
/-
**CategoryTheory.Iso.unop_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：unop_refl (X : Cᵒᵖ) : Iso.unop (Iso.refl X) = Iso.refl X.unop
参数：X : Cᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_refl (X : Cᵒᵖ) : Iso.unop (Iso.refl X) = Iso.refl X.unop := rfl

@[simp]
/-
**CategoryTheory.Iso.unop_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：unop_trans {X Y Z : Cᵒᵖ} (α : X ≅ Y) (β : Y ≅ Z) : Iso.unop (α ≪≫ β) = Iso
.unop β ≪≫ Iso.unop α
参数：α : X ≅ Y；β : Y ≅ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_trans {X Y Z : Cᵒᵖ} (α : X ≅ Y) (β : Y ≅ Z) :
    Iso.unop (α ≪≫ β) = Iso.unop β ≪≫ Iso.unop α :=
  rfl

@[simp]
/-
**CategoryTheory.Iso.unop_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：unop_symm {X Y : Cᵒᵖ} (α : X ≅ Y) : Iso.unop α.symm = (Iso.unop α).symm
参数：α : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_symm {X Y : Cᵒᵖ} (α : X ≅ Y) : Iso.unop α.symm = (Iso.unop α).symm := rfl

section

variable {D : Type*} [Category* D] {F G : C ⥤ Dᵒᵖ} (e : F ≅ G) (X : C)

@[reassoc +to_dual (attr := simp)]
/-
**CategoryTheory.Iso.unop_hom_inv_id_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：unop_hom_inv_id_app : (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.unop_id`：unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X)
-/
lemma unop_hom_inv_id_app : (e.hom.app X).unop ≫ (e.inv.app X).unop = 𝟙 _ := by
  rw [← unop_comp, inv_hom_id_app, unop_id]

@[reassoc +to_dual (attr := simp)]
/-
**CategoryTheory.Iso.unop_inv_hom_id_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：unop_inv_hom_id_app : (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.unop_comp`：unop_comp {X Y Z : Cᵒᵖ} {f : X ⟶ Y} {g : Y ⟶ Z
} : (f ≫ g).unop = g.unop ≫ f.unop
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.unop_id`：unop_id {X : Cᵒᵖ} : (𝟙 X).unop = 𝟙 (unop X)
-/
lemma unop_inv_hom_id_app : (e.inv.app X).unop ≫ (e.hom.app X).unop = 𝟙 _ := by
  rw [← unop_comp, hom_inv_id_app, unop_id]

end

end Iso

namespace NatIso

variable {D : Type u₂} [Category.{v₂} D]
variable {F G : C ⥤ D}

/-- The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a natural
isomorphism between the original functors `F ≅ G`. -/
@[simps]
/-
**CategoryTheory.NatIso.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatIso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → {F G : CategoryT
heory.Functor C D} → (F ≅ G) → (G.op ≅ F.op)
参数：F ≅ G；G.op ≅ F.op。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between opposite functors `G.op ≅ F.op` induced by a nat
ural
isomorphism between the original functors `F ≅ G`.
-/
protected def op (α : F ≅ G) : G.op ≅ F.op where
  hom := NatTrans.op α.hom
  inv := NatTrans.op α.inv
  hom_inv_id := by ext; dsimp; rw [← op_comp]; rw [α.inv_hom_id_app]; rfl
  inv_hom_id := by ext; dsimp; rw [← op_comp]; rw [α.hom_inv_id_app]; rfl

@[simp]
/-
**CategoryTheory.NatIso.op_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatIso
`。
形式化陈述：op_refl : NatIso.op (Iso.refl F) = Iso.refl F.op
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_refl : NatIso.op (Iso.refl F) = Iso.refl F.op := rfl

@[simp]
/-
**CategoryTheory.NatIso.op_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatIs
o`。
形式化陈述：op_trans {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) : NatIso.op (α ≪≫ β) = NatIso
.op β ≪≫ NatIso.op α
参数：α : F ≅ G；β : G ≅ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_trans {H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) :
    NatIso.op (α ≪≫ β) = NatIso.op β ≪≫ NatIso.op α :=
  rfl

@[simp]
/-
**CategoryTheory.NatIso.op_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatIso
`。
形式化陈述：op_symm (α : F ≅ G) : NatIso.op α.symm = (NatIso.op α).symm
参数：α : F ≅ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem op_symm (α : F ≅ G) : NatIso.op α.symm = (NatIso.op α).symm := rfl

/-- The natural isomorphism between functors `G ≅ F` induced by a natural isomorphism
between the opposite functors `F.op ≅ G.op`. -/
@[simps]
/-
**CategoryTheory.NatIso.removeOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatIs
o`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → {F G : CategoryT
heory.Functor C D} → (F.op ≅ G.op) → (G ≅ F)
参数：F.op ≅ G.op；G ≅ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between functors `G ≅ F` induced by a natural isomorphis
m
between the opposite functors `F.op ≅ G.op`.
-/
protected def removeOp (α : F.op ≅ G.op) : G ≅ F where
  hom := NatTrans.removeOp α.hom
  inv := NatTrans.removeOp α.inv

/-- The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural isomorphism
between the original functors `F ≅ G`. -/
@[simps]
/-
**CategoryTheory.NatIso.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatIso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {F G : C
ategoryTheory.Functor Cᵒᵖ Dᵒᵖ} → (F ≅ G) → (G.unop ≅ F.unop)
参数：F ≅ G；G.unop ≅ F.unop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between functors `G.unop ≅ F.unop` induced by a natural 
isomorphism
between the original functors `F ≅ G`.
-/
protected def unop {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : G.unop ≅ F.unop where
  hom := NatTrans.unop α.hom
  inv := NatTrans.unop α.inv

@[simp]
/-
**CategoryTheory.NatIso.unop_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatI
so`。
形式化陈述：unop_refl (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatIso.unop (Iso.refl F) = Iso.refl F.unop
参数：F : Cᵒᵖ ⥤ Dᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_refl (F : Cᵒᵖ ⥤ Dᵒᵖ) : NatIso.unop (Iso.refl F) = Iso.refl F.unop := rfl

@[simp]
/-
**CategoryTheory.NatIso.unop_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Nat
Iso`。
形式化陈述：unop_trans {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) (β : G ≅ H) : NatIso.unop (α ≪≫
 β) = NatIso.unop β ≪≫ NatIso.unop α
参数：α : F ≅ G；β : G ≅ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_trans {F G H : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) (β : G ≅ H) :
    NatIso.unop (α ≪≫ β) = NatIso.unop β ≪≫ NatIso.unop α :=
  rfl

@[simp]
/-
**CategoryTheory.NatIso.unop_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatI
so`。
形式化陈述：unop_symm {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : NatIso.unop α.symm = (NatIso.uno
p α).symm
参数：α : F ≅ G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unop_symm {F G : Cᵒᵖ ⥤ Dᵒᵖ} (α : F ≅ G) : NatIso.unop α.symm = (NatIso.unop α).symm := rfl
/-
**CategoryTheory.NatIso.op_isoWhiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.NatIso`。
形式化陈述：op_isoWhiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ≅ G) : Nat
Iso.op (isoWhiskerRight α H) = (Functor.opComp _ _) ≪≫ isoWhiskerRight (NatIso.o
p α) H.op ≪≫ (Functor.opComp _ _).symm
参数：α : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.opComp_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_isoWhiskerRight {E : Type*} [Category* E] {H : D ⥤ E} (α : F ≅ G) :
    NatIso.op (isoWhiskerRight α H) =
    (Functor.opComp _ _) ≪≫ isoWhiskerRight (NatIso.op α) H.op ≪≫ (Functor.opComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.op_isoWhiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.NatIso`。
形式化陈述：op_isoWhiskerLeft {E : Type*} [Category* E] {H : E ⥤ C} (α : F ≅ G) : NatI
so.op (isoWhiskerLeft H α) = (Functor.opComp _ _) ≪≫ isoWhiskerLeft H.op (NatIso
.op α) ≪≫ (Functor.opComp _ _).symm
参数：α : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.opComp_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_isoWhiskerLeft {E : Type*} [Category* E] {H : E ⥤ C} (α : F ≅ G) :
    NatIso.op (isoWhiskerLeft H α) =
    (Functor.opComp _ _) ≪≫ isoWhiskerLeft H.op (NatIso.op α) ≪≫ (Functor.opComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.unop_whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.NatIso`。
形式化陈述：unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ E
ᵒᵖ} (α : F ≅ G) : NatIso.unop (isoWhiskerRight α H) = (Functor.unopComp _ _) ≪≫ 
isoWhiskerRight (NatIso.unop α) H.unop ≪≫ (Functor.unopComp _ _).symm
参数：α : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.unop_hom`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.unopComp_hom_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_whiskerRight {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Dᵒᵖ ⥤ Eᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerRight α H) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerRight (NatIso.unop α) H.unop ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.unop_whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.NatIso`。
形式化陈述：unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒ
ᵖ} (α : F ≅ G) : NatIso.unop (isoWhiskerLeft H α) = (Functor.unopComp _ _) ≪≫ is
oWhiskerLeft H.unop (NatIso.unop α) ≪≫ (Functor.unopComp _ _).symm
参数：α : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.unop_hom`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.unopComp_hom_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_whiskerLeft {F G : Cᵒᵖ ⥤ Dᵒᵖ} {E : Type*} [Category* E] {H : Eᵒᵖ ⥤ Cᵒᵖ} (α : F ≅ G) :
    NatIso.unop (isoWhiskerLeft H α) =
    (Functor.unopComp _ _) ≪≫ isoWhiskerLeft H.unop (NatIso.unop α) ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.op_leftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：op_leftUnitor : NatIso.op F.leftUnitor = F.op.leftUnitor.symm ≪≫ isoWhiske
rRight (Functor.opId C).symm F.op ≪≫ (Functor.opComp _ _).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.opId_inv_app`：∀ (C : Type u₁) [inst : CategoryThe
ory.Category.{v₁, u₁} C] (X : Cᵒᵖ),   (CategoryTheory.Functor.opId C).inv.app X 
= CategoryTheory.Category…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_leftUnitor :
    NatIso.op F.leftUnitor =
    F.op.leftUnitor.symm ≪≫
      isoWhiskerRight (Functor.opId C).symm F.op ≪≫
      (Functor.opComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.op_rightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.NatIso`。
形式化陈述：op_rightUnitor : NatIso.op F.rightUnitor = F.op.rightUnitor.symm ≪≫ isoWhi
skerLeft F.op (Functor.opId D).symm ≪≫ (Functor.opComp _ _).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.opId_inv_app`：∀ (C : Type u₁) [inst : CategoryThe
ory.Category.{v₁, u₁} C] (X : Cᵒᵖ),   (CategoryTheory.Functor.opId C).inv.app X 
= CategoryTheory.Category…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_rightUnitor :
    NatIso.op F.rightUnitor =
    F.op.rightUnitor.symm ≪≫
      isoWhiskerLeft F.op (Functor.opId D).symm ≪≫
      (Functor.opComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.op_associator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
NatIso`。
形式化陈述：op_associator {E E' : Type*} [Category* E] [Category* E'] {F : C ⥤ D} {G :
 D ⥤ E} {H : E ⥤ E'} : NatIso.op (Functor.associator F G H) = Functor.opComp _ _
 ≪≫ isoWhiskerLeft F.op (Functor.opComp _ _) ≪≫ (Functor.associator F.op G.op H.
op).symm ≪≫ isoWhiskerRight (Functor.opComp _ _).symm H.op ≪≫ (Functor.opComp _ 
_).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
{F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.opComp_hom_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.opComp_inv_app`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_associator {E E' : Type*} [Category* E] [Category* E']
    {F : C ⥤ D} {G : D ⥤ E} {H : E ⥤ E'} :
    NatIso.op (Functor.associator F G H) =
      Functor.opComp _ _ ≪≫ isoWhiskerLeft F.op (Functor.opComp _ _) ≪≫
        (Functor.associator F.op G.op H.op).symm ≪≫
        isoWhiskerRight (Functor.opComp _ _).symm H.op ≪≫ (Functor.opComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.unop_leftUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.NatIso`。
形式化陈述：unop_leftUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} : NatIso.unop F.leftUnitor = F.unop.leftUn
itor.symm ≪≫ isoWhiskerRight (Functor.unopId C).symm F.unop ≪≫ (Functor.unopComp
 _ _).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.unop_hom`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.unopId_inv_app`：∀ (C : Type u₁) [inst : CategoryT
heory.Category.{v₁, u₁} C] (X : C),   (CategoryTheory.Functor.unopId C).inv.app 
X = CategoryTheory.Category…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_leftUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} :
    NatIso.unop F.leftUnitor =
    F.unop.leftUnitor.symm ≪≫
      isoWhiskerRight (Functor.unopId C).symm F.unop ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.unop_rightUnitor** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.NatIso`。
形式化陈述：unop_rightUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} : NatIso.unop F.rightUnitor = F.unop.righ
tUnitor.symm ≪≫ isoWhiskerLeft F.unop (Functor.unopId D).symm ≪≫ (Functor.unopCo
mp _ _).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.unop_hom`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.unopId_inv_app`：∀ (C : Type u₁) [inst : CategoryT
heory.Category.{v₁, u₁} C] (X : C),   (CategoryTheory.Functor.unopId C).inv.app 
X = CategoryTheory.Category…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_rightUnitor {F : Cᵒᵖ ⥤ Dᵒᵖ} :
    NatIso.unop F.rightUnitor =
    F.unop.rightUnitor.symm ≪≫
      isoWhiskerLeft F.unop (Functor.unopId D).symm ≪≫
      (Functor.unopComp _ _).symm := by
  cat_disch
/-
**CategoryTheory.NatIso.unop_associator** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.NatIso`。
形式化陈述：unop_associator {E E' : Type*} [Category* E] [Category* E'] {F : Cᵒᵖ ⥤ Dᵒᵖ
} {G : Dᵒᵖ ⥤ Eᵒᵖ} {H : Eᵒᵖ ⥤ E'ᵒᵖ} : NatIso.unop (Functor.associator F G H) = Fu
nctor.unopComp _ _ ≪≫ isoWhiskerLeft F.unop (Functor.unopComp _ _) ≪≫ (Functor.a
ssociator F.unop G.unop H.unop).symm ≪≫ isoWhiskerRight (Functor.unopComp _ _).s
ymm H.unop ≪≫ (Functor.unopComp _ _).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatIso.unop_hom`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D] 
  {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.unopComp_hom_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.unopComp_inv_app`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {E : Type u_1} [in…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unop_associator {E E' : Type*} [Category* E] [Category* E']
    {F : Cᵒᵖ ⥤ Dᵒᵖ} {G : Dᵒᵖ ⥤ Eᵒᵖ} {H : Eᵒᵖ ⥤ E'ᵒᵖ} :
    NatIso.unop (Functor.associator F G H) =
      Functor.unopComp _ _ ≪≫ isoWhiskerLeft F.unop (Functor.unopComp _ _) ≪≫
        (Functor.associator F.unop G.unop H.unop).symm ≪≫
        isoWhiskerRight (Functor.unopComp _ _).symm H.unop ≪≫ (Functor.unopComp _ _).symm := by
  cat_disch

end NatIso

section

variable {D : Type*} [Category* D] {F G : C ⥤ D}

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : F ⟶ G) [IsIso α] :
    IsIso (NatTrans.op α) :=
  (NatIso.op (asIso α)).isIso_hom

@[push]
/-
**CategoryTheory.inv_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：inv_op (α : F ⟶ G) [IsIso α] : inv (NatTrans.op α) = NatTrans.op (inv α)
参数：α : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.instIsIsoFunctorOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u_1}   [inst_1 : CategoryTheory.Categor
y.{v_1, u_1} D] {F G : Category…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_op (α : F ⟶ G) [IsIso α] :
    inv (NatTrans.op α) = NatTrans.op (inv α) :=
  IsIso.inv_eq_of_hom_inv_id (by simp [← NatTrans.op_comp])

end

namespace Equivalence

variable {D : Type u₂} [Category.{v₂} D]

/-- An equivalence between categories gives an equivalence between the opposite categories.
-/
@[simps]
/-
**CategoryTheory.Equivalence.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equiva
lence`。
形式化陈述：op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ where functor
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between categories gives an equivalence between the opposite cate
gories.
-/
def op (e : C ≌ D) : Cᵒᵖ ≌ Dᵒᵖ where
  functor := e.functor.op
  inverse := e.inverse.op
  unitIso := (NatIso.op e.unitIso).symm
  counitIso := (NatIso.op e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.unop_inj
    simp

/-- An equivalence between opposite categories gives an equivalence between the original categories.
-/
@[simps]
/-
**CategoryTheory.Equivalence.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Equi
valence`。
形式化陈述：unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D where functor
参数：e : Cᵒᵖ ≌ Dᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between opposite categories gives an equivalence between the orig
inal categories.
-/
def unop (e : Cᵒᵖ ≌ Dᵒᵖ) : C ≌ D where
  functor := e.functor.unop
  inverse := e.inverse.unop
  unitIso := (NatIso.unop e.unitIso).symm
  counitIso := (NatIso.unop e.counitIso).symm
  functor_unitIso_comp X := by
    apply Quiver.Hom.op_inj
    simp

/-- An equivalence between `C` and `Dᵒᵖ` gives an equivalence between `Cᵒᵖ` and `D`. -/
/-
**CategoryTheory.Equivalence.leftOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Eq
uivalence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (C ≌ Dᵒᵖ) → (Cᵒᵖ ≌ D)
参数：C ≌ Dᵒᵖ；Cᵒᵖ ≌ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between `C` and `Dᵒᵖ` gives an equivalence between `Cᵒᵖ` and `D`.
-/
@[simps!] def leftOp (e : C ≌ Dᵒᵖ) : Cᵒᵖ ≌ D := e.op.trans (opOpEquivalence D)

/-- An equivalence between `Cᵒᵖ` and `D` gives an equivalence between `C` and `Dᵒᵖ`. -/
/-
**CategoryTheory.Equivalence.rightOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.E
quivalence`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → (Cᵒᵖ ≌ D) → (C ≌ Dᵒᵖ)
参数：Cᵒᵖ ≌ D；C ≌ Dᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between `Cᵒᵖ` and `D` gives an equivalence between `C` and `Dᵒᵖ`.
-/
@[simps!] def rightOp (e : Cᵒᵖ ≌ D) : C ≌ Dᵒᵖ := (opOpEquivalence C).symm.trans e.op

end Equivalence

/-- The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful for building
adjunctions.
Note that this (definitionally) gives variants
```
def opEquiv' (A : C) (B : Cᵒᵖ) : (Opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
  opEquiv _ _

def opEquiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ Opposite.op B) ≃ (B ⟶ A.unop) :=
  opEquiv _ _

def opEquiv''' (A B : C) : (Opposite.op A ⟶ Opposite.op B) ≃ (B ⟶ A) :=
  opEquiv _ _
```
-/
@[to_dual self, simps (attr := to_dual self)]
/-
**CategoryTheory.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：opEquiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) where toFun f
参数：A B : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between arrows of the form `A ⟶ B` and `B.unop ⟶ A.unop`. Useful
 for building
adjunctions.
Note that this (definitionally) gives variants
```
def opEquiv' (A : C) (B : Cᵒᵖ) : (Opposite.op A ⟶ B) ≃ (B.unop ⟶ A) :=
  opEquiv _ _

def opEquiv'' (A : Cᵒᵖ) (B : C) : (A ⟶ Opposite.op B) ≃ (B ⟶ A.unop) :=
  opEquiv _ _

def opEquiv''' (A B : C) : (Opposite.op A ⟶ Opposite.op B) ≃ (B ⟶ A) :=
  opEquiv _ _
```
-/
def opEquiv (A B : Cᵒᵖ) : (A ⟶ B) ≃ (B.unop ⟶ A.unop) where
  toFun f := f.unop
  invFun g := g.op

@[to_dual self]
/-
**CategoryTheory.subsingleton_of_unop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`
。
形式化陈述：subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsin
gleton (A ⟶ B)
参数：A B : Cᵒᵖ；unop B ⟶ unop A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
-/
instance subsingleton_of_unop (A B : Cᵒᵖ) [Subsingleton (unop B ⟶ unop A)] : Subsingleton (A ⟶ B) :=
  (opEquiv A B).subsingleton

@[to_dual self]
/-
**CategoryTheory.decidableEqOfUnop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：decidableEqOfUnop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableE
q (A ⟶ B)
参数：A B : Cᵒᵖ；unop B ⟶ unop A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableEqOfUnop (A B : Cᵒᵖ) [DecidableEq (unop B ⟶ unop A)] : DecidableEq (A ⟶ B) :=
  (opEquiv A B).decidableEq

/-- The equivalence between isomorphisms of the form `A ≅ B` and `B.unop ≅ A.unop`.

Note this is definitionally the same as the other three variants:
* `(Opposite.op A ≅ B) ≃ (B.unop ≅ A)`
* `(A ≅ Opposite.op B) ≃ (B ≅ A.unop)`
* `(Opposite.op A ≅ Opposite.op B) ≃ (B ≅ A)`
-/
@[simps]
/-
**CategoryTheory.isoOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：isoOpEquiv (A B : Cᵒᵖ) : (A ≅ B) ≃ (B.unop ≅ A.unop) where toFun f
参数：A B : Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between isomorphisms of the form `A ≅ B` and `B.unop ≅ A.unop`.

Note this is definitionally the same as the other three variants:
* `(Opposite.op A ≅ B) ≃ (B.unop ≅ A)`
* `(A ≅ Opposite.op B) ≃ (B ≅ A.unop)`
* `(Opposite.op A ≅ Opposite.op B) ≃ (B ≅ A)`
-/
def isoOpEquiv (A B : Cᵒᵖ) : (A ≅ B) ≃ (B.unop ≅ A.unop) where
  toFun f := f.unop
  invFun g := g.op

namespace Functor

variable (C)
variable (D : Type u₂) [Category.{v₂} D]

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of functor categories induced by `op` and `unop`.
-/
@[simps]
/-
**CategoryTheory.Functor.opUnopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：opUnopEquiv : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of functor categories induced by `op` and `unop`.
-/
def opUnopEquiv : (C ⥤ D)ᵒᵖ ≌ Cᵒᵖ ⥤ Dᵒᵖ where
  functor := opHom _ _
  inverse := opInv _ _
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.opUnopIso.op)
      (by
        intro F G f
        dsimp [opUnopIso]
        rw [show f = f.unop.op by simp, ← op_comp, ← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents fun F => F.unopOpIso

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of functor categories induced by `leftOp` and `rightOp`.
-/
@[simps!]
/-
**CategoryTheory.Functor.leftOpRightOpEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：leftOpRightOpEquiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of functor categories induced by `leftOp` and `rightOp`.
-/
def leftOpRightOpEquiv : (Cᵒᵖ ⥤ D)ᵒᵖ ≌ C ⥤ Dᵒᵖ where
  functor :=
    { obj := fun F => F.unop.rightOp
      map := fun η => NatTrans.rightOp η.unop }
  inverse :=
    { obj := fun F => op F.leftOp
      map := fun η => η.leftOp.op }
  unitIso :=
    NatIso.ofComponents (fun F => F.unop.rightOpLeftOpIso.op)
      (by
        intro F G η
        dsimp
        rw [show η = η.unop.op by simp, ← op_comp, ← op_comp]
        congr 1
        cat_disch)
  counitIso := NatIso.ofComponents fun F => F.leftOpRightOpIso
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ D} [EssSurj F] : EssSurj F.op where
  mem_essImage X := ⟨op _, ⟨(F.objObjPreimageIso X.unop).op.symm⟩⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : Cᵒᵖ ⥤ D} [EssSurj F] : EssSurj F.rightOp where
  mem_essImage X := ⟨_, ⟨(F.objObjPreimageIso X.unop).op.symm⟩⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ Dᵒᵖ} [EssSurj F] : EssSurj F.leftOp where
  mem_essImage X := ⟨op _, ⟨(F.objObjPreimageIso (op X)).unop.symm⟩⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ D} [IsEquivalence F] : IsEquivalence F.op where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : Cᵒᵖ ⥤ D} [IsEquivalence F] : IsEquivalence F.rightOp where
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {F : C ⥤ Dᵒᵖ} [IsEquivalence F] : IsEquivalence F.leftOp where

end Functor

end CategoryTheory

