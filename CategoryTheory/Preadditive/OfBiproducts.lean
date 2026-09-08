/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.GroupTheory.EckmannHilton
public import Mathlib.Tactic.CategoryTheory.Reassoc
/-!
# Constructing a semiadditive structure from binary biproducts

We show that any category with zero morphisms and binary biproducts is enriched over the category
of commutative monoids.

-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.SemiadditiveOfBinaryBiproducts

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

section

variable (X Y : C)

/-- `f +ₗ g` is the composite `X ⟶ Y ⊞ Y ⟶ Y`, where the first map is `(f, g)` and the second map
is `(𝟙 𝟙)`. -/
@[simp]
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.leftAdd** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：leftAdd (f g : X ⟶ Y) : X ⟶ Y
参数：f g : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…

--- 原说明 ---
`f +ₗ g` is the composite `X ⟶ Y ⊞ Y ⟶ Y`, where the first map is `(f, g)` and t
he second map
is `(𝟙 𝟙)`.
-/
def leftAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)

/-- `f +ᵣ g` is the composite `X ⟶ X ⊞ X ⟶ Y`, where the first map is `(𝟙, 𝟙)` and the second map
is `(f g)`. -/
@[simp]
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.rightAdd** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：rightAdd (f g : X ⟶ Y) : X ⟶ Y
参数：f g : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…

--- 原说明 ---
`f +ᵣ g` is the composite `X ⟶ X ⊞ X ⟶ Y`, where the first map is `(𝟙, 𝟙)` and t
he second map
is `(f g)`.
-/
def rightAdd (f g : X ⟶ Y) : X ⟶ Y :=
  biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g

local infixr:65 " +ₗ " => leftAdd X Y

local infixr:65 " +ᵣ " => rightAdd X Y
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.isUnital_leftAdd** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：isUnital_leftAdd : EckmannHilton.IsUnital (· +ₗ ·) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem isUnital_leftAdd : EckmannHilton.IsUnital (· +ₗ ·) 0 := by
  have hr : ∀ f : X ⟶ Y, biprod.lift (0 : X ⟶ Y) f = f ≫ biprod.inr := by
    intro f
    ext
    · simp
    · simp [Category.assoc]
  have hl : ∀ f : X ⟶ Y, biprod.lift f (0 : X ⟶ Y) = f ≫ biprod.inl := by
    intro f
    ext
    · simp
    · simp [biprod.lift_snd, Category.assoc, comp_zero]
  exact {
    left_id := fun f => by simp [hr f, leftAdd, Category.assoc, Category.comp_id, biprod.inr_desc],
    right_id := fun f => by simp [hl f, leftAdd, Category.assoc, Category.comp_id, biprod.inl_desc]
  }
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.isUnital_rightAdd** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：isUnital_rightAdd : EckmannHilton.IsUnital (· +ᵣ ·) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst_assoc`：∀ {C : Type uC} [inst 
: CategoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMo
rphisms C]   {P Q : C} (self : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
-/
theorem isUnital_rightAdd : EckmannHilton.IsUnital (· +ᵣ ·) 0 := by
  have h₂ : ∀ f : X ⟶ Y, biprod.desc (0 : X ⟶ Y) f = biprod.snd ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_snd_assoc]
  have h₁ : ∀ f : X ⟶ Y, biprod.desc f (0 : X ⟶ Y) = biprod.fst ≫ f := by
    intro f
    ext
    · simp
    · simp only [biprod.inr_desc, BinaryBicone.inr_fst_assoc, zero_comp]
  exact {
    left_id := fun f => by simp [h₂ f, rightAdd, biprod.lift_snd_assoc, Category.id_comp],
    right_id := fun f => by simp [h₁ f, rightAdd, biprod.lift_fst_assoc, Category.id_comp]
  }
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.distrib** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：distrib (f g h k : X ⟶ Y) : (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k
参数：f g h k : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.SemiadditiveOfBinaryBiproducts.leftAdd.eq_1`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   [inst_2 : CategoryTheory.Limi…
· 使用定理 `CategoryTheory.SemiadditiveOfBinaryBiproducts.rightAdd.eq_1`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroMorphisms C]   [inst_2 : CategoryTheory.Limi…
-/
theorem distrib (f g h k : X ⟶ Y) : (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k := by
  let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift (biprod.desc f g) (biprod.desc h k)
  have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by ext <;> simp [diag]
  have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by ext <;> simp [diag]
  have h₁ : biprod.lift (f +ᵣ g) (h +ᵣ k) = biprod.lift (𝟙 X) (𝟙 X) ≫ diag := by
    ext <;> cat_disch
  have h₂ : diag ≫ biprod.desc (𝟙 Y) (𝟙 Y) = biprod.desc (f +ₗ h) (g +ₗ k) := by
    ext <;> simp [reassoc_of% hd₁, reassoc_of% hd₂]
  rw [leftAdd, h₁, Category.assoc, h₂, rightAdd]

/-- In a category with binary biproducts, the morphisms form a commutative monoid. -/
@[instance_reducible]
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.addCommMonoidHomOfHasBinaryBipro
ducts** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：addCommMonoidHomOfHasBinaryBiproducts : AddCommMonoid (X ⟶ Y) where add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with binary biproducts, the morphisms form a commutative monoid.
-/
def addCommMonoidHomOfHasBinaryBiproducts : AddCommMonoid (X ⟶ Y) where
  add := (· +ᵣ ·)
  add_assoc :=
    (EckmannHilton.mul_assoc (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).assoc
  zero_add := (isUnital_rightAdd X Y).left_id
  add_zero := (isUnital_rightAdd X Y).right_id
  add_comm :=
    (EckmannHilton.mul_comm (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).comm
  nsmul := letI : Add (X ⟶ Y) := ⟨(· +ᵣ ·)⟩; nsmulRec

end

section

variable {X Y Z : C}

attribute [local instance] addCommMonoidHomOfHasBinaryBiproducts

/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.add_eq_right_addition** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：add_eq_right_addition (f g : X ⟶ Y) : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ bi
prod.desc f g
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_eq_right_addition (f g : X ⟶ Y) : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g :=
  rfl
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.add_eq_left_addition** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：add_eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc
 (𝟙 Y) (𝟙 Y)
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EckmannHilton.mul`：mul : m₁ = m₂
· 使用定理 `CategoryTheory.SemiadditiveOfBinaryBiproducts.isUnital_leftAdd`：isUnital
_leftAdd : EckmannHilton.IsUnital (· +ₗ ·) 0
· 使用定理 `CategoryTheory.SemiadditiveOfBinaryBiproducts.isUnital_rightAdd`：isUnita
l_rightAdd : EckmannHilton.IsUnital (· +ᵣ ·) 0
· 使用定理 `CategoryTheory.SemiadditiveOfBinaryBiproducts.distrib`：distrib (f g h k 
: X ⟶ Y) : (f +ᵣ g) +ₗ h +ᵣ k = (f +ₗ h) +ᵣ g +ₗ k
-/
theorem add_eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) :=
  congr_fun₂ (EckmannHilton.mul (isUnital_leftAdd X Y) (isUnital_rightAdd X Y) (distrib X Y)).symm f
    g
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.add_comp** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：add_comp (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h
参数：f g : X ⟶ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext'`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inl_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc_assoc`：∀ {C : Type uC} [inst : Cat
egoryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   {W X Y : C} [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.biprod.inr_desc`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem add_comp (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h := by
  simp only [add_eq_right_addition, Category.assoc]
  congr
  ext <;> simp
/-
**CategoryTheory.SemiadditiveOfBinaryBiproducts.comp_add** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SemiadditiveOfBinaryBiproducts`。
形式化陈述：comp_add (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h
参数：f : X ⟶ Y；g h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.SemiadditiveOfBinaryBiproducts.add_eq_left_addition`：add_
eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 
Y)
· 使用定理 `CategoryTheory.Limits.biprod.hom_ext`：∀ {C : Type uC} [inst : CategoryTh
eory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]  
 {X Y Z : C} [inst_2 : Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.biprod.lift_fst`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.biprod.lift_snd`：∀ {C : Type uC} [inst : CategoryT
heory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
  {W X Y : C} [inst_2 : Cat…
-/
theorem comp_add (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h := by
  simp only [add_eq_left_addition, ← Category.assoc]
  congr
  ext <;> simp

end

end CategoryTheory.SemiadditiveOfBinaryBiproducts

