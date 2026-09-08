/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Homology of preadditive categories

In this file, it is shown that if `C` is a preadditive category, then
`ShortComplex C` is a preadditive category.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

namespace ShortComplex

variable {S₁ S₂ S₃ : ShortComplex C}

attribute [local simp] Hom.comm₁₂ Hom.comm₂₃

/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (S₁ ⟶ S₂) where
  add φ φ' :=
    { τ₁ := φ.τ₁ + φ'.τ₁
      τ₂ := φ.τ₂ + φ'.τ₂
      τ₃ := φ.τ₃ + φ'.τ₃ }
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (S₁ ⟶ S₂) where
  sub φ φ' :=
    { τ₁ := φ.τ₁ - φ'.τ₁
      τ₂ := φ.τ₂ - φ'.τ₂
      τ₃ := φ.τ₃ - φ'.τ₃ }
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (S₁ ⟶ S₂) where
  neg φ :=
    { τ₁ := -φ.τ₁
      τ₂ := -φ.τ₂
      τ₃ := -φ.τ₃ }
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (S₁ ⟶ S₂) where
  add_assoc := fun a b c => by ext <;> apply add_assoc
  add_zero := fun a => by ext <;> apply add_zero
  zero_add := fun a => by ext <;> apply zero_add
  neg_add_cancel := fun a => by ext <;> apply neg_add_cancel
  add_comm := fun a b => by ext <;> apply add_comm
  sub_eq_add_neg := fun a b => by ext <;> apply sub_eq_add_neg
  nsmul := nsmulRec
  zsmul := zsmulRec
/-
**CategoryTheory.ShortComplex.add_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₁ = φ.τ₁ + φ'.τ₁ := rfl
/-
**CategoryTheory.ShortComplex.add_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₂ = φ.τ₂ + φ'.τ₂ := rfl
/-
**CategoryTheory.ShortComplex.add_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ + φ').τ₃ = φ.τ₃ + φ'.τ₃ := rfl
/-
**CategoryTheory.ShortComplex.sub_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_τ₁ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₁ = φ.τ₁ - φ'.τ₁ := rfl
/-
**CategoryTheory.ShortComplex.sub_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_τ₂ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₂ = φ.τ₂ - φ'.τ₂ := rfl
/-
**CategoryTheory.ShortComplex.sub_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sub_τ₃ (φ φ' : S₁ ⟶ S₂) : (φ - φ').τ₃ = φ.τ₃ - φ'.τ₃ := rfl
/-
**CategoryTheory.ShortComplex.neg_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_τ₁ (φ : S₁ ⟶ S₂) : (-φ).τ₁ = -φ.τ₁ := rfl
/-
**CategoryTheory.ShortComplex.neg_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_τ₂ (φ : S₁ ⟶ S₂) : (-φ).τ₂ = -φ.τ₂ := rfl
/-
**CategoryTheory.ShortComplex.neg_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sho
rtComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_τ₃ (φ : S₁ ⟶ S₂) : (-φ).τ₃ = -φ.τ₃ := rfl
/-
**CategoryTheory.ShortComplex.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.ShortCo
mplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive (ShortComplex C) where

section LeftHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}

namespace LeftHomologyMapData

variable (γ : LeftHomologyMapData φ h₁ h₂) (γ' : LeftHomologyMapData φ' h₁ h₂)

/-- Given a left homology map data for morphism `φ`, this is the induced left homology
map data for `-φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.neg** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：neg : LeftHomologyMapData (-φ) h₁ h₂ where φK
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a left homology map data for morphism `φ`, this is the induced left homolo
gy
map data for `-φ`.
-/
def neg : LeftHomologyMapData (-φ) h₁ h₂ where
  φK := -γ.φK
  φH := -γ.φH

/-- Given left homology map data for morphisms `φ` and `φ'`, this is
the induced left homology map data for `φ + φ'`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.add** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：add : LeftHomologyMapData (φ + φ') h₁ h₂ where φK
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given left homology map data for morphisms `φ` and `φ'`, this is
the induced left homology map data for `φ + φ'`.
-/
def add : LeftHomologyMapData (φ + φ') h₁ h₂ where
  φK := γ.φK + γ'.φK
  φH := γ.φH + γ'.φH

end LeftHomologyMapData

variable (h₁ h₂)

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ : S₁ ⟶
 S₂} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.Sho
rtComplex.leftHomologyMap' (-φ) h₁ h₂ = -CategoryTheory.ShortComplex.leftHomolog
yMap' φ h₁ h₂
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；-φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.neg_φH`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftHomologyMap'_neg :
    leftHomologyMap' (-φ) h₁ h₂ = -leftHomologyMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ.neg.leftHomologyMap'_eq, LeftHomologyMapData.neg_φH]

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ : S₁ ⟶
 S₂} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.Sho
rtComplex.cyclesMap' (-φ) h₁ h₂ = -CategoryTheory.ShortComplex.cyclesMap' φ h₁ h
₂
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；-φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.neg_φK`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesMap'_neg :
    cyclesMap' (-φ) h₁ h₂ = -cyclesMap' φ h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ.neg.cyclesMap'_eq, LeftHomologyMapData.neg_φK]

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_add** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.
ShortComplex.leftHomologyMap' (φ + φ') h₁ h₂ =     CategoryTheory.ShortComplex.l
eftHomologyMap' φ h₁ h₂ + CategoryTheory.ShortComplex.leftHomologyMap' φ' h₁ h₂
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；φ + φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.add_φH`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftHomologyMap'_add :
    leftHomologyMap' (φ + φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ +
      leftHomologyMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.leftHomologyMap'_eq, γ'.leftHomologyMap'_eq,
    (γ.add γ').leftHomologyMap'_eq, LeftHomologyMapData.add_φH]

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap'_add** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.
ShortComplex.cyclesMap' (φ + φ') h₁ h₂ =     CategoryTheory.ShortComplex.cyclesM
ap' φ h₁ h₂ + CategoryTheory.ShortComplex.cyclesMap' φ' h₁ h₂
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；φ + φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.cyclesMap'_eq`：∀ {C : Ty
pe u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.L
imits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.add_φK`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesMap'_add :
    cyclesMap' (φ + φ') h₁ h₂ = cyclesMap' φ h₁ h₂ +
      cyclesMap' φ' h₁ h₂ := by
  have γ : LeftHomologyMapData φ h₁ h₂ := default
  have γ' : LeftHomologyMapData φ' h₁ h₂ := default
  simp only [γ.cyclesMap'_eq, γ'.cyclesMap'_eq,
    (γ.add γ').cyclesMap'_eq, LeftHomologyMapData.add_φK]

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.
ShortComplex.leftHomologyMap' (φ - φ') h₁ h₂ =     CategoryTheory.ShortComplex.l
eftHomologyMap' φ h₁ h₂ - CategoryTheory.ShortComplex.leftHomologyMap' φ' h₁ h₂
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；φ - φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_add`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_neg`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftHomologyMap'_sub :
    leftHomologyMap' (φ - φ') h₁ h₂ = leftHomologyMap' φ h₁ h₂ -
      leftHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, leftHomologyMap'_add, leftHomologyMap'_neg]

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.
ShortComplex.cyclesMap' (φ - φ') h₁ h₂ =     CategoryTheory.ShortComplex.cyclesM
ap' φ h₁ h₂ - CategoryTheory.ShortComplex.cyclesMap' φ' h₁ h₂
参数：h₁ : S₁.LeftHomologyData；h₂ : S₂.LeftHomologyData；φ - φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_add`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_neg`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cyclesMap'_sub :
    cyclesMap' (φ - φ') h₁ h₂ = cyclesMap' φ h₁ h₂ -
      cyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, cyclesMap'_add, cyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasLeftHomology] [S₂.HasLeftHomology]

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_neg : leftHomologyMap (-φ) = -leftHomologyMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_neg`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma leftHomologyMap_neg : leftHomologyMap (-φ) = -leftHomologyMap φ :=
  leftHomologyMap'_neg _ _

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：cyclesMap_neg : cyclesMap (-φ) = -cyclesMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_neg`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
-/
lemma cyclesMap_neg : cyclesMap (-φ) = -cyclesMap φ :=
  cyclesMap'_neg _ _

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_add** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_add : leftHomologyMap (φ + φ') = leftHomologyMap φ + leftH
omologyMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_add`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma leftHomologyMap_add : leftHomologyMap (φ + φ') = leftHomologyMap φ + leftHomologyMap φ' :=
  leftHomologyMap'_add _ _

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：cyclesMap_add : cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_add`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
-/
lemma cyclesMap_add : cyclesMap (φ + φ') = cyclesMap φ + cyclesMap φ' :=
  cyclesMap'_add _ _

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_sub : leftHomologyMap (φ - φ') = leftHomologyMap φ - leftH
omologyMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_sub`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma leftHomologyMap_sub : leftHomologyMap (φ - φ') = leftHomologyMap φ - leftHomologyMap φ' :=
  leftHomologyMap'_sub _ _

@[simp]
/-
**CategoryTheory.ShortComplex.cyclesMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：cyclesMap_sub : cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.cyclesMap'_sub`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
-/
lemma cyclesMap_sub : cyclesMap (φ - φ') = cyclesMap φ - cyclesMap φ' :=
  cyclesMap'_sub _ _

end

/-
**CategoryTheory.ShortComplex.leftHomologyFunctor_additive** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasKernels C] [in
st_3 : CategoryTheory.Limits.HasCokernels C],   (CategoryTheory.ShortComplex.lef
tHomologyFunctor C).Additive
参数：CategoryTheory.ShortComplex.leftHomologyFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyFunctor_map`：∀ (C : Type u_1) [i
nst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.leftHomologyMap_add`：leftHomologyMap_add : l
eftHomologyMap (φ + φ') = leftHomologyMap φ + leftHomologyMap φ'
-/
instance leftHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
    (leftHomologyFunctor C).Additive where
/-
**CategoryTheory.ShortComplex.cyclesFunctor_additive** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasKernels C] [in
st_3 : CategoryTheory.Limits.HasCokernels C],   (CategoryTheory.ShortComplex.cyc
lesFunctor C).Additive
参数：CategoryTheory.ShortComplex.cyclesFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.cyclesFunctor_map`：∀ (C : Type u_1) [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.cyclesMap_add`：cyclesMap_add : cyclesMap (φ 
+ φ') = cyclesMap φ + cyclesMap φ'
-/
instance cyclesFunctor_additive [HasKernels C] [HasCokernels C] : (cyclesFunctor C).Additive where

end LeftHomology


section RightHomology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}

namespace RightHomologyMapData

variable (γ : RightHomologyMapData φ h₁ h₂) (γ' : RightHomologyMapData φ' h₁ h₂)

/-- Given a right homology map data for morphism `φ`, this is the induced right homology
map data for `-φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.neg** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：neg : RightHomologyMapData (-φ) h₁ h₂ where φQ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a right homology map data for morphism `φ`, this is the induced right homo
logy
map data for `-φ`.
-/
def neg : RightHomologyMapData (-φ) h₁ h₂ where
  φQ := -γ.φQ
  φH := -γ.φH

/-- Given right homology map data for morphisms `φ` and `φ'`, this is the induced
right homology map data for `φ + φ'`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.add** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：add : RightHomologyMapData (φ + φ') h₁ h₂ where φQ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given right homology map data for morphisms `φ` and `φ'`, this is the induced
right homology map data for `φ + φ'`.
-/
def add : RightHomologyMapData (φ + φ') h₁ h₂ where
  φQ := γ.φQ + γ'.φQ
  φH := γ.φH + γ'.φH

end RightHomologyMapData

variable (h₁ h₂)

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap'_neg** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ : S₁ ⟶
 S₂} (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData),   CategoryTheory.S
hortComplex.rightHomologyMap' (-φ) h₁ h₂ = -CategoryTheory.ShortComplex.rightHom
ologyMap' φ h₁ h₂
参数：h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；-φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.neg_φH`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightHomologyMap'_neg :
    rightHomologyMap' (-φ) h₁ h₂ = -rightHomologyMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ.neg.rightHomologyMap'_eq, RightHomologyMapData.neg_φH]

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ : S₁ ⟶
 S₂} (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData),   CategoryTheory.S
hortComplex.opcyclesMap' (-φ) h₁ h₂ = -CategoryTheory.ShortComplex.opcyclesMap' 
φ h₁ h₂
参数：h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；-φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.neg_φQ`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesMap'_neg :
    opcyclesMap' (-φ) h₁ h₂ = -opcyclesMap' φ h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ.neg.opcyclesMap'_eq, RightHomologyMapData.neg_φQ]

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap'_add** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData),   CategoryTheor
y.ShortComplex.rightHomologyMap' (φ + φ') h₁ h₂ =     CategoryTheory.ShortComple
x.rightHomologyMap' φ h₁ h₂ + CategoryTheory.ShortComplex.rightHomologyMap' φ' h
₁ h₂
参数：h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；φ + φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.add_φH`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightHomologyMap'_add :
    rightHomologyMap' (φ + φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ +
      rightHomologyMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.rightHomologyMap'_eq, γ'.rightHomologyMap'_eq,
    (γ.add γ').rightHomologyMap'_eq, RightHomologyMapData.add_φH]

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap'_add** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData),   CategoryTheor
y.ShortComplex.opcyclesMap' (φ + φ') h₁ h₂ =     CategoryTheory.ShortComplex.opc
yclesMap' φ h₁ h₂ + CategoryTheory.ShortComplex.opcyclesMap' φ' h₁ h₂
参数：h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；φ + φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.opcyclesMap'_eq`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheor
y.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.add_φQ`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesMap'_add :
    opcyclesMap' (φ + φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ +
      opcyclesMap' φ' h₁ h₂ := by
  have γ : RightHomologyMapData φ h₁ h₂ := default
  have γ' : RightHomologyMapData φ' h₁ h₂ := default
  simp only [γ.opcyclesMap'_eq, γ'.opcyclesMap'_eq,
    (γ.add γ').opcyclesMap'_eq, RightHomologyMapData.add_φQ]

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap'_sub** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData),   CategoryTheor
y.ShortComplex.rightHomologyMap' (φ - φ') h₁ h₂ =     CategoryTheory.ShortComple
x.rightHomologyMap' φ h₁ h₂ - CategoryTheory.ShortComplex.rightHomologyMap' φ' h
₁ h₂
参数：h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；φ - φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_add`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_neg`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightHomologyMap'_sub :
    rightHomologyMap' (φ - φ') h₁ h₂ = rightHomologyMap' φ h₁ h₂ -
      rightHomologyMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, rightHomologyMap'_add, rightHomologyMap'_neg]

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData),   CategoryTheor
y.ShortComplex.opcyclesMap' (φ - φ') h₁ h₂ =     CategoryTheory.ShortComplex.opc
yclesMap' φ h₁ h₂ - CategoryTheory.ShortComplex.opcyclesMap' φ' h₁ h₂
参数：h₁ : S₁.RightHomologyData；h₂ : S₂.RightHomologyData；φ - φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap'`：opcyclesMap'_smul : opcyclesMa
p' (a • φ) h₁ h₂ = a • opcyclesMap' φ h₁ h₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_add`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_neg`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opcyclesMap'_sub :
    opcyclesMap' (φ - φ') h₁ h₂ = opcyclesMap' φ h₁ h₂ -
      opcyclesMap' φ' h₁ h₂ := by
  simp only [sub_eq_add_neg, opcyclesMap'_add, opcyclesMap'_neg]

variable (φ φ')

section

variable [S₁.HasRightHomology] [S₂.HasRightHomology]

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：rightHomologyMap_neg : rightHomologyMap (-φ) = -rightHomologyMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_neg`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma rightHomologyMap_neg : rightHomologyMap (-φ) = -rightHomologyMap φ :=
  rightHomologyMap'_neg _ _

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：opcyclesMap_neg : opcyclesMap (-φ) = -opcyclesMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_neg`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma opcyclesMap_neg : opcyclesMap (-φ) = -opcyclesMap φ :=
  opcyclesMap'_neg _ _

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap_add** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：rightHomologyMap_add : rightHomologyMap (φ + φ') = rightHomologyMap φ + ri
ghtHomologyMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_add`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma rightHomologyMap_add :
    rightHomologyMap (φ + φ') = rightHomologyMap φ + rightHomologyMap φ' :=
  rightHomologyMap'_add _ _

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap_add** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：opcyclesMap_add : opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_add`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma opcyclesMap_add : opcyclesMap (φ + φ') = opcyclesMap φ + opcyclesMap φ' :=
  opcyclesMap'_add _ _

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ShortComplex`。
形式化陈述：rightHomologyMap_sub : rightHomologyMap (φ - φ') = rightHomologyMap φ - ri
ghtHomologyMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_sub`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma rightHomologyMap_sub :
    rightHomologyMap (φ - φ') = rightHomologyMap φ - rightHomologyMap φ' :=
  rightHomologyMap'_sub _ _

@[simp]
/-
**CategoryTheory.ShortComplex.opcyclesMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：opcyclesMap_sub : opcyclesMap (φ - φ') = opcyclesMap φ - opcyclesMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.opcyclesMap'_sub`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma opcyclesMap_sub : opcyclesMap (φ - φ') = opcyclesMap φ - opcyclesMap φ' :=
  opcyclesMap'_sub _ _

end

/-
**CategoryTheory.ShortComplex.rightHomologyFunctor_additive** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasKernels C] [in
st_3 : CategoryTheory.Limits.HasCokernels C],   (CategoryTheory.ShortComplex.rig
htHomologyFunctor C).Additive
参数：CategoryTheory.ShortComplex.rightHomologyFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyFunctor_map`：∀ (C : Type u_1) [
inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap_add`：rightHomologyMap_add :
 rightHomologyMap (φ + φ') = rightHomologyMap φ + rightHomologyMap φ'
-/
instance rightHomologyFunctor_additive [HasKernels C] [HasCokernels C] :
    (rightHomologyFunctor C).Additive where
/-
**CategoryTheory.ShortComplex.opcyclesFunctor_additive** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasKernels C] [in
st_3 : CategoryTheory.Limits.HasCokernels C],   (CategoryTheory.ShortComplex.opc
yclesFunctor C).Additive
参数：CategoryTheory.ShortComplex.opcyclesFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.opcyclesFunctor_map`：∀ (C : Type u_1) [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   [inst_2 : CategoryTheor…
· 使用引理 `CategoryTheory.ShortComplex.opcyclesMap_add`：opcyclesMap_add : opcyclesM
ap (φ + φ') = opcyclesMap φ + opcyclesMap φ'
-/
instance opcyclesFunctor_additive [HasKernels C] [HasCokernels C] :
    (opcyclesFunctor C).Additive where

end RightHomology

section Homology

variable {φ φ' : S₁ ⟶ S₂} {h₁ : S₁.HomologyData} {h₂ : S₂.HomologyData}

namespace HomologyMapData

variable (γ : HomologyMapData φ h₁ h₂) (γ' : HomologyMapData φ' h₁ h₂)

/-- Given a homology map data for a morphism `φ`, this is the induced homology
map data for `-φ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.neg** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：neg : HomologyMapData (-φ) h₁ h₂ where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a homology map data for a morphism `φ`, this is the induced homology
map data for `-φ`.
-/
def neg : HomologyMapData (-φ) h₁ h₂ where
  left := γ.left.neg
  right := γ.right.neg

/-- Given homology map data for morphisms `φ` and `φ'`, this is the induced homology
map data for `φ + φ'`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomologyMapData.add** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.HomologyMapData`。
形式化陈述：add : HomologyMapData (φ + φ') h₁ h₂ where left
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given homology map data for morphisms `φ` and `φ'`, this is the induced homology
map data for `φ + φ'`.
-/
def add : HomologyMapData (φ + φ') h₁ h₂ where
  left := γ.left.add γ'.left
  right := γ.right.add γ'.right

end HomologyMapData

variable (h₁ h₂)

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_neg** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ : S₁ ⟶
 S₂} (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData),   CategoryTheory.ShortComple
x.homologyMap' (-φ) h₁ h₂ = -CategoryTheory.ShortComplex.homologyMap' φ h₁ h₂
参数：h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；-φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_neg`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap'_neg :
    homologyMap' (-φ) h₁ h₂ = -homologyMap' φ h₁ h₂ :=
  leftHomologyMap'_neg _ _

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_add** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData),   CategoryTheory.ShortCom
plex.homologyMap' (φ + φ') h₁ h₂ =     CategoryTheory.ShortComplex.homologyMap' 
φ h₁ h₂ + CategoryTheory.ShortComplex.homologyMap' φ' h₁ h₂
参数：h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；φ + φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_add`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap'_add :
    homologyMap' (φ + φ') h₁ h₂ = homologyMap' φ h₁ h₂ + homologyMap' φ' h₁ h₂ :=
  leftHomologyMap'_add _ _

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_sub** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ φ' : S
₁ ⟶ S₂} (h₁ : S₁.HomologyData) (h₂ : S₂.HomologyData),   CategoryTheory.ShortCom
plex.homologyMap' (φ - φ') h₁ h₂ =     CategoryTheory.ShortComplex.homologyMap' 
φ h₁ h₂ - CategoryTheory.ShortComplex.homologyMap' φ' h₁ h₂
参数：h₁ : S₁.HomologyData；h₂ : S₂.HomologyData；φ - φ'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_sub`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap'_sub :
    homologyMap' (φ - φ') h₁ h₂ = homologyMap' φ h₁ h₂ - homologyMap' φ' h₁ h₂ :=
  leftHomologyMap'_sub _ _

variable (φ φ')

section

variable [S₁.HasHomology] [S₂.HasHomology]

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_neg** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：homologyMap_neg : homologyMap (-φ) = -homologyMap φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_neg`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap_neg : homologyMap (-φ) = -homologyMap φ :=
  homologyMap'_neg _ _

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_add** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：homologyMap_add : homologyMap (φ + φ') = homologyMap φ + homologyMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_add`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap_add : homologyMap (φ + φ') = homologyMap φ + homologyMap φ' :=
  homologyMap'_add _ _

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_sub** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：homologyMap_sub : homologyMap (φ - φ') = homologyMap φ - homologyMap φ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_sub`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap_sub : homologyMap (φ - φ') = homologyMap φ - homologyMap φ' :=
  homologyMap'_sub _ _

end

/-
**CategoryTheory.ShortComplex.homologyFunctor_additive** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.CategoryWithHomology C],
 (CategoryTheory.ShortComplex.homologyFunctor C).Additive
参数：CategoryTheory.ShortComplex.homologyFunctor C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ShortComplex.homologyFunctor_map`：∀ (C : Type u) [inst : 
CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C]   [inst_2 : CategoryTheory.Cate…
· 使用引理 `CategoryTheory.ShortComplex.homologyMap_add`：homologyMap_add : homologyM
ap (φ + φ') = homologyMap φ + homologyMap φ'
-/
instance homologyFunctor_additive [CategoryWithHomology C] : (homologyFunctor C).Additive where

end Homology

section Homotopy

variable (φ₁ φ₂ φ₃ φ₄ : S₁ ⟶ S₂)

/-- A homotopy between two morphisms of short complexes `S₁ ⟶ S₂` consists of various
maps and conditions which will be sufficient to show that they induce the same morphism
in homology. -/
@[ext]
/-
**CategoryTheory.ShortComplex.Homotopy** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory
.ShortComplex`。
形式化陈述：Homotopy where /-- a morphism `S₁.X₁ ⟶ S₂.X₁` -/ h₀ : S₁.X₁ ⟶ S₂.X₁ h₀_f :
 h₀ ≫ S₂.f = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy between two morphisms of short complexes `S₁ ⟶ S₂` consists of variou
s
maps and conditions which will be sufficient to show that they induce the same m
orphism
in homology.
-/
structure Homotopy where
  /-- a morphism `S₁.X₁ ⟶ S₂.X₁` -/
  h₀ : S₁.X₁ ⟶ S₂.X₁
  h₀_f : h₀ ≫ S₂.f = 0 := by cat_disch
  /-- a morphism `S₁.X₂ ⟶ S₂.X₁` -/
  h₁ : S₁.X₂ ⟶ S₂.X₁
  /-- a morphism `S₁.X₃ ⟶ S₂.X₂` -/
  h₂ : S₁.X₃ ⟶ S₂.X₂
  /-- a morphism `S₁.X₃ ⟶ S₂.X₃` -/
  h₃ : S₁.X₃ ⟶ S₂.X₃
  g_h₃ : S₁.g ≫ h₃ = 0 := by cat_disch
  comm₁ : φ₁.τ₁ = S₁.f ≫ h₁ + h₀ + φ₂.τ₁ := by cat_disch
  comm₂ : φ₁.τ₂ = S₁.g ≫ h₂ + h₁ ≫ S₂.f + φ₂.τ₂ := by cat_disch
  comm₃ : φ₁.τ₃ = h₃ + h₂ ≫ S₂.g + φ₂.τ₃ := by cat_disch

attribute [reassoc (attr := simp)] Homotopy.h₀_f Homotopy.g_h₃

variable (S₁ S₂)

/-- Constructor for null homotopic morphisms, see also `Homotopy.ofNullHomotopic`
and `Homotopy.eq_add_nullHomotopic`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.nullHomotopic** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex`。
形式化陈述：nullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂
.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) : S₁ ⟶ S₂ 
where τ₁
参数：h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : h₀ ≫ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂.X₂
；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : S₁.g ≫ h₃ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for null homotopic morphisms, see also `Homotopy.ofNullHomotopic`
and `Homotopy.eq_add_nullHomotopic`.
-/
def nullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    S₁ ⟶ S₂ where
  τ₁ := h₀ + S₁.f ≫ h₁
  τ₂ := h₁ ≫ S₂.f + S₁.g ≫ h₂
  τ₃ := h₂ ≫ S₂.g + h₃

namespace Homotopy

attribute [local simp] neg_comp

variable {S₁ S₂ φ₁ φ₂ φ₃ φ₄}

/-- The obvious homotopy between two equal morphisms of short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Homotopy`。
形式化陈述：ofEq (h : φ₁ = φ₂) : Homotopy φ₁ φ₂ where h₀
参数：h : φ₁ = φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious homotopy between two equal morphisms of short complexes.
-/
def ofEq (h : φ₁ = φ₂) : Homotopy φ₁ φ₂ where
  h₀ := 0
  h₁ := 0
  h₂ := 0
  h₃ := 0

/-- The obvious homotopy between a morphism of short complexes and itself. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.Homotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Homotopy`。
形式化陈述：refl (φ : S₁ ⟶ S₂) : Homotopy φ φ
参数：φ : S₁ ⟶ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious homotopy between a morphism of short complexes and itself.
-/
def refl (φ : S₁ ⟶ S₂) : Homotopy φ φ := ofEq rfl

/-- The symmetry of homotopy between morphisms of short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Homotopy`。
形式化陈述：symm (h : Homotopy φ₁ φ₂) : Homotopy φ₂ φ₁ where h₀
参数：h : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetry of homotopy between morphisms of short complexes.
-/
def symm (h : Homotopy φ₁ φ₂) : Homotopy φ₂ φ₁ where
  h₀ := -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [h.comm₁, comp_neg]; abel
  comm₂ := by rw [h.comm₂, comp_neg, neg_comp]; abel
  comm₃ := by rw [h.comm₃, neg_comp]; abel

/-- If two maps of short complexes are homotopic, their opposites also are. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.neg** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex.Homotopy`。
形式化陈述：neg (h : Homotopy φ₁ φ₂) : Homotopy (-φ₁) (-φ₂) where h₀
参数：h : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two maps of short complexes are homotopic, their opposites also are.
-/
def neg (h : Homotopy φ₁ φ₂) : Homotopy (-φ₁) (-φ₂) where
  h₀ := -h.h₀
  h₁ := -h.h₁
  h₂ := -h.h₂
  h₃ := -h.h₃
  comm₁ := by rw [neg_τ₁, neg_τ₁, h.comm₁, neg_add_rev, comp_neg]; abel
  comm₂ := by rw [neg_τ₂, neg_τ₂, h.comm₂, neg_add_rev, comp_neg, neg_comp]; abel
  comm₃ := by rw [neg_τ₃, neg_τ₃, h.comm₃, neg_comp]; abel

/-- The transitivity of homotopy between morphisms of short complexes. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ShortComplex.Homotopy`。
形式化陈述：trans (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃) : Homotopy φ₁ φ₃ where
 h₀
参数：h₁₂ : Homotopy φ₁ φ₂；h₂₃ : Homotopy φ₂ φ₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transitivity of homotopy between morphisms of short complexes.
-/
def trans (h₁₂ : Homotopy φ₁ φ₂) (h₂₃ : Homotopy φ₂ φ₃) : Homotopy φ₁ φ₃ where
  h₀ := h₁₂.h₀ + h₂₃.h₀
  h₁ := h₁₂.h₁ + h₂₃.h₁
  h₂ := h₁₂.h₂ + h₂₃.h₂
  h₃ := h₁₂.h₃ + h₂₃.h₃
  comm₁ := by rw [h₁₂.comm₁, h₂₃.comm₁, comp_add]; abel
  comm₂ := by rw [h₁₂.comm₂, h₂₃.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [h₁₂.comm₃, h₂₃.comm₃, add_comp]; abel

/-- Homotopy between morphisms of short complexes is compatible with addition. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.add** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex.Homotopy`。
形式化陈述：add (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ + φ₃) (φ₂ + 
φ₄) where h₀
参数：h : Homotopy φ₁ φ₂；h' : Homotopy φ₃ φ₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy between morphisms of short complexes is compatible with addition.
-/
def add (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ + φ₃) (φ₂ + φ₄) where
  h₀ := h.h₀ + h'.h₀
  h₁ := h.h₁ + h'.h₁
  h₂ := h.h₂ + h'.h₂
  h₃ := h.h₃ + h'.h₃
  comm₁ := by rw [add_τ₁, add_τ₁, h.comm₁, h'.comm₁, comp_add]; abel
  comm₂ := by rw [add_τ₂, add_τ₂, h.comm₂, h'.comm₂, comp_add, add_comp]; abel
  comm₃ := by rw [add_τ₃, add_τ₃, h.comm₃, h'.comm₃, add_comp]; abel

/-- Homotopy between morphisms of short complexes is compatible with subtraction. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.sub** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.ShortComplex.Homotopy`。
形式化陈述：sub (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ - φ₃) (φ₂ - 
φ₄) where h₀
参数：h : Homotopy φ₁ φ₂；h' : Homotopy φ₃ φ₄。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy between morphisms of short complexes is compatible with subtraction.
-/
def sub (h : Homotopy φ₁ φ₂) (h' : Homotopy φ₃ φ₄) : Homotopy (φ₁ - φ₃) (φ₂ - φ₄) where
  h₀ := h.h₀ - h'.h₀
  h₁ := h.h₁ - h'.h₁
  h₂ := h.h₂ - h'.h₂
  h₃ := h.h₃ - h'.h₃
  comm₁ := by rw [sub_τ₁, sub_τ₁, h.comm₁, h'.comm₁, comp_sub]; abel
  comm₂ := by rw [sub_τ₂, sub_τ₂, h.comm₂, h'.comm₂, comp_sub, sub_comp]; abel
  comm₃ := by rw [sub_τ₃, sub_τ₃, h.comm₃, h'.comm₃, sub_comp]; abel

/-- Homotopy between morphisms of short complexes is compatible with precomposition. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ShortComplex.Homotopy`。
形式化陈述：compLeft (h : Homotopy φ₁ φ₂) (ψ : S₃ ⟶ S₁) : Homotopy (ψ ≫ φ₁) (ψ ≫ φ₂) w
here h₀
参数：h : Homotopy φ₁ φ₂；ψ : S₃ ⟶ S₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy between morphisms of short complexes is compatible with precomposition.
-/
def compLeft (h : Homotopy φ₁ φ₂) (ψ : S₃ ⟶ S₁) : Homotopy (ψ ≫ φ₁) (ψ ≫ φ₂) where
  h₀ := ψ.τ₁ ≫ h.h₀
  h₁ := ψ.τ₂ ≫ h.h₁
  h₂ := ψ.τ₃ ≫ h.h₂
  h₃ := ψ.τ₃ ≫ h.h₃
  g_h₃ := by rw [← ψ.comm₂₃_assoc, h.g_h₃, comp_zero]
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, comp_add, comp_add, add_left_inj, ψ.comm₁₂_assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, comp_add, comp_add, assoc, ψ.comm₂₃_assoc]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, comp_add, comp_add, assoc]

/-- Homotopy between morphisms of short complexes is compatible with postcomposition. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.compRight** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.Homotopy`。
形式化陈述：compRight (h : Homotopy φ₁ φ₂) (ψ : S₂ ⟶ S₃) : Homotopy (φ₁ ≫ ψ) (φ₂ ≫ ψ) 
where h₀
参数：h : Homotopy φ₁ φ₂；ψ : S₂ ⟶ S₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy between morphisms of short complexes is compatible with postcomposition
.
-/
def compRight (h : Homotopy φ₁ φ₂) (ψ : S₂ ⟶ S₃) : Homotopy (φ₁ ≫ ψ) (φ₂ ≫ ψ) where
  h₀ := h.h₀ ≫ ψ.τ₁
  h₁ := h.h₁ ≫ ψ.τ₁
  h₂ := h.h₂ ≫ ψ.τ₂
  h₃ := h.h₃ ≫ ψ.τ₃
  comm₁ := by rw [comp_τ₁, comp_τ₁, h.comm₁, add_comp, add_comp, assoc]
  comm₂ := by rw [comp_τ₂, comp_τ₂, h.comm₂, add_comp, add_comp, assoc, assoc, assoc, ψ.comm₁₂]
  comm₃ := by rw [comp_τ₃, comp_τ₃, h.comm₃, add_comp, add_comp, assoc, assoc, ψ.comm₂₃]

/-- Homotopy between morphisms of short complexes is compatible with composition. -/
@[simps!]
/-
**CategoryTheory.ShortComplex.Homotopy.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Homotopy`。
形式化陈述：comp (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂) : Homoto
py (φ₁ ≫ ψ₁) (φ₂ ≫ ψ₂)
参数：h : Homotopy φ₁ φ₂；h' : Homotopy ψ₁ ψ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy between morphisms of short complexes is compatible with composition.
-/
def comp (h : Homotopy φ₁ φ₂) {ψ₁ ψ₂ : S₂ ⟶ S₃} (h' : Homotopy ψ₁ ψ₂) :
    Homotopy (φ₁ ≫ ψ₁) (φ₂ ≫ ψ₂) :=
  (h.compRight ψ₁).trans (h'.compLeft φ₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy between morphisms in `ShortComplex Cᵒᵖ` that is induced by a homotopy
between morphisms in `ShortComplex C`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ShortComplex.Homotopy`。
形式化陈述：op (h : Homotopy φ₁ φ₂) : Homotopy (opMap φ₁) (opMap φ₂) where h₀
参数：h : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between morphisms in `ShortComplex Cᵒᵖ` that is induced by a homoto
py
between morphisms in `ShortComplex C`.
-/
def op (h : Homotopy φ₁ φ₂) : Homotopy (opMap φ₁) (opMap φ₂) where
  h₀ := h.h₃.op
  h₁ := h.h₂.op
  h₂ := h.h₁.op
  h₃ := h.h₀.op
  h₀_f := Quiver.Hom.unop_inj h.g_h₃
  g_h₃ := Quiver.Hom.unop_inj h.h₀_f
  comm₁ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.unop_inj (by dsimp; rw [h.comm₁]; abel)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The homotopy between morphisms in `ShortComplex C` that is induced by a homotopy
between morphisms in `ShortComplex Cᵒᵖ`. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ShortComplex.Homotopy`。
形式化陈述：unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) : H
omotopy (unopMap φ₁) (unopMap φ₂) where h₀
参数：h : Homotopy φ₁ φ₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy between morphisms in `ShortComplex C` that is induced by a homotopy
between morphisms in `ShortComplex Cᵒᵖ`.
-/
def unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ₁ φ₂ : S₁ ⟶ S₂} (h : Homotopy φ₁ φ₂) :
    Homotopy (unopMap φ₁) (unopMap φ₂) where
  h₀ := h.h₃.unop
  h₁ := h.h₂.unop
  h₂ := h.h₁.unop
  h₃ := h.h₀.unop
  h₀_f := Quiver.Hom.op_inj h.g_h₃
  g_h₃ := Quiver.Hom.op_inj h.h₀_f
  comm₁ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₃]; abel)
  comm₂ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₂]; abel)
  comm₃ := Quiver.Hom.op_inj (by dsimp; rw [h.comm₁]; abel)

variable (φ₁ φ₂)

/-- Equivalence expressing that two morphisms are homotopic iff
their difference is homotopic to zero. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.equivSubZero** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.ShortComplex.Homotopy`。
形式化陈述：equivSubZero : Homotopy φ₁ φ₂ ≃ Homotopy (φ₁ - φ₂) 0 where toFun h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence expressing that two morphisms are homotopic iff
their difference is homotopic to zero.
-/
def equivSubZero : Homotopy φ₁ φ₂ ≃ Homotopy (φ₁ - φ₂) 0 where
  toFun h := (h.sub (refl φ₂)).trans (ofEq (sub_self φ₂))
  invFun h := ((ofEq (sub_add_cancel φ₁ φ₂).symm).trans
    (h.add (refl φ₂))).trans (ofEq (zero_add φ₂))
  left_inv := by cat_disch
  right_inv := by cat_disch

variable {φ₁ φ₂}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：eq_add_nullHomotopic (h : Homotopy φ₁ φ₂) : φ₁ = φ₂ + nullHomotopic _ _ h.
h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃
参数：h : Homotopy φ₁ φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.hom_ext`：hom_ext (f g : S₁ ⟶ S₂) (h₁ : f.τ₁ 
= g.τ₁) (h₂ : f.τ₂ = g.τ₂) (h₃ : f.τ₃ = g.τ₃) : f = g
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.h₀_f`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.g_h₃`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.comm₁`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
· 使用定理 `_private.Mathlib.Algebra.Homology.ShortComplex.Preadditive.0.CategoryThe
ory.ShortComplex.Homotopy.eq_add_nullHomotopic._abel_1_1`：∀ {C : Type u_2} [inst
 : CategoryTheory.Category.{u_1, u_2} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.comm₂`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
· 使用定理 `_private.Mathlib.Algebra.Homology.ShortComplex.Preadditive.0.CategoryThe
ory.ShortComplex.Homotopy.eq_add_nullHomotopic._abel_1_2`：∀ {C : Type u_2} [inst
 : CategoryTheory.Category.{u_1, u_2} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.comm₃`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁
 S₂ : CategoryTheory.ShortComple…
· 使用定理 `_private.Mathlib.Algebra.Homology.ShortComplex.Preadditive.0.CategoryThe
ory.ShortComplex.Homotopy.eq_add_nullHomotopic._abel_1_3`：∀ {C : Type u_2} [inst
 : CategoryTheory.Category.{u_1, u_2} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma eq_add_nullHomotopic (h : Homotopy φ₁ φ₂) :
    φ₁ = φ₂ + nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂ h.h₃ h.g_h₃ := by
  ext
  · dsimp; rw [h.comm₁]; abel
  · dsimp; rw [h.comm₂]; abel
  · dsimp; rw [h.comm₃]; abel

variable (S₁ S₂)

/-- A morphism constructed with `nullHomotopic` is homotopic to zero. -/
@[simps]
/-
**CategoryTheory.ShortComplex.Homotopy.ofNullHomotopic** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：ofNullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0) (h₁ : S₁.X₂ ⟶ 
S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) : Homoto
py (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) 0 where h₀
参数：h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : h₀ ≫ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂.X₂
；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : S₁.g ≫ h₃ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism constructed with `nullHomotopic` is homotopic to zero.
-/
def ofNullHomotopic (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    Homotopy (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) 0 where
  h₀ := h₀
  h₁ := h₁
  h₂ := h₂
  h₃ := h₃
  h₀_f := h₀_f
  g_h₃ := g_h₃
  comm₁ := by rw [nullHomotopic_τ₁, zero_τ₁, add_zero]; abel
  comm₂ := by rw [nullHomotopic_τ₂, zero_τ₂, add_zero]; abel
  comm₃ := by rw [nullHomotopic_τ₃, zero_τ₃, add_zero]; abel

end Homotopy

variable {S₁ S₂}

/-- The left homology map data expressing that null homotopic maps induce the zero
morphism in left homology. -/
/-
**CategoryTheory.ShortComplex.LeftHomologyMapData.ofNullHomotopic** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.ShortComplex.LeftHomologyMapData`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {S₁ S₂ : CategoryTheory.ShortComple
x C} →         (H₁ : S₁.LeftHomologyData) →           (H₂ : S₂.LeftHomologyData)
 →             (h₀ : S₁.X₁ ⟶ S₂.X₁) →               (h₀_f : CategoryTheory.Categ
oryStruct.comp h₀ S₂.f = 0) →                 (h₁ : S₁.X₂ ⟶ S₂.X₁) →            
       (h₂ : S₁.X₃ ⟶ S₂.X₂) →                     (h₃ : S₁.X₃ ⟶ S₂.X₃) →        
               (g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0) →        
                 CategoryTheory.ShortComplex.LeftHomologyMapData (S₁.nullHomotop
ic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁                           H₂
参数：H₁ : S₁.LeftHomologyData；H₂ : S₂.LeftHomologyData；h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : C
ategoryTheory.CategoryStruct.comp h₀ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂
.X₂；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0；S₁.
nullHomotopic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left homology map data expressing that null homotopic maps induce the zero
morphism in left homology.
-/
def LeftHomologyMapData.ofNullHomotopic
    (H₁ : S₁.LeftHomologyData) (H₂ : S₂.LeftHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    LeftHomologyMapData (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ where
  φK := H₂.liftK (H₁.i ≫ h₁ ≫ S₂.f) (by simp)
  φH := 0
  commf' := by
    rw [← cancel_mono H₂.i, assoc, LeftHomologyData.liftK_i, LeftHomologyData.f'_i_assoc,
      nullHomotopic_τ₁, add_comp, add_comp, assoc, assoc, assoc, LeftHomologyData.f'_i,
      right_eq_add, h₀_f]
  commπ := by
    rw [H₂.liftK_π_eq_zero_of_boundary (H₁.i ≫ h₁ ≫ S₂.f) (H₁.i ≫ h₁) (by rw [assoc]), comp_zero]

/-- The right homology map data expressing that null homotopic maps induce the zero
morphism in right homology. -/
/-
**CategoryTheory.ShortComplex.RightHomologyMapData.ofNullHomotopic** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.ShortComplex.RightHomologyMapData`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {S₁ S₂ : CategoryTheory.ShortComple
x C} →         (H₁ : S₁.RightHomologyData) →           (H₂ : S₂.RightHomologyDat
a) →             (h₀ : S₁.X₁ ⟶ S₂.X₁) →               (h₀_f : CategoryTheory.Cat
egoryStruct.comp h₀ S₂.f = 0) →                 (h₁ : S₁.X₂ ⟶ S₂.X₁) →          
         (h₂ : S₁.X₃ ⟶ S₂.X₂) →                     (h₃ : S₁.X₃ ⟶ S₂.X₃) →      
                 (g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0) →      
                   CategoryTheory.ShortComplex.RightHomologyMapData (S₁.nullHomo
topic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁                           H₂
参数：H₁ : S₁.RightHomologyData；H₂ : S₂.RightHomologyData；h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f :
 CategoryTheory.CategoryStruct.comp h₀ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ 
S₂.X₂；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0；S
₁.nullHomotopic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right homology map data expressing that null homotopic maps induce the zero
morphism in right homology.
-/
def RightHomologyMapData.ofNullHomotopic
    (H₁ : S₁.RightHomologyData) (H₂ : S₂.RightHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    RightHomologyMapData (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ where
  φQ := H₁.descQ (S₁.g ≫ h₂ ≫ H₂.p) (by simp)
  φH := 0
  commg' := by
    rw [← cancel_epi H₁.p, RightHomologyData.p_descQ_assoc, RightHomologyData.p_g'_assoc,
      nullHomotopic_τ₃, comp_add, assoc, assoc, RightHomologyData.p_g', g_h₃, add_zero]
  commι := by
    rw [H₁.ι_descQ_eq_zero_of_boundary (S₁.g ≫ h₂ ≫ H₂.p) (h₂ ≫ H₂.p) rfl, zero_comp]

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (H₁ : S₁.
LeftHomologyData) (H₂ : S₂.LeftHomologyData) (h₀ : S₁.X₁ ⟶ S₂.X₁)   (h₀_f : Cate
goryTheory.CategoryStruct.comp h₀ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S
₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃)   (g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ 
= 0),   CategoryTheory.ShortComplex.leftHomologyMap' (S₁.nullHomotopic S₂ h₀ h₀_
f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0
参数：H₁ : S₁.LeftHomologyData；H₂ : S₂.LeftHomologyData；h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : C
ategoryTheory.CategoryStruct.comp h₀ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂
.X₂；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0；S₁.
nullHomotopic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.LeftHomologyMapData.leftHomologyMap'_eq`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma leftHomologyMap'_nullHomotopic
    (H₁ : S₁.LeftHomologyData) (H₂ : S₂.LeftHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    leftHomologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  (LeftHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).leftHomologyMap'_eq

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap'_nullHomotopic** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (H₁ : S₁.
RightHomologyData) (H₂ : S₂.RightHomologyData) (h₀ : S₁.X₁ ⟶ S₂.X₁)   (h₀_f : Ca
tegoryTheory.CategoryStruct.comp h₀ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶
 S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃)   (g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h
₃ = 0),   CategoryTheory.ShortComplex.rightHomologyMap' (S₁.nullHomotopic S₂ h₀ 
h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0
参数：H₁ : S₁.RightHomologyData；H₂ : S₂.RightHomologyData；h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f :
 CategoryTheory.CategoryStruct.comp h₀ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ 
S₂.X₂；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0；S
₁.nullHomotopic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.RightHomologyMapData.rightHomologyMap'_eq`：∀
 {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Category
Theory.Limits.HasZeroMorphisms C]   {S₁ S₂ : CategoryTheory…
-/
lemma rightHomologyMap'_nullHomotopic
    (H₁ : S₁.RightHomologyData) (H₂ : S₂.RightHomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    rightHomologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 :=
  (RightHomologyMapData.ofNullHomotopic H₁ H₂ h₀ h₀_f h₁ h₂ h₃ g_h₃).rightHomologyMap'_eq

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap'_nullHomotopic** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.ShortComplex`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} (H₁ : S₁.
HomologyData) (H₂ : S₂.HomologyData) (h₀ : S₁.X₁ ⟶ S₂.X₁)   (h₀_f : CategoryTheo
ry.CategoryStruct.comp h₀ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h
₃ : S₁.X₃ ⟶ S₂.X₃)   (g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0),   
CategoryTheory.ShortComplex.homologyMap' (S₁.nullHomotopic S₂ h₀ h₀_f h₁ h₂ h₃ g
_h₃) H₁ H₂ = 0
参数：H₁ : S₁.HomologyData；H₂ : S₂.HomologyData；h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : CategoryT
heory.CategoryStruct.comp h₀ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂.X₂；h₃ :
 S₁.X₃ ⟶ S₂.X₃；g_h₃ : CategoryTheory.CategoryStruct.comp S₁.g h₃ = 0；S₁.nullHomo
topic S₂ h₀ h₀_f h₁ h₂ h₃ g_h₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap'_nullHomotopic
    (H₁ : S₁.HomologyData) (H₂ : S₂.HomologyData)
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap' (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) H₁ H₂ = 0 := by
  apply leftHomologyMap'_nullHomotopic

variable (S₁ S₂)

@[simp]
/-
**CategoryTheory.ShortComplex.leftHomologyMap_nullHomotopic** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：leftHomologyMap_nullHomotopic [S₁.HasLeftHomology] [S₂.HasLeftHomology] (h
₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.
X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) : leftHomologyMap (nullHomotopic
 _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0
参数：h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : h₀ ≫ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂.X₂
；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : S₁.g ≫ h₃ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma leftHomologyMap_nullHomotopic [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    leftHomologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 := by
  apply leftHomologyMap'_nullHomotopic

@[simp]
/-
**CategoryTheory.ShortComplex.rightHomologyMap_nullHomotopic** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex`。
形式化陈述：rightHomologyMap_nullHomotopic [S₁.HasRightHomology] [S₂.HasRightHomology]
 (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ 
S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) : rightHomologyMap (nullHomot
opic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0
参数：h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : h₀ ≫ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂.X₂
；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : S₁.g ≫ h₃ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_nullHomotopic`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pre
additive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma rightHomologyMap_nullHomotopic [S₁.HasRightHomology] [S₂.HasRightHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    rightHomologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 := by
  apply rightHomologyMap'_nullHomotopic

@[simp]
/-
**CategoryTheory.ShortComplex.homologyMap_nullHomotopic** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ShortComplex`。
形式化陈述：homologyMap_nullHomotopic [S₁.HasHomology] [S₂.HasHomology] (h₀ : S₁.X₁ ⟶ 
S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0) (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁
.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) : homologyMap (nullHomotopic _ _ h₀ h₀_f h₁ 
h₂ h₃ g_h₃) = 0
参数：h₀ : S₁.X₁ ⟶ S₂.X₁；h₀_f : h₀ ≫ S₂.f = 0；h₁ : S₁.X₂ ⟶ S₂.X₁；h₂ : S₁.X₃ ⟶ S₂.X₂
；h₃ : S₁.X₃ ⟶ S₂.X₃；g_h₃ : S₁.g ≫ h₃ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_nullHomotopic`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap_nullHomotopic [S₁.HasHomology] [S₂.HasHomology]
    (h₀ : S₁.X₁ ⟶ S₂.X₁) (h₀_f : h₀ ≫ S₂.f = 0)
    (h₁ : S₁.X₂ ⟶ S₂.X₁) (h₂ : S₁.X₃ ⟶ S₂.X₂) (h₃ : S₁.X₃ ⟶ S₂.X₃) (g_h₃ : S₁.g ≫ h₃ = 0) :
    homologyMap (nullHomotopic _ _ h₀ h₀_f h₁ h₂ h₃ g_h₃) = 0 := by
  apply homologyMap'_nullHomotopic

namespace Homotopy

variable {φ₁ φ₂ S₁ S₂}

/-
**CategoryTheory.ShortComplex.Homotopy.leftHomologyMap'_congr** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ₁ φ₂ : 
S₁ ⟶ S₂} (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂)   (h₁ : S₁.LeftHomolog
yData) (h₂ : S₂.LeftHomologyData),   CategoryTheory.ShortComplex.leftHomologyMap
' φ₁ h₁ h₂ = CategoryTheory.ShortComplex.leftHomologyMap' φ₂ h₁ h₂
参数：h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂；h₁ : S₁.LeftHomologyData；h₂ : 
S₂.LeftHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.h₀_f`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.g_h₃`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic`：eq_add_nullHo
motopic (h : Homotopy φ₁ φ₂) : φ₁ = φ₂ + nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂
 h.h₃ h.g_h₃
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_add`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.leftHomologyMap'_nullHomotopic`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Prea
dditive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma leftHomologyMap'_congr (h : Homotopy φ₁ φ₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : leftHomologyMap' φ₁ h₁ h₂ = leftHomologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_nullHomotopic, leftHomologyMap'_add, leftHomologyMap'_nullHomotopic, add_zero]
/-
**CategoryTheory.ShortComplex.Homotopy.rightHomologyMap'_congr** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ₁ φ₂ : 
S₁ ⟶ S₂} (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂)   (h₁ : S₁.RightHomolo
gyData) (h₂ : S₂.RightHomologyData),   CategoryTheory.ShortComplex.rightHomology
Map' φ₁ h₁ h₂ = CategoryTheory.ShortComplex.rightHomologyMap' φ₂ h₁ h₂
参数：h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂；h₁ : S₁.RightHomologyData；h₂ :
 S₂.RightHomologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.rightHomologyMap'`：rightHomologyMap'_smul : 
rightHomologyMap' (a • φ) h₁ h₂ = a • rightHomologyMap' φ h₁ h₂
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.h₀_f`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.g_h₃`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic`：eq_add_nullHo
motopic (h : Homotopy φ₁ φ₂) : φ₁ = φ₂ + nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂
 h.h₃ h.g_h₃
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_add`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.rightHomologyMap'_nullHomotopic`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pre
additive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma rightHomologyMap'_congr (h : Homotopy φ₁ φ₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : rightHomologyMap' φ₁ h₁ h₂ = rightHomologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_nullHomotopic, rightHomologyMap'_add, rightHomologyMap'_nullHomotopic, add_zero]
/-
**CategoryTheory.ShortComplex.Homotopy.homologyMap'_congr** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   {S₁ S₂ : CategoryTheory.ShortComplex C} {φ₁ φ₂ : 
S₁ ⟶ S₂} (h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂)   (h₁ : S₁.HomologyDat
a) (h₂ : S₂.HomologyData),   CategoryTheory.ShortComplex.homologyMap' φ₁ h₁ h₂ =
 CategoryTheory.ShortComplex.homologyMap' φ₂ h₁ h₂
参数：h : CategoryTheory.ShortComplex.Homotopy φ₁ φ₂；h₁ : S₁.HomologyData；h₂ : S₂.H
omologyData。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.h₀_f`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.g_h₃`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {S₁ 
S₂ : CategoryTheory.ShortComple…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.Homotopy.eq_add_nullHomotopic`：eq_add_nullHo
motopic (h : Homotopy φ₁ φ₂) : φ₁ = φ₂ + nullHomotopic _ _ h.h₀ h.h₀_f h.h₁ h.h₂
 h.h₃ h.g_h₃
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_add`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   {
S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `CategoryTheory.ShortComplex.homologyMap'_nullHomotopic`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddit
ive C]   {S₁ S₂ : CategoryTheory.ShortComple…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma homologyMap'_congr (h : Homotopy φ₁ φ₂) (h₁ : S₁.HomologyData)
    (h₂ : S₂.HomologyData) : homologyMap' φ₁ h₁ h₂ = homologyMap' φ₂ h₁ h₂ := by
  rw [h.eq_add_nullHomotopic, homologyMap'_add, homologyMap'_nullHomotopic, add_zero]
/-
**CategoryTheory.ShortComplex.Homotopy.leftHomologyMap_congr** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：leftHomologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasLeftHomology] [S₂.HasLef
tHomology] : leftHomologyMap φ₁ = leftHomologyMap φ₂
参数：h : Homotopy φ₁ φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.leftHomologyMap'_congr`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pre
additive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma leftHomologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ₁ = leftHomologyMap φ₂ :=
  h.leftHomologyMap'_congr _ _
/-
**CategoryTheory.ShortComplex.Homotopy.rightHomologyMap_congr** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：rightHomologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasR
ightHomology] : rightHomologyMap φ₁ = rightHomologyMap φ₂
参数：h : Homotopy φ₁ φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.rightHomologyMap'_congr`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pr
eadditive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma rightHomologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ₁ = rightHomologyMap φ₂ :=
  h.rightHomologyMap'_congr _ _
/-
**CategoryTheory.ShortComplex.Homotopy.homologyMap_congr** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ShortComplex.Homotopy`。
形式化陈述：homologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology] :
 homologyMap φ₁ = homologyMap φ₂
参数：h : Homotopy φ₁ φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Homotopy.homologyMap'_congr`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preaddi
tive C]   {S₁ S₂ : CategoryTheory.ShortComple…
-/
lemma homologyMap_congr (h : Homotopy φ₁ φ₂) [S₁.HasHomology] [S₂.HasHomology] :
    homologyMap φ₁ = homologyMap φ₂ :=
  h.homologyMap'_congr _ _

end Homotopy

/-- A homotopy equivalence between two short complexes `S₁` and `S₂` consists
of morphisms `hom : S₁ ⟶ S₂` and `inv : S₂ ⟶ S₁` such that both compositions
`hom ≫ inv` and `inv ≫ hom` are homotopic to the identity. -/
@[ext]
/-
**CategoryTheory.ShortComplex.HomotopyEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.ShortComplex`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] → CategoryTheory.ShortComplex C → CategoryT
heory.ShortComplex C → Type v_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy equivalence between two short complexes `S₁` and `S₂` consists
of morphisms `hom : S₁ ⟶ S₂` and `inv : S₂ ⟶ S₁` such that both compositions
`hom ≫ inv` and `inv ≫ hom` are homotopic to the identity.
-/
structure HomotopyEquiv where
  /-- the forward direction of a homotopy equivalence. -/
  hom : S₁ ⟶ S₂
  /-- the backwards direction of a homotopy equivalence. -/
  inv : S₂ ⟶ S₁
  /-- the composition of the two directions of a homotopy equivalence is
  homotopic to the identity of the source -/
  homotopyHomInvId : Homotopy (hom ≫ inv) (𝟙 S₁)
  /-- the composition of the two directions of a homotopy equivalence is
  homotopic to the identity of the target -/
  homotopyInvHomId : Homotopy (inv ≫ hom) (𝟙 S₂)

namespace HomotopyEquiv

variable {S₁ S₂}

/-- The homotopy equivalence from a short complex to itself that is induced
by the identity. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomotopyEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.HomotopyEquiv`。
形式化陈述：refl (S : ShortComplex C) : HomotopyEquiv S S where hom
参数：S : ShortComplex C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy equivalence from a short complex to itself that is induced
by the identity.
-/
def refl (S : ShortComplex C) : HomotopyEquiv S S where
  hom := 𝟙 S
  inv := 𝟙 S
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := Homotopy.ofEq (by simp)

/-- The inverse of a homotopy equivalence. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomotopyEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ShortComplex.HomotopyEquiv`。
形式化陈述：symm (e : HomotopyEquiv S₁ S₂) : HomotopyEquiv S₂ S₁ where hom
参数：e : HomotopyEquiv S₁ S₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a homotopy equivalence.
-/
def symm (e : HomotopyEquiv S₁ S₂) : HomotopyEquiv S₂ S₁ where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- The composition of homotopy equivalences. -/
@[simps]
/-
**CategoryTheory.ShortComplex.HomotopyEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.HomotopyEquiv`。
形式化陈述：trans (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃) : HomotopyEquiv
 S₁ S₃ where hom
参数：e : HomotopyEquiv S₁ S₂；e' : HomotopyEquiv S₂ S₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of homotopy equivalences.
-/
def trans (e : HomotopyEquiv S₁ S₂) (e' : HomotopyEquiv S₂ S₃) :
    HomotopyEquiv S₁ S₃ where
  hom := e.hom ≫ e'.hom
  inv := e'.inv ≫ e.inv
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans
    (((e'.homotopyHomInvId.compRight e.inv).compLeft e.hom).trans
      ((Homotopy.ofEq (by simp)).trans e.homotopyHomInvId))
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans
    (((e.homotopyInvHomId.compRight e'.hom).compLeft e'.inv).trans
      ((Homotopy.ofEq (by simp)).trans e'.homotopyInvHomId))

end HomotopyEquiv

end Homotopy

section

variable (S : ShortComplex C) [S.HasLeftHomology] {A : C}
    (k k' : A ⟶ S.X₂) (hk : k ≫ S.g = 0) (hk' : k' ≫ S.g = 0)

/-
**CategoryTheory.ShortComplex.add_liftCycles** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：add_liftCycles : S.liftCycles k hk + S.liftCycles k' hk' = S.liftCycles (k
 + k') (by rw [add_comp, hk, hk', add_zero])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_liftCycles :
    S.liftCycles k hk + S.liftCycles k' hk' =
      S.liftCycles (k + k') (by rw [add_comp, hk, hk', add_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, add_comp]
/-
**CategoryTheory.ShortComplex.sub_liftCycles** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShortComplex`。
形式化陈述：sub_liftCycles : S.liftCycles k hk - S.liftCycles k' hk' = S.liftCycles (k
 - k') (by rw [sub_comp, hk, hk', sub_zero])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.ShortComplex.instMonoICycles`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   (S : CategoryTheory.Sho…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用引理 `CategoryTheory.ShortComplex.liftCycles_i`：liftCycles_i : S.liftCycles k 
hk ≫ S.iCycles = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_liftCycles :
    S.liftCycles k hk - S.liftCycles k' hk' =
      S.liftCycles (k - k') (by rw [sub_comp, hk, hk', sub_zero]) := by
  simp only [← cancel_mono S.iCycles, liftCycles_i, sub_comp]

end

end ShortComplex

end CategoryTheory

