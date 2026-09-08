/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts

/-!
# Limits involving zero objects

Binary products and coproducts with a zero object always exist,
and pullbacks/pushouts over a zero object are products/coproducts.
-/

@[expose] public section


noncomputable section

open CategoryTheory

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

/-- The limit cone for the product with a zero object. -/
/-
**CategoryTheory.Limits.binaryFanZeroLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：binaryFanZeroLeft (X : C) : BinaryFan (0 : C) X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for the product with a zero object.
-/
def binaryFanZeroLeft (X : C) : BinaryFan (0 : C) X :=
  BinaryFan.mk 0 (𝟙 X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The limit cone for the product with a zero object is limiting. -/
/-
**CategoryTheory.Limits.binaryFanZeroLeftIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：binaryFanZeroLeftIsLimit (X : C) : IsLimit (binaryFanZeroLeft X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for the product with a zero object is limiting.
-/
def binaryFanZeroLeftIsLimit (X : C) : IsLimit (binaryFanZeroLeft X) :=
  BinaryFan.isLimitMk (fun s => BinaryFan.snd s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)
/-
**CategoryTheory.Limits.hasBinaryProduct_zero_left** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasBinaryProduct_zero_left (X : C) : HasBinaryProduct (0 : C) X
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasBinaryProduct_zero_left (X : C) : HasBinaryProduct (0 : C) X :=
  HasLimit.mk ⟨_, binaryFanZeroLeftIsLimit X⟩

/-- A zero object is a left unit for categorical product. -/
/-
**CategoryTheory.Limits.zeroProdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：zeroProdIso (X : C) : (0 : C) ⨯ X ≅ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is a left unit for categorical product.
-/
def zeroProdIso (X : C) : (0 : C) ⨯ X ≅ X :=
  limit.isoLimitCone ⟨_, binaryFanZeroLeftIsLimit X⟩

@[simp]
/-
**CategoryTheory.Limits.zeroProdIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：zeroProdIso_hom (X : C) : (zeroProdIso X).hom = prod.snd
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroProdIso_hom (X : C) : (zeroProdIso X).hom = prod.snd :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.zeroProdIso_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：zeroProdIso_inv_snd (X : C) : (zeroProdIso X).inv ≫ prod.snd = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zeroProdIso_inv_snd (X : C) : (zeroProdIso X).inv ≫ prod.snd = 𝟙 X := by
  dsimp [zeroProdIso, binaryFanZeroLeft]
  simp

/-- The limit cone for the product with a zero object. -/
/-
**CategoryTheory.Limits.binaryFanZeroRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：binaryFanZeroRight (X : C) : BinaryFan X (0 : C)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for the product with a zero object.
-/
def binaryFanZeroRight (X : C) : BinaryFan X (0 : C) :=
  BinaryFan.mk (𝟙 X) 0

set_option backward.isDefEq.respectTransparency.types false in
/-- The limit cone for the product with a zero object is limiting. -/
/-
**CategoryTheory.Limits.binaryFanZeroRightIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：binaryFanZeroRightIsLimit (X : C) : IsLimit (binaryFanZeroRight X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for the product with a zero object is limiting.
-/
def binaryFanZeroRightIsLimit (X : C) : IsLimit (binaryFanZeroRight X) :=
  BinaryFan.isLimitMk (fun s => BinaryFan.fst s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)
/-
**CategoryTheory.Limits.hasBinaryProduct_zero_right** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：hasBinaryProduct_zero_right (X : C) : HasBinaryProduct X (0 : C)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasBinaryProduct_zero_right (X : C) : HasBinaryProduct X (0 : C) :=
  HasLimit.mk ⟨_, binaryFanZeroRightIsLimit X⟩

/-- A zero object is a right unit for categorical product. -/
/-
**CategoryTheory.Limits.prodZeroIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：prodZeroIso (X : C) : X ⨯ (0 : C) ≅ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is a right unit for categorical product.
-/
def prodZeroIso (X : C) : X ⨯ (0 : C) ≅ X :=
  limit.isoLimitCone ⟨_, binaryFanZeroRightIsLimit X⟩

@[simp]
/-
**CategoryTheory.Limits.prodZeroIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：prodZeroIso_hom (X : C) : (prodZeroIso X).hom = prod.fst
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodZeroIso_hom (X : C) : (prodZeroIso X).hom = prod.fst :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.prodZeroIso_iso_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：prodZeroIso_iso_inv_snd (X : C) : (prodZeroIso X).inv ≫ prod.fst = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodZeroIso_iso_inv_snd (X : C) : (prodZeroIso X).inv ≫ prod.fst = 𝟙 X := by
  dsimp [prodZeroIso, binaryFanZeroRight]
  simp

/-- The colimit cocone for the coproduct with a zero object. -/
/-
**CategoryTheory.Limits.binaryCofanZeroLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：binaryCofanZeroLeft (X : C) : BinaryCofan (0 : C) X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for the coproduct with a zero object.
-/
def binaryCofanZeroLeft (X : C) : BinaryCofan (0 : C) X :=
  BinaryCofan.mk 0 (𝟙 X)

set_option backward.isDefEq.respectTransparency.types false in
/-- The colimit cocone for the coproduct with a zero object is colimiting. -/
/-
**CategoryTheory.Limits.binaryCofanZeroLeftIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：binaryCofanZeroLeftIsColimit (X : C) : IsColimit (binaryCofanZeroLeft X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for the coproduct with a zero object is colimiting.
-/
def binaryCofanZeroLeftIsColimit (X : C) : IsColimit (binaryCofanZeroLeft X) :=
  BinaryCofan.isColimitMk (fun s => BinaryCofan.inr s) (by cat_disch) (by simp)
    (fun s m _ h₂ => by simpa using h₂)
/-
**CategoryTheory.Limits.hasBinaryCoproduct_zero_left** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasBinaryCoproduct_zero_left (X : C) : HasBinaryCoproduct (0 : C) X
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasBinaryCoproduct_zero_left (X : C) : HasBinaryCoproduct (0 : C) X :=
  HasColimit.mk ⟨_, binaryCofanZeroLeftIsColimit X⟩

/-- A zero object is a left unit for categorical coproduct. -/
/-
**CategoryTheory.Limits.zeroCoprodIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：zeroCoprodIso (X : C) : (0 : C) ⨿ X ≅ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is a left unit for categorical coproduct.
-/
def zeroCoprodIso (X : C) : (0 : C) ⨿ X ≅ X :=
  colimit.isoColimitCocone ⟨_, binaryCofanZeroLeftIsColimit X⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.inr_zeroCoprodIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：inr_zeroCoprodIso_hom (X : C) : coprod.inr ≫ (zeroCoprodIso X).hom = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_zeroCoprodIso_hom (X : C) : coprod.inr ≫ (zeroCoprodIso X).hom = 𝟙 X := by
  dsimp [zeroCoprodIso, binaryCofanZeroLeft]
  simp

@[simp]
/-
**CategoryTheory.Limits.zeroCoprodIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：zeroCoprodIso_inv (X : C) : (zeroCoprodIso X).inv = coprod.inr
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zeroCoprodIso_inv (X : C) : (zeroCoprodIso X).inv = coprod.inr :=
  rfl

/-- The colimit cocone for the coproduct with a zero object. -/
/-
**CategoryTheory.Limits.binaryCofanZeroRight** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：binaryCofanZeroRight (X : C) : BinaryCofan X (0 : C)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for the coproduct with a zero object.
-/
def binaryCofanZeroRight (X : C) : BinaryCofan X (0 : C) :=
  BinaryCofan.mk (𝟙 X) 0

set_option backward.isDefEq.respectTransparency.types false in
/-- The colimit cocone for the coproduct with a zero object is colimiting. -/
/-
**CategoryTheory.Limits.binaryCofanZeroRightIsColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：binaryCofanZeroRightIsColimit (X : C) : IsColimit (binaryCofanZeroRight X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for the coproduct with a zero object is colimiting.
-/
def binaryCofanZeroRightIsColimit (X : C) : IsColimit (binaryCofanZeroRight X) :=
  BinaryCofan.isColimitMk (fun s => BinaryCofan.inl s) (by simp) (by cat_disch)
    (fun s m h₁ _ => by simpa using h₁)
/-
**CategoryTheory.Limits.hasBinaryCoproduct_zero_right** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasBinaryCoproduct_zero_right (X : C) : HasBinaryCoproduct X (0 : C)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasBinaryCoproduct_zero_right (X : C) : HasBinaryCoproduct X (0 : C) :=
  HasColimit.mk ⟨_, binaryCofanZeroRightIsColimit X⟩

/-- A zero object is a right unit for categorical coproduct. -/
/-
**CategoryTheory.Limits.coprodZeroIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：coprodZeroIso (X : C) : X ⨿ (0 : C) ≅ X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero object is a right unit for categorical coproduct.
-/
def coprodZeroIso (X : C) : X ⨿ (0 : C) ≅ X :=
  colimit.isoColimitCocone ⟨_, binaryCofanZeroRightIsColimit X⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.inr_coprodZeroIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：inr_coprodZeroIso_hom (X : C) : coprod.inl ≫ (coprodZeroIso X).hom = 𝟙 X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_coprodZeroIso_hom (X : C) : coprod.inl ≫ (coprodZeroIso X).hom = 𝟙 X := by
  dsimp [coprodZeroIso, binaryCofanZeroRight]
  simp

@[simp]
/-
**CategoryTheory.Limits.coprodZeroIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：coprodZeroIso_inv (X : C) : (coprodZeroIso X).inv = coprod.inl
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coprodZeroIso_inv (X : C) : (coprodZeroIso X).inv = coprod.inl :=
  rfl
/-
**CategoryTheory.Limits.hasPullback_over_zero** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasPullback_over_zero (X Y : C) [HasBinaryProduct X Y] : HasPullback (0 : 
X ⟶ 0) (0 : Y ⟶ 0)
参数：X Y : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
instance hasPullback_over_zero (X Y : C) [HasBinaryProduct X Y] :
    HasPullback (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  HasLimit.mk
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

/-- The pullback over the zero object is the product. -/
/-
**CategoryTheory.Limits.pullbackZeroZeroIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：pullbackZeroZeroIso (X Y : C) [HasBinaryProduct X Y] : pullback (0 : X ⟶ 0
) (0 : Y ⟶ 0) ≅ X ⨯ Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback over the zero object is the product.
-/
def pullbackZeroZeroIso (X Y : C) [HasBinaryProduct X Y] :
    pullback (0 : X ⟶ 0) (0 : Y ⟶ 0) ≅ X ⨯ Y :=
  limit.isoLimitCone
    ⟨_, isPullbackOfIsTerminalIsProduct _ _ _ _ HasZeroObject.zeroIsTerminal (prodIsProd X Y)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pullbackZeroZeroIso_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackZeroZeroIso_inv_fst (X Y : C) [HasBinaryProduct X Y] : (pullbackZe
roZeroIso X Y).inv ≫ pullback.fst 0 0 = prod.fst
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackZeroZeroIso_inv_fst (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).inv ≫ pullback.fst 0 0 = prod.fst := by
  dsimp [pullbackZeroZeroIso]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.pullbackZeroZeroIso_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackZeroZeroIso_inv_snd (X Y : C) [HasBinaryProduct X Y] : (pullbackZe
roZeroIso X Y).inv ≫ pullback.snd 0 0 = prod.snd
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackZeroZeroIso_inv_snd (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).inv ≫ pullback.snd 0 0 = prod.snd := by
  dsimp [pullbackZeroZeroIso]
  simp

@[simp]
/-
**CategoryTheory.Limits.pullbackZeroZeroIso_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackZeroZeroIso_hom_fst (X Y : C) [HasBinaryProduct X Y] : (pullbackZe
roZeroIso X Y).hom ≫ prod.fst = pullback.fst 0 0
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullbackZeroZeroIso_inv_fst`：pullbackZeroZeroIso_i
nv_fst (X Y : C) [HasBinaryProduct X Y] : (pullbackZeroZeroIso X Y).inv ≫ pullba
ck.fst 0 0 = prod.fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackZeroZeroIso_hom_fst (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).hom ≫ prod.fst = pullback.fst 0 0 := by simp [← Iso.eq_inv_comp]

@[simp]
/-
**CategoryTheory.Limits.pullbackZeroZeroIso_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackZeroZeroIso_hom_snd (X Y : C) [HasBinaryProduct X Y] : (pullbackZe
roZeroIso X Y).hom ≫ prod.snd = pullback.snd 0 0
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullbackZeroZeroIso_inv_snd`：pullbackZeroZeroIso_i
nv_snd (X Y : C) [HasBinaryProduct X Y] : (pullbackZeroZeroIso X Y).inv ≫ pullba
ck.snd 0 0 = prod.snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackZeroZeroIso_hom_snd (X Y : C) [HasBinaryProduct X Y] :
    (pullbackZeroZeroIso X Y).hom ≫ prod.snd = pullback.snd 0 0 := by simp [← Iso.eq_inv_comp]
/-
**CategoryTheory.Limits.hasPushout_over_zero** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasPushout_over_zero (X Y : C) [HasBinaryCoproduct X Y] : HasPushout (0 : 
0 ⟶ X) (0 : 0 ⟶ Y)
参数：X Y : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
instance hasPushout_over_zero (X Y : C) [HasBinaryCoproduct X Y] :
    HasPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) :=
  HasColimit.mk
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

/-- The pushout over the zero object is the coproduct. -/
/-
**CategoryTheory.Limits.pushoutZeroZeroIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pushoutZeroZeroIso (X Y : C) [HasBinaryCoproduct X Y] : pushout (0 : 0 ⟶ X
) (0 : 0 ⟶ Y) ≅ X ⨿ Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout over the zero object is the coproduct.
-/
def pushoutZeroZeroIso (X Y : C) [HasBinaryCoproduct X Y] :
    pushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) ≅ X ⨿ Y :=
  colimit.isoColimitCocone
    ⟨_, isPushoutOfIsInitialIsCoproduct _ _ _ _ HasZeroObject.zeroIsInitial (coprodIsCoprod X Y)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.inl_pushoutZeroZeroIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inl_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] : pushout.in
l _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inl
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] :
    pushout.inl _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inl := by
  dsimp [pushoutZeroZeroIso]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.inr_pushoutZeroZeroIso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inr_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] : pushout.in
r _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inr
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_pushoutZeroZeroIso_hom (X Y : C) [HasBinaryCoproduct X Y] :
    pushout.inr _ _ ≫ (pushoutZeroZeroIso X Y).hom = coprod.inr := by
  dsimp [pushoutZeroZeroIso]
  simp

@[simp]
/-
**CategoryTheory.Limits.inl_pushoutZeroZeroIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inl_pushoutZeroZeroIso_inv (X Y : C) [HasBinaryCoproduct X Y] : coprod.inl
 ≫ (pushoutZeroZeroIso X Y).inv = pushout.inl _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inl_pushoutZeroZeroIso_hom`：inl_pushoutZeroZeroIso
_hom (X Y : C) [HasBinaryCoproduct X Y] : pushout.inl _ _ ≫ (pushoutZeroZeroIso 
X Y).hom = coprod.inl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_pushoutZeroZeroIso_inv (X Y : C) [HasBinaryCoproduct X Y] :
    coprod.inl ≫ (pushoutZeroZeroIso X Y).inv = pushout.inl _ _ := by simp [Iso.comp_inv_eq]

@[simp]
/-
**CategoryTheory.Limits.inr_pushoutZeroZeroIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：inr_pushoutZeroZeroIso_inv (X Y : C) [HasBinaryCoproduct X Y] : coprod.inr
 ≫ (pushoutZeroZeroIso X Y).inv = pushout.inr _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.inr_pushoutZeroZeroIso_hom`：inr_pushoutZeroZeroIso
_hom (X Y : C) [HasBinaryCoproduct X Y] : pushout.inr _ _ ≫ (pushoutZeroZeroIso 
X Y).hom = coprod.inr
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inr_pushoutZeroZeroIso_inv (X Y : C) [HasBinaryCoproduct X Y] :
    coprod.inr ≫ (pushoutZeroZeroIso X Y).inv = pushout.inr _ _ := by simp [Iso.comp_inv_eq]

end CategoryTheory.Limits

