/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Shifted morphisms

Given a category `C` endowed with a shift by an additive monoid `M` and two
objects `X` and `Y` in `C`, we consider the types `ShiftedHom X Y m`
defined as `X ⟶ Y⟦m⟧` for all `m : M`, and the composition on these
shifted hom.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
  {M : Type*} [AddMonoid M] [HasShift C M] [HasShift D M] [HasShift E M]

/-- In a category `C` equipped with a shift by an additive monoid,
this is the type of morphisms `X ⟶ (Y⟦m⟧)` for `m : M`. -/
/-
**CategoryTheory.ShiftedHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ShiftedHom (X Y : C) (m : M) : Type _
参数：X Y : C；m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category `C` equipped with a shift by an additive monoid,
this is the type of morphisms `X ⟶ (Y⟦m⟧)` for `m : M`.
-/
abbrev ShiftedHom (X Y : C) (m : M) : Type _ := X ⟶ Y⟦m⟧

namespace ShiftedHom

variable {X Y Z T : C}

/-- The composition of `f : X ⟶ Y⟦a⟧` and `g : Y ⟶ Z⟦b⟧`, as a morphism `X ⟶ Z⟦c⟧`
when `b + a = c`. -/
/-
**CategoryTheory.ShiftedHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Shift
edHom`。
形式化陈述：comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a 
= c) : ShiftedHom X Z c
参数：f : ShiftedHom X Y a；g : ShiftedHom Y Z b；h : b + a = c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of `f : X ⟶ Y⟦a⟧` and `g : Y ⟶ Z⟦b⟧`, as a morphism `X ⟶ Z⟦c⟧`
when `b + a = c`.
-/
noncomputable def comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b + a = c) :
    ShiftedHom X Z c :=
  f ≫ g⟦a⟧' ≫ (shiftFunctorAdd' C b a c h).inv.app _
/-
**CategoryTheory.ShiftedHom.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.ShiftedHom`。
形式化陈述：comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : M} (α : ShiftedHom X Y a₁) (β : ShiftedHo
m Y Z a₂) (γ : ShiftedHom Z T a₃) (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h
 : a₃ + a₂ + a₁ = a) : (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← 
add_assoc, h]) = α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h])
参数：α : ShiftedHom X Y a₁；β : ShiftedHom Y Z a₂；γ : ShiftedHom Z T a₃；h₁₂ : a₂ + 
a₁ = a₁₂；h₂₃ : a₃ + a₂ = a₂₃；h : a₃ + a₂ + a₁ = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.shiftFunctorAdd'_assoc_inv_app`：∀ {C : Type u} {A : Type 
u_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddMonoid A]   [inst_2 
: CategoryTheory.HasShift C A] (a₁ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : M}
    (α : ShiftedHom X Y a₁) (β : ShiftedHom Y Z a₂) (γ : ShiftedHom Z T a₃)
    (h₁₂ : a₂ + a₁ = a₁₂) (h₂₃ : a₃ + a₂ = a₂₃) (h : a₃ + a₂ + a₁ = a) :
    (α.comp β h₁₂).comp γ (show a₃ + a₁₂ = a by rw [← h₁₂, ← add_assoc, h]) =
      α.comp (β.comp γ h₂₃) (by rw [← h₂₃, h]) := by
  simp only [comp, assoc, Functor.map_comp,
    shiftFunctorAdd'_assoc_inv_app a₃ a₂ a₁ a₂₃ a₁₂ a h₂₃ h₁₂ h,
    ← NatTrans.naturality_assoc, Functor.comp_map]

/-! In degree `0 : M`, shifted hom `ShiftedHom X Y 0` identify to morphisms `X ⟶ Y`.
We generalize this to `m₀ : M` such that `m₀ : 0` as it shall be convenient when we
apply this with `M := ℤ` and `m₀` the coercion of `0 : ℕ`. -/

/-- The element of `ShiftedHom X Y m₀` (when `m₀ = 0`) attached to a morphism `X ⟶ Y`. -/
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The element of `ShiftedHom X Y m₀` (when `m₀ = 0`) attached to a morphism `X ⟶ Y
`.
-/
noncomputable def mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) : ShiftedHom X Y m₀ :=
  f ≫ (shiftFunctorZero' C m₀ hm₀).inv.app Y

/-- The bijection `(X ⟶ Y) ≃ ShiftedHom X Y m₀` when `m₀ = 0`. -/
@[simps apply]
/-
**CategoryTheory.ShiftedHom.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：homEquiv (m₀ : M) (hm₀ : m₀ = 0) : (X ⟶ Y) ≃ ShiftedHom X Y m₀ where toFun
 f
参数：m₀ : M；hm₀ : m₀ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X ⟶ Y) ≃ ShiftedHom X Y m₀` when `m₀ = 0`.
-/
noncomputable def homEquiv (m₀ : M) (hm₀ : m₀ = 0) : (X ⟶ Y) ≃ ShiftedHom X Y m₀ where
  toFun f := mk₀ m₀ hm₀ f
  invFun g := g ≫ (shiftFunctorZero' C m₀ hm₀).hom.app Y
  left_inv f := by simp [mk₀]
  right_inv g := by simp [mk₀]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) :
    (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add_zero]) = f ≫ g := by
  subst hm₀
  simp [comp, mk₀, shiftFunctorAdd'_add_zero_inv_app, shiftFunctorZero']

@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 0) {a : M} (f : ShiftedHom X Y a) :
    (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_zero]) = f := by
  simp [mk₀_comp]
/-
**CategoryTheory.ShiftedHom.comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
iftedHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_mk₀ {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) :
    f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zero_add]) = f ≫ g⟦a⟧' := by
  subst hm₀
  simp only [comp, shiftFunctorAdd'_zero_add_inv_app, mk₀, shiftFunctorZero',
    eqToIso_refl, Iso.refl_trans, ← Functor.map_comp, assoc, Iso.inv_hom_id_app,
    Functor.id_obj, comp_id]

@[simp]
/-
**CategoryTheory.ShiftedHom.comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
iftedHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_mk₀_id {a : M} (f : ShiftedHom X Y a) (m₀ : M) (hm₀ : m₀ = 0) :
    f.comp (mk₀ m₀ hm₀ (𝟙 Y)) (by rw [hm₀, zero_add]) = f := by
  simp [comp_mk₀]

@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp_mk₀ (f : X ⟶ Y) (g : Y ⟶ Z) {a b c : M} (h : b + a = c)
    (ha : a = 0) (hb : b = 0) :
    (mk₀ a ha f).comp (mk₀ b hb g) h = mk₀ c (by rw [← h, ha, hb, add_zero]) (f ≫ g) := by
  subst ha hb
  obtain rfl : c = 0 := by rw [← h, zero_add]
  rw [mk₀_comp, mk₀, mk₀, assoc]

@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp_mk₀_assoc (f : X ⟶ Y) (g : Y ⟶ Z) {a : M}
    (ha : a = 0) {d : M} (h : ShiftedHom Z T d) :
    (mk₀ a ha f).comp ((mk₀ a ha g).comp h
        (show _ = d by rw [ha, add_zero])) (show _ = d by rw [ha, add_zero]) =
      (mk₀ a ha (f ≫ g)).comp h (by rw [ha, add_zero]) := by
  subst ha
  rw [← comp_assoc, mk₀_comp_mk₀]
  all_goals simp

section Preadditive

variable [Preadditive C]

variable (X Y) in
@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_zero (m₀ : M) (hm₀ : m₀ = 0) : mk₀ m₀ hm₀ (0 : X ⟶ Y) = 0 := by simp [mk₀]

@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_add (m₀ : M) (hm₀ : m₀ = 0) (f g : X ⟶ Y) :
    mk₀ m₀ hm₀ (f + g) = mk₀ m₀ hm₀ f + mk₀ m₀ hm₀ g := by simp [mk₀]

@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_neg (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) :
    mk₀ m₀ hm₀ (-f) = -mk₀ m₀ hm₀ f := by simp [mk₀]

@[simp]
/-
**CategoryTheory.ShiftedHom.comp_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：comp_add [forall (a : M), (shiftFunctor C a).Additive] {a b c : M} (α : Sh
iftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b) (h : b + a = c) : α.comp (β₁ + β₂) h 
= α.comp β₁ h + α.comp β₂ h
参数：a : M；shiftFunctor C a；α : ShiftedHom X Y a；β₁ β₂ : ShiftedHom Y Z b；h : b + 
a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
-/
lemma comp_add [∀ (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (β₁ + β₂) h = α.comp β₁ h + α.comp β₂ h := by
  rw [comp, comp, comp, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

@[simp]
/-
**CategoryTheory.ShiftedHom.add_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：add_comp {a b c : M} (α₁ α₂ : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h 
: b + a = c) : (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h
参数：α₁ α₂ : ShiftedHom X Y a；β : ShiftedHom Y Z b；h : b + a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
-/
lemma add_comp
    {a b c : M} (α₁ α₂ : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (α₁ + α₂).comp β h = α₁.comp β h + α₂.comp β h := by
  rw [comp, comp, comp, Preadditive.add_comp]

@[simp]
/-
**CategoryTheory.ShiftedHom.comp_neg** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：comp_neg [forall (a : M), (shiftFunctor C a).Additive] {a b c : M} (α : Sh
iftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) : α.comp (-β) h = -α.comp
 β h
参数：a : M；shiftFunctor C a；α : ShiftedHom X Y a；β : ShiftedHom Y Z b；h : b + a = 
c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Functor.map_neg`：map_neg {X Y : C} {f : X ⟶ Y} : F.map (-
f) = -F.map f
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
-/
lemma comp_neg [∀ (a : M), (shiftFunctor C a).Additive]
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (-β) h = -α.comp β h := by
  rw [comp, comp, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg]

@[simp]
/-
**CategoryTheory.ShiftedHom.neg_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：neg_comp {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b 
+ a = c) : (-α).comp β h = -α.comp β h
参数：α : ShiftedHom X Y a；β : ShiftedHom Y Z b；h : b + a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
-/
lemma neg_comp
    {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (-α).comp β h = -α.comp β h := by
  rw [comp, comp, Preadditive.neg_comp]

variable (Z) in
@[simp]
/-
**CategoryTheory.ShiftedHom.comp_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ShiftedHom`。
形式化陈述：comp_zero [forall (a : M), (shiftFunctor C a).PreservesZeroMorphisms] {a :
 M} (β : ShiftedHom X Y a) {b c : M} (h : b + a = c) : β.comp (0 : ShiftedHom Y 
Z b) h = 0
参数：a : M；shiftFunctor C a；β : ShiftedHom X Y a；h : b + a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
lemma comp_zero [∀ (a : M), (shiftFunctor C a).PreservesZeroMorphisms]
    {a : M} (β : ShiftedHom X Y a) {b c : M} (h : b + a = c) :
    β.comp (0 : ShiftedHom Y Z b) h = 0 := by
  rw [comp, Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

variable (X) in
@[simp]
/-
**CategoryTheory.ShiftedHom.zero_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ShiftedHom`。
形式化陈述：zero_comp (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c) : (0 : 
ShiftedHom X Y a).comp β h = 0
参数：a : M；β : ShiftedHom Y Z b；h : b + a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
lemma zero_comp (a : M) {b c : M} (β : ShiftedHom Y Z b) (h : b + a = c) :
    (0 : ShiftedHom X Y a).comp β h = 0 := by
  rw [comp, Limits.zero_comp]

end Preadditive

/-- The action on `ShiftedHom` of a functor which commutes with the shift. -/
/-
**CategoryTheory.ShiftedHom.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Shifte
dHom`。
形式化陈述：map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] : ShiftedHo
m (F.obj X) (F.obj Y) a
参数：f : ShiftedHom X Y a；F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on `ShiftedHom` of a functor which commutes with the shift.
-/
def map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] :
    ShiftedHom (F.obj X) (F.obj Y) a :=
  F.map f ≫ (F.commShiftIso a).hom.app Y

@[simp]
/-
**CategoryTheory.ShiftedHom.map_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shi
ftedHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mk₀ (m₀ : M) (hm₀ : m₀ = 0) (f : X ⟶ Y) (F : C ⥤ D) [F.CommShift M] :
    (ShiftedHom.mk₀ m₀ hm₀ f).map F = .mk₀ _ hm₀ (F.map f) := by
  subst hm₀
  simp [map, mk₀, shiftFunctorZero', F.commShiftIso_zero M, ← Functor.map_comp_assoc]

@[simp]
/-
**CategoryTheory.ShiftedHom.id_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shi
ftedHom`。
形式化陈述：id_map {a : M} (f : ShiftedHom X Y a) : f.map (𝟭 C) = f
参数：f : ShiftedHom X Y a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_map {a : M} (f : ShiftedHom X Y a) : f.map (𝟭 C) = f := by
  simp [map]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShiftedHom.comp_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：comp_map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] (G : D
 ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f.map F).map G
参数：f : ShiftedHom X Y a；F : C ⥤ D；G : D ⥤ E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_map {a : M} (f : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M]
    (G : D ⥤ E) [G.CommShift M] : f.map (F ⋙ G) = (f.map F).map G := by
  simp [map, Functor.commShiftIso_comp_hom_app]
/-
**CategoryTheory.ShiftedHom.map_naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ShiftedHom`。
形式化陈述：map_naturality {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G) [F
.CommShift M] [G.CommShift M] [NatTrans.CommShift τ M] : (f.map F).comp (mk₀ 0 r
fl (τ.app Y)) (zero_add _) = (mk₀ 0 rfl (τ.app X)).comp (f.map G) (add_zero _)
参数：f : ShiftedHom X Y a；τ : F ⟶ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀`：comp_mk₀ {a : M} (f : ShiftedHom X Y
 a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) : f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zer
o_add]) = f ≫ g⟦a⟧'
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
· 使用定理 `CategoryTheory.ShiftedHom.map.eq_1`：∀ {C : Type u_1} [inst : CategoryThe
ory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v
_2, u_2} D] {M : Type u_…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
-/
lemma map_naturality {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift τ M] :
    (f.map F).comp (mk₀ 0 rfl (τ.app Y)) (zero_add _) =
      (mk₀ 0 rfl (τ.app X)).comp (f.map G) (add_zero _) := by
  rw [comp_mk₀, mk₀_comp, map, map, Category.assoc, ← τ.naturality_assoc,
    τ.shift_app_comm a]

@[simp]
/-
**CategoryTheory.ShiftedHom.map_naturality_1** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShiftedHom`。
形式化陈述：map_naturality_1 {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G) 
[F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] : (mk₀ 0 rfl (e.inv
.app X)).comp ((f.map F).comp (mk₀ 0 rfl (e.hom.app Y)) (zero_add _)) (add_zero 
_) = f.map G
参数：f : ShiftedHom X Y a；e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.ShiftedHom.map_naturality`：map_naturality {a : M} (f : Sh
iftedHom X Y a) {F G : C ⥤ D} (τ : F ⟶ G) [F.CommShift M] [G.CommShift M] [NatTr
ans.CommShift τ M] : (f.map F)…
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp_mk₀_assoc`：mk₀_comp_mk₀_assoc (f : X 
⟶ Y) (g : Y ⟶ Z) {a : M} (ha : a = 0) {d : M} (h : ShiftedHom Z T d) : (mk₀ a ha
 f).comp ((mk₀ a ha g).comp h (sho…
· 使用定理 `CategoryTheory.ShiftedHom.mk₀.congr_simp`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2
 : CategoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_id_comp`：mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 
0) {a : M} (f : ShiftedHom X Y a) : (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_z
ero]) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_naturality_1
    {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] :
    (mk₀ 0 rfl (e.inv.app X)).comp ((f.map F).comp
      (mk₀ 0 rfl (e.hom.app Y)) (zero_add _)) (add_zero _) = f.map G := by
  simp [map_naturality]

@[simp]
/-
**CategoryTheory.ShiftedHom.map_naturality_2** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ShiftedHom`。
形式化陈述：map_naturality_2 {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G) 
[F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] : (mk₀ 0 rfl (e.hom
.app X)).comp ((f.map G).comp (mk₀ 0 rfl (e.inv.app Y)) (zero_add _)) (add_zero 
_) = f.map F
参数：f : ShiftedHom X Y a；e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShiftedHom.map_naturality_1`：map_naturality_1 {a : M} (f 
: ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G) [F.CommShift M] [G.CommShift M] [N
atTrans.CommShift e.hom M] : (mk…
-/
lemma map_naturality_2
    {a : M} (f : ShiftedHom X Y a) {F G : C ⥤ D} (e : F ≅ G)
    [F.CommShift M] [G.CommShift M] [NatTrans.CommShift e.hom M] :
    (mk₀ 0 rfl (e.hom.app X)).comp ((f.map G).comp
      (mk₀ 0 rfl (e.inv.app Y)) (zero_add _)) (add_zero _) = f.map F :=
  map_naturality_1 f e.symm

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShiftedHom.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：map_comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (h : b 
+ a = c) (F : C ⥤ D) [F.CommShift M] : (f.comp g h).map F = (f.map F).comp (g.ma
p F) h
参数：f : ShiftedHom X Y a；g : ShiftedHom Y Z b；h : b + a = c；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.Functor.commShiftIso_add'`：commShiftIso_add' {a b c : A} 
(h : a + b = c) : F.commShiftIso c = CommShift.isoAdd' h (F.commShiftIso a) (F.c
ommShiftIso b)
· 使用定理 `CategoryTheory.Functor.CommShift.isoAdd'_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] {F : Categor…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp {a b c : M} (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b)
    (h : b + a = c) (F : C ⥤ D) [F.CommShift M] :
    (f.comp g h).map F = (f.map F).comp (g.map F) h := by
  dsimp [comp, map]
  simp only [Functor.map_comp, assoc, ← Functor.commShiftIso_hom_naturality_assoc]
  simp only [F.commShiftIso_add' h, Functor.CommShift.isoAdd'_hom_app,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.comp_obj, comp_id]

section Preadditive

variable [Preadditive C] [Preadditive D]

@[simp]
/-
**CategoryTheory.ShiftedHom.map_add** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sh
iftedHom`。
形式化陈述：map_add {a : M} (α₁ α₂ : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.
Additive] : (α₁ + α₂).map F = α₁.map F + α₂.map F
参数：α₁ α₂ : ShiftedHom X Y a；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_add {a : M} (α₁ α₂ : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Additive] :
    (α₁ + α₂).map F = α₁.map F + α₂.map F := by
  simp [ShiftedHom.map, F.map_add]

@[simp]
/-
**CategoryTheory.ShiftedHom.map_zero** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：map_zero {a : M} (F : C ⥤ D) [F.CommShift M] [F.Additive] : (0 : ShiftedHo
m X Y a).map F = 0
参数：F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_zero {a : M} (F : C ⥤ D) [F.CommShift M] [F.Additive] :
    (0 : ShiftedHom X Y a).map F = 0 := by
  simp [ShiftedHom.map]

end Preadditive

section Linear

variable {R : Type*} [Ring R] [Preadditive C] [Linear R C]

@[simp]
/-
**CategoryTheory.ShiftedHom.comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ShiftedHom`。
形式化陈述：comp_smul [forall (a : M), Functor.Linear R (shiftFunctor C a)] (r : R) {a
 b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) : α.comp
 (r • β) h = r • α.comp β h
参数：a : M；shiftFunctor C a；r : R；α : ShiftedHom X Y a；β : ShiftedHom Y Z b；h : b 
+ a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
-/
lemma comp_smul
    [∀ (a : M), Functor.Linear R (shiftFunctor C a)]
    (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    α.comp (r • β) h = r • α.comp β h := by
  rw [comp, Functor.map_smul, comp, Linear.smul_comp, Linear.comp_smul]

@[simp]
/-
**CategoryTheory.ShiftedHom.smul_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ShiftedHom`。
形式化陈述：smul_comp (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b
) (h : b + a = c) : (r • α).comp β h = r • α.comp β h
参数：r : R；α : ShiftedHom X Y a；β : ShiftedHom Y Z b；h : b + a = c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ShiftedHom.comp.eq_1`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2 : Ca
tegoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
-/
lemma smul_comp
    (r : R) {a b c : M} (α : ShiftedHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) :
    (r • α).comp β h = r • α.comp β h := by
  rw [comp, comp, Linear.smul_comp]

@[simp]
/-
**CategoryTheory.ShiftedHom.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Shifted
Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_smul (m₀ : M) (hm₀ : m₀ = 0) (r : R) {f : X ⟶ Y} :
    mk₀ m₀ hm₀ (r • f) = r • mk₀ m₀ hm₀ f := by
  simp [mk₀]

variable [Preadditive D] [Linear R D]

@[simp]
/-
**CategoryTheory.ShiftedHom.map_smul** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hiftedHom`。
形式化陈述：map_smul (r : R) {a : M} (α : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M
] [F.Linear R] : (r • α).map F = r • (α.map F)
参数：r : R；α : ShiftedHom X Y a；F : C ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_smul`：map_smul {X Y : C} (r : R) (f : X ⟶ Y) 
: F.map (r • f) = r • F.map f
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_smul (r : R) {a : M} (α : ShiftedHom X Y a) (F : C ⥤ D) [F.CommShift M] [F.Linear R] :
    (r • α).map F = r • (α.map F) := by
  simp [ShiftedHom.map, F.map_smul]

end Linear

end ShiftedHom

end CategoryTheory

