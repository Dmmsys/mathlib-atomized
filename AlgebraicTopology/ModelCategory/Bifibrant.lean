/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Bifibrant objects

In this file, we introduce the full subcategories `CofibrantObject C`,
`FibrantObject C` and `BifibrantObject C` of a model category `C` which
respectively consist of cofibrant objects, fibrant objects,
and bifibrant objects, where "bifibrant" means both cofibrant and fibrant.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

variable (C) in
/-- The property that is satisfied by cofibrant objects.
(This is only introduced in order to consider the full subcategory
`CofibrantObject`. Otherwise, the typeclass `IsCofibrant`
is preferred.) -/
/-
**HomotopicalAlgebra.cofibrantObjects** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：cofibrantObjects : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that is satisfied by cofibrant objects.
(This is only introduced in order to consider the full subcategory
`CofibrantObject`. Otherwise, the typeclass `IsCofibrant`
is preferred.)
-/
def cofibrantObjects : ObjectProperty C := IsCofibrant

variable (C) in
/-- The full subcategory of cofibrant objects. -/
/-
**HomotopicalAlgebra.CofibrantObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAlg
ebra`。
形式化陈述：CofibrantObject : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of cofibrant objects.
-/
abbrev CofibrantObject : Type u := (cofibrantObjects C).FullSubcategory

namespace CofibrantObject

/-- Constructor for `CofibrantObject C`. -/
/-
**HomotopicalAlgebra.CofibrantObject.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopical
Algebra.CofibrantObject`。
形式化陈述：mk (X : C) [IsCofibrant X] : CofibrantObject C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `CofibrantObject C`.
-/
abbrev mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩
/-
**HomotopicalAlgebra.CofibrantObject.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ho
motopicalAlgebra.CofibrantObject`。
形式化陈述：mk_surjective (X : CofibrantObject C) : exists (Y : C) (_ : IsCofibrant Y)
, X = mk Y
参数：X : CofibrantObject C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma mk_surjective (X : CofibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `CofibrantObject C`. -/
/-
**HomotopicalAlgebra.CofibrantObject.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopi
calAlgebra.CofibrantObject`。
形式化陈述：homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) : mk X ⟶ mk Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `CofibrantObject C`.
-/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f
/-
**HomotopicalAlgebra.CofibrantObject.homMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.CofibrantObject`。
形式化陈述：homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : mk X ⟶ mk 
Y) : exists (g : X ⟶ Y), f = homMk g
参数：f : mk X ⟶ mk Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
/-
**HomotopicalAlgebra.CofibrantObject.weakEquivalence_homMk_iff** 是 Mathlib 中的一个引
理，位于命名空间 `HomotopicalAlgebra.CofibrantObject`。
形式化陈述：weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C} [IsCo
fibrant X] [IsCofibrant Y] (f : X ⟶ Y) : WeakEquivalence (homMk f) ↔ WeakEquival
ence f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
/-
**HomotopicalAlgebra.CofibrantObject.homMk_id** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.CofibrantObject`。
形式化陈述：homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.CofibrantObject.homMk_homMk** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra.CofibrantObject`。
形式化陈述：homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] (f
 : X ⟶ Y) (g : Y ⟶ Z) : homMk f ≫ homMk g = homMk (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `CofibrantObject C ⥤ C`. -/
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAl
gebra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `CofibrantObject C ⥤ C`.
-/
abbrev ι : CofibrantObject C ⥤ C := (cofibrantObjects C).ι
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) : IsCofibrant X.1 := X.2
/-
**HomotopicalAlgebra.CofibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.CofibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : CofibrantObject C) : IsCofibrant (CofibrantObject.ι.obj X) := X.2

end CofibrantObject

end Cofibrant

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by fibrant objects.
(This is only introduced in order to consider the full subcategory
`FibrantObject`. Otherwise, the typeclass `IsFibrant`
is preferred.) -/
/-
**HomotopicalAlgebra.fibrantObjects** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlgebr
a`。
形式化陈述：fibrantObjects : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that is satisfied by fibrant objects.
(This is only introduced in order to consider the full subcategory
`FibrantObject`. Otherwise, the typeclass `IsFibrant`
is preferred.)
-/
def fibrantObjects : ObjectProperty C := fun X ↦ IsFibrant X

variable (C) in
/-- The full subcategory of fibrant objects. -/
/-
**HomotopicalAlgebra.FibrantObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAlgeb
ra`。
形式化陈述：FibrantObject : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of fibrant objects.
-/
abbrev FibrantObject : Type u := (fibrantObjects C).FullSubcategory

namespace FibrantObject

/-- Constructor for `FibrantObject C`. -/
/-
**HomotopicalAlgebra.FibrantObject.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAl
gebra.FibrantObject`。
形式化陈述：mk (X : C) [IsFibrant X] : FibrantObject C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `FibrantObject C`.
-/
abbrev mk (X : C) [IsFibrant X] : FibrantObject C :=
  ⟨X, by assumption⟩
/-
**HomotopicalAlgebra.FibrantObject.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra.FibrantObject`。
形式化陈述：mk_surjective (X : FibrantObject C) : exists (Y : C) (_ : IsFibrant Y), X 
= mk Y
参数：X : FibrantObject C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
lemma mk_surjective (X : FibrantObject C) :
    ∃ (Y : C) (_ : IsFibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/-- Constructor for morphisms in `FibrantObject C`. -/
/-
**HomotopicalAlgebra.FibrantObject.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopica
lAlgebra.FibrantObject`。
形式化陈述：homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) : mk X ⟶ mk Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `FibrantObject C`.
-/
abbrev homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f
/-
**HomotopicalAlgebra.FibrantObject.homMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `H
omotopicalAlgebra.FibrantObject`。
形式化陈述：homMk_surjective {X Y : C} [IsFibrant X] [IsFibrant Y] (f : mk X ⟶ mk Y) :
 exists (g : X ⟶ Y), f = homMk g
参数：f : mk X ⟶ mk Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_surjective {X Y : C} [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
/-
**HomotopicalAlgebra.FibrantObject.weakEquivalence_homMk_iff** 是 Mathlib 中的一个引理，
位于命名空间 `HomotopicalAlgebra.FibrantObject`。
形式化陈述：weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C} [IsFi
brant X] [IsFibrant Y] (f : X ⟶ Y) : WeakEquivalence (homMk f) ↔ WeakEquivalence
 f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
/-
**HomotopicalAlgebra.FibrantObject.homMk_id** 是 Mathlib 中的一个引理，位于命名空间 `Homotopic
alAlgebra.FibrantObject`。
形式化陈述：homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.FibrantObject.homMk_homMk** 是 Mathlib 中的一个引理，位于命名空间 `Homoto
picalAlgebra.FibrantObject`。
形式化陈述：homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z] (f : X ⟶
 Y) (g : Y ⟶ Z) : homMk f ≫ homMk g = homMk (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `FibrantObject C ⥤ C`. -/
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAlge
bra.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `FibrantObject C ⥤ C`.
-/
abbrev ι : FibrantObject C ⥤ C := (fibrantObjects C).ι
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FibrantObject C) : IsFibrant X.1 := X.2
/-
**HomotopicalAlgebra.FibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlgebr
a.FibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end FibrantObject

end Fibrant

section Bifibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/-- The property that is satisfied by bifibrant objects, i.e. objects
that are both cofibrant and fibrant.
(This is only introduced in order to consider the full subcategory
`BifibrantObject`. Otherwise, the typeclasses `IsCofibrant` and
`IsFibrant` are preferred.) -/
/-
**HomotopicalAlgebra.bifibrantObjects** 是 Mathlib 中的一个定义，位于命名空间 `HomotopicalAlge
bra`。
形式化陈述：bifibrantObjects : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that is satisfied by bifibrant objects, i.e. objects
that are both cofibrant and fibrant.
(This is only introduced in order to consider the full subcategory
`BifibrantObject`. Otherwise, the typeclasses `IsCofibrant` and
`IsFibrant` are preferred.)
-/
def bifibrantObjects : ObjectProperty C :=
  cofibrantObjects C ⊓ fibrantObjects C

variable (C) in
/-
**HomotopicalAlgebra.bifibrantObjects_le_cofibrantObject** 是 Mathlib 中的一个引理，位于命名
空间 `HomotopicalAlgebra`。
形式化陈述：bifibrantObjects_le_cofibrantObject : bifibrantObjects C <= cofibrantObjec
ts C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma bifibrantObjects_le_cofibrantObject :
    bifibrantObjects C ≤ cofibrantObjects C :=
  fun _ h ↦ h.1

variable (C) in
/-
**HomotopicalAlgebra.bifibrantObjects_le_fibrantObject** 是 Mathlib 中的一个引理，位于命名空间
 `HomotopicalAlgebra`。
形式化陈述：bifibrantObjects_le_fibrantObject : bifibrantObjects C <= fibrantObjects C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma bifibrantObjects_le_fibrantObject :
    bifibrantObjects C ≤ fibrantObjects C :=
  fun _ h ↦ h.2

variable (C) in
/-- The full subcategory of bifibrant objects. -/
/-
**HomotopicalAlgebra.BifibrantObject** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAlg
ebra`。
形式化陈述：BifibrantObject : Type u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of bifibrant objects.
-/
abbrev BifibrantObject : Type u := (bifibrantObjects C).FullSubcategory

namespace BifibrantObject

/-- Constructor for `BifibrantObject C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopical
Algebra.BifibrantObject`。
形式化陈述：mk (X : C) [IsCofibrant X] [IsFibrant X] : BifibrantObject C
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `BifibrantObject C`.
-/
abbrev mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩
/-
**HomotopicalAlgebra.BifibrantObject.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Ho
motopicalAlgebra.BifibrantObject`。
形式化陈述：mk_surjective (X : BifibrantObject C) : exists (Y : C) (_ : IsCofibrant Y)
 (_ : IsFibrant Y), X = mk Y
参数：X : BifibrantObject C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mk_surjective (X : BifibrantObject C) :
    ∃ (Y : C) (_ : IsCofibrant Y) (_ : IsFibrant Y), X = mk Y :=
  ⟨X.obj, X.property.1, X.property.2, rfl⟩

/-- Constructor for morphisms in `BifibrantObject C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.homMk** 是 Mathlib 中的一个缩写定义，位于命名空间 `Homotopi
calAlgebra.BifibrantObject`。
形式化陈述：homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [IsFibrant Y
] (f : X ⟶ Y) : mk X ⟶ mk Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `BifibrantObject C`.
-/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f
/-
**HomotopicalAlgebra.BifibrantObject.homMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`HomotopicalAlgebra.BifibrantObject`。
形式化陈述：homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y] [IsFibrant X] [
IsFibrant Y] (f : mk X ⟶ mk Y) : exists (g : X ⟶ Y), f = homMk g
参数：f : mk X ⟶ mk Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    ∃ (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.weakEquivalence_homMk_iff** 是 Mathlib 中的一个引
理，位于命名空间 `HomotopicalAlgebra.BifibrantObject`。
形式化陈述：weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C} [IsCo
fibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) : WeakEquival
ence (homMk f) ↔ WeakEquivalence f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
/-
**HomotopicalAlgebra.BifibrantObject.homMk_id** 是 Mathlib 中的一个引理，位于命名空间 `Homotop
icalAlgebra.BifibrantObject`。
形式化陈述：homMk_id (X : C) [IsCofibrant X] [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X)
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_id (X : C) [IsCofibrant X] [IsFibrant X] :
    homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
/-
**HomotopicalAlgebra.BifibrantObject.homMk_homMk** 是 Mathlib 中的一个引理，位于命名空间 `Homo
topicalAlgebra.BifibrantObject`。
形式化陈述：homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z] [I
sFibrant X] [IsFibrant Y] [IsFibrant Z] (f : X ⟶ Y) (g : Y ⟶ Z) : homMk f ≫ homM
k g = homMk (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/-- The inclusion functor `BifibrantObject C ⥤ C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAl
gebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `BifibrantObject C ⥤ C`.
-/
abbrev ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) : IsCofibrant X.obj := X.property.1
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) : IsFibrant X.obj := X.property.2
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.property.1
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.property.2

/-- The inclusion `BifibrantObject C ⥤ CofibrantObject C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAl
gebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion `BifibrantObject C ⥤ CofibrantObject C`.
-/
abbrev ιCofibrantObject : BifibrantObject C ⥤ CofibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

/-- The inclusion functor `BifibrantObject C ⥤ FibrantObject C`. -/
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopicalAl
gebra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `BifibrantObject C ⥤ FibrantObject C`.
-/
abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) : IsCofibrant (ιFibrantObject.obj X).obj := X.property.1
/-
**HomotopicalAlgebra.BifibrantObject.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopicalAlge
bra.BifibrantObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : BifibrantObject C) : IsFibrant (ιCofibrantObject.obj X).obj := X.property.2

end BifibrantObject

end Bifibrant

end HomotopicalAlgebra

