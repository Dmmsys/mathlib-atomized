/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# The center of a category

Given a category `C`, we introduce an abbreviation `CatCenter C` for
the center of the category `C`, which is `End (𝟭 C)`, the
type of endomorphisms of the identity functor of `C`.

## References
* https://ncatlab.org/nlab/show/center+of+a+category

-/

public section
universe v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/-- The center of a category `C` is the type `End (𝟭 C)` of the endomorphisms
of the identify functor of `C`. -/
/-
**CategoryTheory.CatCenter** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：CatCenter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a category `C` is the type `End (𝟭 C)` of the endomorphisms
of the identify functor of `C`.
-/
abbrev CatCenter := End (𝟭 C)

namespace CatCenter

variable {C}

/-- The action of the center of a category on an object. (This is necessary as
`NatTrans.app x X` is syntactically an endomorphism of `(𝟭 C).obj X`
rather than of `X`.) -/
/-
**CategoryTheory.CatCenter.app** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.CatCe
nter`。
形式化陈述：app (x : CatCenter C) (X : C) : X ⟶ X
参数：x : CatCenter C；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the center of a category on an object. (This is necessary as
`NatTrans.app x X` is syntactically an endomorphism of `(𝟭 C).obj X`
rather than of `X`.)
-/
abbrev app (x : CatCenter C) (X : C) : X ⟶ X := NatTrans.app x X

@[ext]
/-
**CategoryTheory.CatCenter.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CatCent
er`。
形式化陈述：ext (x y : CatCenter C) (h : forall (X : C), x.app X = y.app X) : x = y
参数：x y : CatCenter C；h : forall (X : C), x.app X = y.app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext (x y : CatCenter C) (h : ∀ (X : C), x.app X = y.app X) : x = y :=
  NatTrans.ext (funext h)

@[reassoc]
/-
**CategoryTheory.CatCenter.naturality** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
CatCenter`。
形式化陈述：naturality (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : f ≫ z.app Y = z.app X
 ≫ f
参数：z : CatCenter C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma naturality (z : CatCenter C) {X Y : C} (f : X ⟶ Y) :
    f ≫ z.app Y = z.app X ≫ f := NatTrans.naturality z f

@[reassoc]
/-
**CategoryTheory.CatCenter.mul_app'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ca
tCenter`。
形式化陈述：mul_app' (x y : CatCenter C) (X : C) : (x * y).app X = y.app X ≫ x.app X
参数：x y : CatCenter C；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_app' (x y : CatCenter C) (X : C) : (x * y).app X = y.app X ≫ x.app X := rfl

@[reassoc]
/-
**CategoryTheory.CatCenter.mul_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat
Center`。
形式化陈述：mul_app (x y : CatCenter C) (X : C) : (x * y).app X = x.app X ≫ y.app X
参数：x y : CatCenter C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.CatCenter.mul_app'`：mul_app' (x y : CatCenter C) (X : C) 
: (x * y).app X = y.app X ≫ x.app X
· 使用引理 `CategoryTheory.CatCenter.naturality`：naturality (z : CatCenter C) {X Y :
 C} (f : X ⟶ Y) : f ≫ z.app Y = z.app X ≫ f
-/
lemma mul_app (x y : CatCenter C) (X : C) : (x * y).app X = x.app X ≫ y.app X := by
  rw [mul_app']
  exact x.naturality (y.app X)
/-
**CategoryTheory.CatCenter.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatCenter`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMulCommutative (CatCenter C) where
  is_comm.comm x y := by
    ext X
    rw [mul_app' x y, mul_app y x]
/-
**CategoryTheory.CatCenter.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatCenter`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} : SMul (CatCenter C) (X ⟶ Y) where
  smul z f := f ≫ z.app Y
/-
**CategoryTheory.CatCenter.smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Cat
Center`。
形式化陈述：smul_eq (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = f ≫ z.app Y
参数：z : CatCenter C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_eq (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = f ≫ z.app Y := rfl
/-
**CategoryTheory.CatCenter.smul_eq'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ca
tCenter`。
形式化陈述：smul_eq' (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = z.app X ≫ f
参数：z : CatCenter C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.naturality`：naturality (z : CatCenter C) {X Y :
 C} (f : X ⟶ Y) : f ≫ z.app Y = z.app X ≫ f
-/
lemma smul_eq' (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = z.app X ≫ f :=
  z.naturality f
/-
**CategoryTheory.CatCenter.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatCenter`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} : SMul (CatCenter C)ˣ (X ≅ Y) where
  smul z e :=
    { hom := z.1 • e.hom
      inv := (z⁻¹).1 • e.inv
      hom_inv_id := by
        rw [smul_eq, smul_eq', Category.assoc, ← mul_app_assoc]
        simp
      inv_hom_id := by
        rw [smul_eq, smul_eq', Category.assoc, ← mul_app_assoc]
        simp }

@[reassoc]
/-
**CategoryTheory.CatCenter.smul_iso_hom_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.CatCenter`。
形式化陈述：smul_iso_hom_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) : (z • f).hom =
 f.hom ≫ z.1.app Y
参数：z : (CatCenter C)ˣ；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_iso_hom_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).hom = f.hom ≫ z.1.app Y := rfl

@[reassoc]
/-
**CategoryTheory.CatCenter.smul_iso_hom_eq'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：smul_iso_hom_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) : (z • f).hom 
= z.1.app X ≫ f.hom
参数：z : (CatCenter C)ˣ；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.naturality`：naturality (z : CatCenter C) {X Y :
 C} (f : X ⟶ Y) : f ≫ z.app Y = z.app X ≫ f
-/
lemma smul_iso_hom_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).hom = z.1.app X ≫ f.hom :=
  z.1.naturality f.hom

@[reassoc]
/-
**CategoryTheory.CatCenter.smul_iso_inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.CatCenter`。
形式化陈述：smul_iso_inv_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) : (z • f).inv =
 f.inv ≫ (z⁻¹.1).app X
参数：z : (CatCenter C)ˣ；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_iso_inv_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).inv = f.inv ≫ (z⁻¹.1).app X := rfl

@[reassoc]
/-
**CategoryTheory.CatCenter.smul_iso_inv_eq'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：smul_iso_inv_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) : (z • f).inv 
= (z⁻¹.1).app Y ≫ f.inv
参数：z : (CatCenter C)ˣ；f : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CatCenter.naturality`：naturality (z : CatCenter C) {X Y :
 C} (f : X ⟶ Y) : f ≫ z.app Y = z.app X ≫ f
-/
lemma smul_iso_inv_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).inv = (z⁻¹.1).app Y ≫ f.inv :=
  z.2.naturality f.inv

end CatCenter

end CategoryTheory

