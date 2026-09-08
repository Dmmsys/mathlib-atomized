/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe w v v' u u'

open CategoryTheory

open CategoryTheory.Category

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
/-
**CategoryTheory.Limits.HasZeroMorphisms** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：HasZeroMorphisms where /-- Every morphism space has zero -/ [zero : forall
 X Y : C, Zero (X ⟶ Y)] /-- `f` composed with `0` is `0` -/ comp_zero : forall {
X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category "has zero morphisms" if there is a designated "zero morphism" in each
 morphism space,
and compositions of zero morphisms with anything give the zero morphism.
-/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : ∀ X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by cat_disch
  /-- `0` composed with `f` is `0` -/
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by cat_disch

attribute [instance_reducible, instance] HasZeroMorphisms.zero

variable {C}

@[simp]
/-
**CategoryTheory.Limits.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y 
⟶ Z) = (0 : X ⟶ Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
-/
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z

@[simp]
/-
**CategoryTheory.Limits.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y)
 ≫ f = (0 : X ⟶ Z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.zero_comp`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] (X : C)   {Y Z : C} (f : Y ⟶ Z), …
-/
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f
/-
**CategoryTheory.Limits.hasZeroMorphismsPEmpty** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasZeroMorphismsPEmpty : HasZeroMorphisms (Discrete PEmpty) where zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
-/
instance hasZeroMorphismsPEmpty : HasZeroMorphisms (Discrete PEmpty) where
  zero := by cat_disch
/-
**CategoryTheory.Limits.hasZeroMorphismsPUnit** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasZeroMorphismsPUnit : HasZeroMorphisms (Discrete PUnit) where zero X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasZeroMorphismsPUnit : HasZeroMorphisms (Discrete PUnit) where
  zero X Y := by repeat (constructor)

namespace HasZeroMorphisms

/-- This lemma will be immediately superseded by `ext`, below. -/
/-
**CategoryTheory.Limits.HasZeroMorphisms.ext_aux** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.HasZeroMorphisms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma will be immediately superseded by `ext`, below.
-/
private theorem ext_aux (I J : HasZeroMorphisms C)
    (w : ∀ X Y : C, (I.zero X Y).zero = (J.zero X Y).zero) : I = J := by
  have : I.zero = J.zero := by
    funext X Y
    specialize w X Y
    apply congrArg Zero.mk w
  cases I; cases J
  congr
  · apply proof_irrel_heq
  · apply proof_irrel_heq

/-- If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `HasZeroMorphisms` to exist at all.

See, particularly, the note on `zeroMorphismsOfZeroObject` below.
-/
/-
**CategoryTheory.Limits.HasZeroMorphisms.ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.HasZeroMorphisms`。
形式化陈述：ext (I J : HasZeroMorphisms C) : I = J
参数：I J : HasZeroMorphisms C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms.0.CategoryTh
eory.Limits.HasZeroMorphisms.ext_aux`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] (I J : CategoryTheory.Limits.HasZeroMorphisms C),   (∀ (X Y : C),
 Zero.zero = Zero.…
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.zero_comp`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] (X : C)   {Y Z : C} (f : Y ⟶ Z), …
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `HasZeroMorphisms` to exist at all.

See, particularly, the note on `zeroMorphismsOfZeroObject` below.
-/
theorem ext (I J : HasZeroMorphisms C) : I = J := by
  apply ext_aux
  intro X Y
  have : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (I.zero X Y).zero := by
    apply I.zero_comp X (J.zero Y Y).zero
  have that : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (J.zero X Y).zero := by
    apply J.comp_zero (I.zero X Y).zero Y
  rw [← this, ← that]
/-
**CategoryTheory.Limits.HasZeroMorphisms.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits.HasZeroMorphisms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (HasZeroMorphisms C) :=
  ⟨ext⟩

end HasZeroMorphisms

open Opposite HasZeroMorphisms

/-
**CategoryTheory.Limits.hasZeroMorphismsOpposite** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasZeroMorphismsOpposite [HasZeroMorphisms C] : HasZeroMorphisms Cᵒᵖ where
 zero X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasZeroMorphismsOpposite [HasZeroMorphisms C] : HasZeroMorphisms Cᵒᵖ where
  zero X Y := ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X {Y Z} (f : Y ⟶ Z) :=
    congrArg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))

section

variable [HasZeroMorphisms C]

/-
**CategoryTheory.Limits.op_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C),   Quiver.Hom.op 0 = 0
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 := rfl
/-
**CategoryTheory.Limits.unop_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C]   (X Y : Cᵒᵖ), Quiver.Hom.unop 0 = 0
参数：X Y : Cᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma unop_zero (X Y : Cᵒᵖ) : (0 : X ⟶ Y).unop = 0 := rfl
/-
**CategoryTheory.Limits.zero_of_comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g 
= 0) : f = 0
参数：g : Y ⟶ Z；h : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
-/
theorem zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0 := by
  rw [← zero_comp, cancel_mono] at h
  exact h
/-
**CategoryTheory.Limits.zero_of_epi_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 
0) : g = 0
参数：f : X ⟶ Y；h : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0 := by
  rw [← comp_zero, cancel_epi] at h
  exact h
/-
**CategoryTheory.Limits.comp_eq_zero_iff_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：comp_eq_zero_iff_of_epi {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] : f ≫ 
g = 0 ↔ g = 0
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_epi_comp`：zero_of_epi_comp {X Y Z : C} (f 
: X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma comp_eq_zero_iff_of_epi {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] :
    f ≫ g = 0 ↔ g = 0 :=
  ⟨zero_of_epi_comp _, by simp +contextual⟩
/-
**CategoryTheory.Limits.eq_zero_of_image_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f
 = 0) : f = 0
参数：w : image.ι f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …
-/
theorem eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) :
    f = 0 := by rw [← image.fac f, w, HasZeroMorphisms.comp_zero]
/-
**CategoryTheory.Limits.nonzero_image_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f != 0) :
 image.ι f != 0
参数：w : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.eq_zero_of_image_eq_zero`：eq_zero_of_image_eq_zero
 {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) : f = 0
-/
theorem nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f ≠ 0) : image.ι f ≠ 0 :=
  fun h => w (eq_zero_of_image_eq_zero h)

end

section

variable [HasZeroMorphisms D]

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroMorphisms (C ⥤ D) where
  zero F G := ⟨{ app := fun _ => 0 }⟩
  comp_zero := fun η H => by
    ext X; dsimp; apply comp_zero
  zero_comp := fun F {G H} η => by
    ext X; dsimp; apply zero_comp

@[simp]
/-
**CategoryTheory.Limits.zero_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
形式化陈述：zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0
参数：F G : C ⥤ D；j : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 := rfl

end

namespace IsZero

variable [HasZeroMorphisms C]

/-
**CategoryTheory.Limits.IsZero.eq_zero_of_src** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsZero`。
形式化陈述：eq_zero_of_src {X Y : C} (o : IsZero X) (f : X ⟶ Y) : f = 0
参数：o : IsZero X；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
-/
theorem eq_zero_of_src {X Y : C} (o : IsZero X) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_src _ _
/-
**CategoryTheory.Limits.IsZero.eq_zero_of_tgt** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsZero`。
形式化陈述：eq_zero_of_tgt {X Y : C} (o : IsZero Y) (f : X ⟶ Y) : f = 0
参数：o : IsZero Y；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_tgt`：eq_of_tgt (hX : IsZero X) (f g :
 Y ⟶ X) : f = g
-/
theorem eq_zero_of_tgt {X Y : C} (o : IsZero Y) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_tgt _ _
/-
**CategoryTheory.Limits.IsZero.iff_id_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsZero`。
形式化陈述：iff_id_eq_zero (X : C) : IsZero X ↔ 𝟙 X = 0
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem iff_id_eq_zero (X : C) : IsZero X ↔ 𝟙 X = 0 :=
  ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← id_comp f, ← id_comp (0 : X ⟶ Y), h, zero_comp, zero_comp]; simp only⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← comp_id f, ← comp_id (0 : Y ⟶ X), h, comp_zero, comp_zero]; simp only ⟩⟩⟩⟩
/-
**CategoryTheory.Limits.IsZero.of_mono_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.IsZero`。
形式化陈述：of_mono_zero (X Y : C) [Mono (0 : X ⟶ Y)] : IsZero X
参数：X Y : C；0 : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_mono_zero (X Y : C) [Mono (0 : X ⟶ Y)] : IsZero X :=
  (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))
/-
**CategoryTheory.Limits.IsZero.of_epi_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.IsZero`。
形式化陈述：of_epi_zero (X Y : C) [Epi (0 : X ⟶ Y)] : IsZero Y
参数：X Y : C；0 : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_epi_zero (X Y : C) [Epi (0 : X ⟶ Y)] : IsZero Y :=
  (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))
/-
**CategoryTheory.Limits.IsZero.of_mono_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.IsZero`。
形式化陈述：of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0) : IsZero X
参数：f : X ⟶ Y；h : f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_mono_zero`：of_mono_zero (X Y : C) [Mono 
(0 : X ⟶ Y)] : IsZero X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0) : IsZero X := by
  subst h
  apply of_mono_zero X Y
/-
**CategoryTheory.Limits.IsZero.of_epi_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.IsZero`。
形式化陈述：of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y
参数：f : X ⟶ Y；h : f = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_epi_zero`：of_epi_zero (X Y : C) [Epi (0 
: X ⟶ Y)] : IsZero Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y := by
  subst h
  apply of_epi_zero X Y
/-
**CategoryTheory.Limits.IsZero.iff_isSplitMono_eq_zero** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.IsZero`。
形式化陈述：iff_isSplitMono_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔
 f = 0
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.IsSplitMono.id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f],   
CategoryTheory.Cate…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.retraction.congr_simp`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X Y : C} (f f_1 : Y ⟶ X) (e_f : f = f_1)   [hf : Cate
goryTheory.IsSplitMono f],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iff_isSplitMono_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.id_comp f, h, zero_comp]
  · intro h
    rw [← IsSplitMono.id f]
    simp only [h, zero_comp]
/-
**CategoryTheory.Limits.IsZero.iff_isSplitEpi_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Limits.IsZero`。
形式化陈述：iff_isSplitEpi_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f
 = 0
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.section_.congr_simp`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [hf : Catego
ryTheory.IsSplitEpi f], …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iff_isSplitEpi_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.comp_id f, h, comp_zero]
  · intro h
    rw [← IsSplitEpi.id f]
    simp [h]
/-
**CategoryTheory.Limits.IsZero.of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.IsZero`。
形式化陈述：of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y) : IsZero X
参数：f : X ⟶ Y；i : IsZero Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_mono_zero`：of_mono_zero (X Y : C) [Mono 
(0 : X ⟶ Y)] : IsZero X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_tgt`：eq_zero_of_tgt {X Y : C} (o
 : IsZero Y) (f : X ⟶ Y) : f = 0
-/
theorem of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y) : IsZero X := by
  obtain rfl := i.eq_zero_of_tgt f
  exact IsZero.of_mono_zero X Y
/-
**CategoryTheory.Limits.IsZero.of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.IsZero`。
形式化陈述：of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X) : IsZero Y
参数：f : X ⟶ Y；i : IsZero X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_epi_zero`：of_epi_zero (X Y : C) [Epi (0 
: X ⟶ Y)] : IsZero Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsZero.eq_zero_of_src`：eq_zero_of_src {X Y : C} (o
 : IsZero X) (f : X ⟶ Y) : f = 0
-/
theorem of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X) : IsZero Y := by
  obtain rfl := i.eq_zero_of_src f
  exact IsZero.of_epi_zero X Y

end IsZero

/-- A category with a zero object has zero morphisms.

It is rarely a good idea to use this. Many categories that have a zero object have zero
morphisms for some other reason, for example from additivity. Library code that uses
`zeroMorphismsOfZeroObject` will then be incompatible with these categories because
the `HasZeroMorphisms` instances will not be definitionally equal. For this reason library
code should generally ask for an instance of `HasZeroMorphisms` separately, even if it already
asks for an instance of `HasZeroObject`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.IsZero.hasZeroMorphisms** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.IsZero`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {O : C} →
 CategoryTheory.Limits.IsZero O → CategoryTheory.Limits.HasZeroMorphisms C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with a zero object has zero morphisms.

It is rarely a good idea to use this. Many categories that have a zero object ha
ve zero
morphisms for some other reason, for example from additivity. Library code that 
uses
`zeroMorphismsOfZeroObject` will then be incompatible with these categories beca
use
the `HasZeroMorphisms` instances will not be definitionally equal. For this reas
on library
code should generally ask for an instance of `HasZeroMorphisms` separately, even
 if it already
asks for an instance of `HasZeroObject`.
-/
def IsZero.hasZeroMorphisms {O : C} (hO : IsZero O) : HasZeroMorphisms C where
  zero X Y := { zero := hO.from_ X ≫ hO.to_ Y }
  zero_comp X {Y Z} f := by
    change (hO.from_ X ≫ hO.to_ Y) ≫ f = hO.from_ X ≫ hO.to_ Z
    rw [Category.assoc]
    congr
    apply hO.eq_of_src
  comp_zero {X Y} f Z := by
    change f ≫ (hO.from_ Y ≫ hO.to_ Z) = hO.from_ X ≫ hO.to_ Z
    rw [← Category.assoc]
    congr
    apply hO.eq_of_tgt

namespace HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- A category with a zero object has zero morphisms.

It is rarely a good idea to use this. Many categories that have a zero object have zero
morphisms for some other reason, for example from additivity. Library code that uses
`zeroMorphismsOfZeroObject` will then be incompatible with these categories because
the `HasZeroMorphisms` instances will not be definitionally equal. For this reason library
code should generally ask for an instance of `HasZeroMorphisms` separately, even if it already
asks for an instance of `HasZeroObject`. -/
@[instance_reducible]
/-
**CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroMorphismsOfZeroObject : HasZeroMorphisms C where zero X _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category with a zero object has zero morphisms.

It is rarely a good idea to use this. Many categories that have a zero object ha
ve zero
morphisms for some other reason, for example from additivity. Library code that 
uses
`zeroMorphismsOfZeroObject` will then be incompatible with these categories beca
use
the `HasZeroMorphisms` instances will not be definitionally equal. For this reas
on library
code should generally ask for an instance of `HasZeroMorphisms` separately, even
 if it already
asks for an instance of `HasZeroObject`.
-/
def zeroMorphismsOfZeroObject : HasZeroMorphisms C where
  zero X _ := { zero := (default : X ⟶ 0) ≫ default }
  zero_comp X {Y Z} f := by
    change ((default : X ⟶ 0) ≫ default) ≫ f = (default : X ⟶ 0) ≫ default
    rw [Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]
  comp_zero {X Y} f Z := by
    change f ≫ (default : Y ⟶ 0) ≫ default = (default : X ⟶ 0) ≫ default
    rw [← Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_hom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoIsInitial_hom {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).hom 
= 0
参数：t : IsInitial X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
-/
theorem zeroIsoIsInitial_hom {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).hom = 0 := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_inv** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoIsInitial_inv {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).inv 
= 0
参数：t : IsInitial X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.to_zero_ext`：to_zero_ext {X : C} (f 
g : X ⟶ 0) : f = g
-/
theorem zeroIsoIsInitial_inv {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).inv = 0 := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_hom** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoIsTerminal_hom {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).h
om = 0
参数：t : IsTerminal X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
-/
theorem zeroIsoIsTerminal_hom {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).hom = 0 := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_inv** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoIsTerminal_inv {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).i
nv = 0
参数：t : IsTerminal X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.to_zero_ext`：to_zero_ext {X : C} (f 
g : X ⟶ 0) : f = g
-/
theorem zeroIsoIsTerminal_inv {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).inv = 0 := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_hom** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoInitial_hom [HasInitial C] : zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
-/
theorem zeroIsoInitial_hom [HasInitial C] : zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C) := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoInitial_inv [HasInitial C] : zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.initial.hom_ext`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C] {P : C}
   (f g : ⊥_ C ⟶ P), f = g
-/
theorem zeroIsoInitial_inv [HasInitial C] : zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0) := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoTerminal_hom [HasTerminal C] : zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
-/
theorem zeroIsoTerminal_hom [HasTerminal C] : zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C) := by ext

@[simp]
/-
**CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_inv** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Limits.HasZeroObject`。
形式化陈述：zeroIsoTerminal_inv [HasTerminal C] : zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.to_zero_ext`：to_zero_ext {X : C} (f 
g : X ⟶ 0) : f = g
-/
theorem zeroIsoTerminal_inv [HasTerminal C] : zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0) := by ext

end HasZeroMorphisms

open ZeroObject

/-
**CategoryTheory.Limits.HasZeroObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits.HasZeroObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : Type*} [Category* B] : HasZeroObject (B ⥤ C) :=
  (((CategoryTheory.Functor.const B).obj (0 : C)).isZero fun _ => isZero_zero _).hasZeroObject

end HasZeroObject

open ZeroObject

variable {D}

@[simp]
/-
**CategoryTheory.Limits.IsZero.map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.IsZero`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   [CategoryTheory.Limits.HasZeroObjec
t D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   {F : CategoryTheory.F
unctor C D}, CategoryTheory.Limits.IsZero F → ∀ {X Y : C} (f : X ⟶ Y), F.map f =
 0
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.obj`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {D : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} D]  
 [CategoryTheory.Limit…
-/
theorem IsZero.map [HasZeroObject D] [HasZeroMorphisms D] {F : C ⥤ D} (hF : IsZero F) {X Y : C}
    (f : X ⟶ Y) : F.map f = 0 :=
  (hF.obj _).eq_of_src _ _

@[simp]
/-
**CategoryTheory.Limits._root_.CategoryTheory.Functor.zero_obj** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CategoryTheory.Functor.zero_obj [HasZeroObject D] (X : C) :
    IsZero ((0 : C ⥤ D).obj X) :=
  (isZero_zero _).obj _

@[simp]
/-
**CategoryTheory.Limits._root_.CategoryTheory.zero_map** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CategoryTheory.zero_map [HasZeroObject D] [HasZeroMorphisms D] {X Y : C}
    (f : X ⟶ Y) : (0 : C ⥤ D).map f = 0 :=
  (isZero_zero _).map _

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

@[simp]
/-
**CategoryTheory.Limits.id_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
-/
theorem id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0) := by apply HasZeroObject.from_zero_ext

-- This can't be a `simp` lemma because the left-hand side would be a metavariable.
/-- An arrow ending in the zero object is zero -/
/-
**CategoryTheory.Limits.zero_of_to_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0
参数：f : X ⟶ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.to_zero_ext`：to_zero_ext {X : C} (f 
g : X ⟶ 0) : f = g

--- 原说明 ---
An arrow ending in the zero object is zero
-/
theorem zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 := by ext
/-
**CategoryTheory.Limits.zero_of_target_iso_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0
参数：f : X ⟶ Y；i : Y ≅ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.id_zero`：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 := by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [Iso.hom_inv_id, id_comp, comp_id]
  simpa using h

/-- An arrow starting at the zero object is zero -/
/-
**CategoryTheory.Limits.zero_of_from_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0
参数：f : 0 ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g

--- 原说明 ---
An arrow starting at the zero object is zero
-/
theorem zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 := by ext
/-
**CategoryTheory.Limits.zero_of_source_iso_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
参数：f : X ⟶ Y；i : X ≅ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.id_zero`：id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0)
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
-/
theorem zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 := by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [Iso.hom_inv_id_assoc, id_comp]
  simpa using h
/-
**CategoryTheory.Limits.zero_of_source_iso_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0) : f 
= 0
参数：f : X ⟶ Y；i : IsIsomorphic X 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_source_iso_zero`：zero_of_source_iso_zero {
X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
-/
theorem zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0) : f = 0 :=
  zero_of_source_iso_zero f (Nonempty.some i)
/-
**CategoryTheory.Limits.zero_of_target_iso_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0) : f 
= 0
参数：f : X ⟶ Y；i : IsIsomorphic Y 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_target_iso_zero`：zero_of_target_iso_zero {
X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0
-/
theorem zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0) : f = 0 :=
  zero_of_target_iso_zero f (Nonempty.some i)
/-
**CategoryTheory.Limits.mono_of_source_iso_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : Mono f
参数：f : X ⟶ Y；i : X ≅ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_of_target_iso_zero`：zero_of_target_iso_zero {
X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0
-/
theorem mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : Mono f :=
  ⟨fun {Z} g h _ => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩
/-
**CategoryTheory.Limits.epi_of_target_iso_zero** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f
参数：f : X ⟶ Y；i : Y ≅ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_of_source_iso_zero`：zero_of_source_iso_zero {
X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
-/
theorem epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f :=
  ⟨fun {Z} g h _ => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

/-- An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
/-
**CategoryTheory.Limits.idZeroEquivIsoZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：idZeroEquivIsoZero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0) where toFun h
参数：X : C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as a
n `≃`.
-/
def idZeroEquivIsoZero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0) where
  toFun h :=
    { hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by cat_disch
  right_inv := by cat_disch

@[simp]
/-
**CategoryTheory.Limits.idZeroEquivIsoZero_apply_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：idZeroEquivIsoZero_apply_hom (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero 
X) h).hom = 0
参数：X : C；h : 𝟙 X = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idZeroEquivIsoZero_apply_hom (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).hom = 0 :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.idZeroEquivIsoZero_apply_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：idZeroEquivIsoZero_apply_inv (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero 
X) h).inv = 0
参数：X : C；h : 𝟙 X = 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idZeroEquivIsoZero_apply_inv (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).inv = 0 :=
  rfl

/-- If `0 : X ⟶ Y` is a monomorphism, then `X ≅ 0`. -/
@[simps]
/-
**CategoryTheory.Limits.isoZeroOfMonoZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：isoZeroOfMonoZero {X Y : C} (_ : Mono (0 : X ⟶ Y)) : X ≅ 0 where hom
参数：_ : Mono (0 : X ⟶ Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `0 : X ⟶ Y` is a monomorphism, then `X ≅ 0`.
-/
def isoZeroOfMonoZero {X Y : C} (_ : Mono (0 : X ⟶ Y)) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_mono (0 : X ⟶ Y)).mp (by simp)

/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
/-
**CategoryTheory.Limits.isoZeroOfEpiZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：isoZeroOfEpiZero {X Y : C} (_ : Epi (0 : X ⟶ Y)) : Y ≅ 0 where hom
参数：_ : Epi (0 : X ⟶ Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`.
-/
def isoZeroOfEpiZero {X Y : C} (_ : Epi (0 : X ⟶ Y)) : Y ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_epi (0 : X ⟶ Y)).mp (by simp)

/-- If a monomorphism out of `X` is zero, then `X ≅ 0`. -/
/-
**CategoryTheory.Limits.isoZeroOfMonoEqZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isoZeroOfMonoEqZero {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0) : X ≅ 0
参数：h : f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a monomorphism out of `X` is zero, then `X ≅ 0`.
-/
def isoZeroOfMonoEqZero {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0) : X ≅ 0 := by
  subst h
  apply isoZeroOfMonoZero (Y := Y) ‹_›

/-- If an epimorphism in to `Y` is zero, then `Y ≅ 0`. -/
/-
**CategoryTheory.Limits.isoZeroOfEpiEqZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isoZeroOfEpiEqZero {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0) : Y ≅ 0
参数：h : f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an epimorphism in to `Y` is zero, then `Y ≅ 0`.
-/
def isoZeroOfEpiEqZero {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0) : Y ≅ 0 := by
  subst h
  apply isoZeroOfEpiZero (X := X) ‹_›

/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
/-
**CategoryTheory.Limits.isoOfIsIsomorphicZero** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isoOfIsIsomorphicZero {X : C} (P : IsIsomorphic X 0) : X ≅ 0 where hom
参数：P : IsIsomorphic X 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices.
-/
def isoOfIsIsomorphicZero {X : C} (P : IsIsomorphic X 0) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by
    have P := P.some
    rw [← P.hom_inv_id, ← Category.id_comp P.inv]
    apply Eq.symm
    simp only [id_comp, Iso.hom_inv_id, comp_zero]
    apply (idZeroEquivIsoZero X).invFun P
  inv_hom_id := by simp

end

section IsIso

variable [HasZeroMorphisms C]

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
/-
**CategoryTheory.Limits.isIsoZeroEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：isIsoZeroEquiv (X Y : C) : IsIso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0 where toF
un
参数：X Y : C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
def isIsoZeroEquiv (X Y : C) : IsIso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0 where
  toFun := by
    intro i
    rw [← IsIso.hom_inv_id (0 : X ⟶ Y)]
    rw [← IsIso.inv_hom_id (0 : X ⟶ Y)]
    simp only [comp_zero, and_self, zero_comp]
  invFun h := ⟨⟨(0 : Y ⟶ X), by cat_disch⟩⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
/-
**CategoryTheory.Limits.isIsoZeroSelfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：isIsoZeroSelfEquiv (X : C) : IsIso (0 : X ⟶ X) ≃ 𝟙 X = 0
参数：X : C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def isIsoZeroSelfEquiv (X : C) : IsIso (0 : X ⟶ X) ≃ 𝟙 X = 0 := by simpa using isIsoZeroEquiv X X

variable [HasZeroObject C]

open ZeroObject

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
/-
**CategoryTheory.Limits.isIsoZeroEquivIsoZero** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：isIsoZeroEquivIsoZero (X Y : C) : IsIso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0)
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
def isIsoZeroEquivIsoZero (X Y : C) : IsIso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0) := by
  -- This is lame, because `Prod` can't cope with `Prop`, so we can't use `Equiv.prodCongr`.
  refine (isIsoZeroEquiv X Y).trans ?_
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X).symm eX
    · exact (idZeroEquivIsoZero Y).symm eY
  · rintro ⟨hX, hY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X) hX
    · exact (idZeroEquivIsoZero Y) hY
  · cat_disch
  · cat_disch

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are zero objects.
-/
/-
**CategoryTheory.Limits.isIsoZero_iff_source_target_isZero** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：isIsoZero_iff_source_target_isZero (X Y : C) : IsIso (0 : X ⟶ Y) ↔ IsZero 
X ∧ IsZero Y
参数：X Y : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are zero objects.
-/
lemma isIsoZero_iff_source_target_isZero (X Y : C) : IsIso (0 : X ⟶ Y) ↔ IsZero X ∧ IsZero Y := by
  constructor
  · intro h
    let h' := isIsoZeroEquivIsoZero _ _ h
    exact ⟨(isZero_zero _).of_iso h'.1, (isZero_zero _).of_iso h'.2⟩
  · intro ⟨hX, hY⟩
    exact (isIsoZeroEquivIsoZero _ _).symm ⟨hX.isoZero, hY.isoZero⟩
/-
**CategoryTheory.Limits.isIso_of_source_target_iso_zero** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：isIso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅
 0) : IsIso f
参数：f : X ⟶ Y；i : X ≅ 0；j : Y ≅ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.zero_of_source_iso_zero`：zero_of_source_iso_zero {
X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0
-/
theorem isIso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) :
    IsIso f := by
  rw [zero_of_source_iso_zero f i]
  exact (isIsoZeroEquivIsoZero _ _).invFun ⟨i, j⟩

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
/-
**CategoryTheory.Limits.isIsoZeroSelfEquivIsoZero** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：isIsoZeroSelfEquivIsoZero (X : C) : IsIso (0 : X ⟶ X) ≃ (X ≅ 0)
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Limits.HasZeroObject.instSubsingletonIsoOfNat`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.H
asZeroObject C] (X : C),   Subsingleton (X ≅ 0)

--- 原说明 ---
A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def isIsoZeroSelfEquivIsoZero (X : C) : IsIso (0 : X ⟶ X) ≃ (X ≅ 0) :=
  (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv

end IsIso

/-- If there are zero morphisms, any initial object is a zero object. -/
/-
**CategoryTheory.Limits.hasZeroObject_of_hasInitial_object** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：hasZeroObject_of_hasInitial_object [HasZeroMorphisms C] [HasInitial C] : H
asZeroObject C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Limits.HasZeroMorphisms.comp_zero`：∀ {C : Type u} {inst :
 CategoryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasZeroMorphism
s C] {X Y : C}   (f : X ⟶ Y) (Z : C), …

--- 原说明 ---
If there are zero morphisms, any initial object is a zero object.
-/
theorem hasZeroObject_of_hasInitial_object [HasZeroMorphisms C] [HasInitial C] :
    HasZeroObject C := by
  refine ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ 0 := by congr!; subsingleton
    _ = 0 := HasZeroMorphisms.comp_zero _ _

/-- If there are zero morphisms, any terminal object is a zero object. -/
/-
**CategoryTheory.Limits.hasZeroObject_of_hasTerminal_object** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasZeroObject_of_hasTerminal_object [HasZeroMorphisms C] [HasTerminal C] :
 HasZeroObject C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)

--- 原说明 ---
If there are zero morphisms, any terminal object is a zero object.
-/
theorem hasZeroObject_of_hasTerminal_object [HasZeroMorphisms C] [HasTerminal C] :
    HasZeroObject C := by
  refine ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = 0 ≫ f := by congr!; subsingleton
    _ = 0 := zero_comp

section Image

variable [HasZeroMorphisms C]

/-
**CategoryTheory.Limits.image_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
    [Epi (factorThruImage f)] (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
  zero_of_epi_comp (factorThruImage f) <| by simp [h]
/-
**CategoryTheory.Limits.comp_factorThruImage_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：comp_factorThruImage_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage
 g] (h : f ≫ g = 0) : f ≫ factorThruImage g = 0
参数：h : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.zero_of_comp_mono`：zero_of_comp_mono {X Y Z : C} {
f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0
· 使用定理 `CategoryTheory.Limits.instMonoι`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f], CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.image.fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : CategoryTheory.Limits.HasIma
ge f],   CategoryTheo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_factorThruImage_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
    (h : f ≫ g = 0) : f ≫ factorThruImage g = 0 :=
  zero_of_comp_mono (image.ι g) <| by simp [h]

variable [HasZeroObject C]

open ZeroObject

/-- The zero morphism has a `MonoFactorisation` through the zero object.
-/
@[simps]
/-
**CategoryTheory.Limits.monoFactorisationZero** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：monoFactorisationZero (X Y : C) : MonoFactorisation (0 : X ⟶ Y) where I
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero morphism has a `MonoFactorisation` through the zero object.
-/
def monoFactorisationZero (X Y : C) : MonoFactorisation (0 : X ⟶ Y) where
  I := 0
  m := 0
  e := 0

/-- The factorisation through the zero object is an image factorisation.
-/
/-
**CategoryTheory.Limits.imageFactorisationZero** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：imageFactorisationZero (X Y : C) : ImageFactorisation (0 : X ⟶ Y) where F
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The factorisation through the zero object is an image factorisation.
-/
def imageFactorisationZero (X Y : C) : ImageFactorisation (0 : X ⟶ Y) where
  F := monoFactorisationZero X Y
  isImage := { lift := fun _ => 0 }
/-
**CategoryTheory.Limits.hasImage_zero** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：hasImage_zero {X Y : C} : HasImage (0 : X ⟶ Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImage.mk`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {X Y : C} {f : X ⟶ Y}   (F : CategoryTheory.Limits.ImageFact
orisation f), CategoryT…
-/
instance hasImage_zero {X Y : C} : HasImage (0 : X ⟶ Y) :=
  HasImage.mk <| imageFactorisationZero _ _

/-- The image of a zero morphism is the zero object. -/
/-
**CategoryTheory.Limits.imageZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：imageZero {X Y : C} : image (0 : X ⟶ Y) ≅ 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a zero morphism is the zero object.
-/
def imageZero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
  IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).isImage

/-- The image of a morphism which is equal to zero is the zero object. -/
/-
**CategoryTheory.Limits.imageZero'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：imageZero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] : image f ≅ 0
参数：h : f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a morphism which is equal to zero is the zero object.
-/
def imageZero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] : image f ≅ 0 :=
  image.eqToIso h ≪≫ imageZero

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Limits.image.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image.ι_zero {X Y : C} [HasImage (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 := by
  rw [← image.lift_fac (monoFactorisationZero X Y)]
  simp

/-- If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
/-
**CategoryTheory.Limits.image.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
theorem image.ι_zero' [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] :
    image.ι f = 0 := by
  rw [image.eq_fac h]
  simp

end Image

set_option backward.isDefEq.respectTransparency false in
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
/-
**CategoryTheory.Limits.isSplitMono_sigma_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the presence of zero morphisms, coprojections into a coproduct are (split) mo
nomorphisms.
-/
instance isSplitMono_sigma_ι {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasColimit (Discrete.functor f)] (b : β) : IsSplitMono (Sigma.ι f b) := by
  classical exact IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }

set_option backward.isDefEq.respectTransparency false in
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
/-
**CategoryTheory.Limits.isSplitEpi_pi_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the presence of zero morphisms, projections into a product are (split) epimor
phisms.
-/
instance isSplitEpi_pi_π {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasLimit (Discrete.functor f)] (b : β) : IsSplitEpi (Pi.π f b) := by
  classical exact IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }

set_option backward.isDefEq.respectTransparency false in
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
/-
**CategoryTheory.Limits.isSplitMono_coprod_inl** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isSplitMono_coprod_inl [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X 
Y)] : IsSplitMono (coprod.inl : X ⟶ X ⨿ Y)
参数：pair X Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   C
ategoryTheory.IsSpli…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the presence of zero morphisms, coprojections into a coproduct are (split) mo
nomorphisms.
-/
instance isSplitMono_coprod_inl [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inl : X ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }

set_option backward.isDefEq.respectTransparency false in
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
/-
**CategoryTheory.Limits.isSplitMono_coprod_inr** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：isSplitMono_coprod_inr [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X 
Y)] : IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y)
参数：pair X Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   C
ategoryTheory.IsSpli…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the presence of zero morphisms, coprojections into a coproduct are (split) mo
nomorphisms.
-/
instance isSplitMono_coprod_inr [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }

set_option backward.isDefEq.respectTransparency false in
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
/-
**CategoryTheory.Limits.isSplitEpi_prod_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isSplitEpi_prod_fst [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
 IsSplitEpi (prod.fst : X ⨯ Y ⟶ X)
参数：pair X Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the presence of zero morphisms, projections into a product are (split) epimor
phisms.
-/
instance isSplitEpi_prod_fst [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.fst : X ⨯ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }

set_option backward.isDefEq.respectTransparency false in
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
/-
**CategoryTheory.Limits.isSplitEpi_prod_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：isSplitEpi_prod_snd [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
 IsSplitEpi (prod.snd : X ⨯ Y ⟶ Y)
参数：pair X Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (se : CategoryTheory.SplitEpi f),   Cat
egoryTheory.IsSplit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the presence of zero morphisms, projections into a product are (split) epimor
phisms.
-/
instance isSplitEpi_prod_snd [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.snd : X ⨯ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }


section

variable [HasZeroMorphisms C] [HasZeroObject C] {F : D ⥤ C}

/-- If a functor `F` is zero, then any cone for `F` with a zero point is limit. -/
/-
**CategoryTheory.Limits.IsLimit.ofIsZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         [CategoryTh
eory.Limits.HasZeroMorphisms C] →           [CategoryTheory.Limits.HasZeroObject
 C] →             {F : CategoryTheory.Functor D C} →               (c : Category
Theory.Limits.Cone F) →                 CategoryTheory.Limits.IsZero F → Categor
yTheory.Limits.IsZero c.pt → CategoryTheory.Limits.IsLimit c
参数：c : CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor `F` is zero, then any cone for `F` with a zero point is limit.
-/
def IsLimit.ofIsZero (c : Cone F) (hF : IsZero F) (hc : IsZero c.pt) : IsLimit c where
  lift _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_tgt _ _
  uniq _ _ _ := hc.eq_of_tgt _ _

/-- If a functor `F` is zero, then any cocone for `F` with a zero point is colimit. -/
/-
**CategoryTheory.Limits.IsColimit.ofIsZero** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         [CategoryTh
eory.Limits.HasZeroMorphisms C] →           [CategoryTheory.Limits.HasZeroObject
 C] →             {F : CategoryTheory.Functor D C} →               (c : Category
Theory.Limits.Cocone F) →                 CategoryTheory.Limits.IsZero F → Categ
oryTheory.Limits.IsZero c.pt → CategoryTheory.Limits.IsColimit c
参数：c : CategoryTheory.Limits.Cocone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor `F` is zero, then any cocone for `F` with a zero point is colimit.
-/
def IsColimit.ofIsZero (c : Cocone F) (hF : IsZero F) (hc : IsZero c.pt) : IsColimit c where
  desc _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_src _ _
  uniq _ _ _ := hc.eq_of_src _ _
/-
**CategoryTheory.Limits.IsLimit.isZero_pt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   [CategoryTheory.Limits.HasZeroMorph
isms C] [CategoryTheory.Limits.HasZeroObject C] {F : CategoryTheory.Functor D C}
   {c : CategoryTheory.Limits.Cone F} (hc : CategoryTheory.Limits.IsLimit c),   
CategoryTheory.Limits.IsZero F → CategoryTheory.Limits.IsZero c.pt
参数：hc : CategoryTheory.Limits.IsLimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma IsLimit.isZero_pt {c : Cone F} (hc : IsLimit c) (hF : IsZero F) : IsZero c.pt :=
  (isZero_zero C).of_iso (IsLimit.conePointUniqueUpToIso hc
    (IsLimit.ofIsZero (Cone.mk 0 0) hF (isZero_zero C)))
/-
**CategoryTheory.Limits.IsColimit.isZero_pt** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [in
st_1 : CategoryTheory.Category.{v', u'} D]   [CategoryTheory.Limits.HasZeroMorph
isms C] [CategoryTheory.Limits.HasZeroObject C] {F : CategoryTheory.Functor D C}
   {c : CategoryTheory.Limits.Cocone F} (hc : CategoryTheory.Limits.IsColimit c)
,   CategoryTheory.Limits.IsZero F → CategoryTheory.Limits.IsZero c.pt
参数：hc : CategoryTheory.Limits.IsColimit c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
-/
lemma IsColimit.isZero_pt {c : Cocone F} (hc : IsColimit c) (hF : IsZero F) : IsZero c.pt :=
  (isZero_zero C).of_iso (IsColimit.coconePointUniqueUpToIso hc
    (IsColimit.ofIsZero (Cocone.mk 0 0) hF (isZero_zero C)))

/-- Given a functor `F : D ⥤ C`, zero morphisms on `C` induce zero morphisms on
`D` by taking preimages. -/
@[reducible]
/-
**CategoryTheory.Limits._root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorph
isms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : D ⥤ C`, zero morphisms on `C` induce zero morphisms on
`D` by taking preimages.
-/
def _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms (hF : F.FullyFaithful) :
    HasZeroMorphisms D where
  zero X Y := ⟨hF.preimage 0⟩
  comp_zero f _ := by
    apply hF.map_injective
    change F.map (f ≫ (hF.preimage _)) = F.map (hF.preimage _)
    simp
  zero_comp _ _ _ f := by
    apply hF.map_injective
    change F.map ((hF.preimage _) ≫ f) = F.map (hF.preimage _)
    simp

omit [HasZeroObject C] in
/-
**CategoryTheory.Limits._root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorph
isms_def** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.CategoryTheory.Functor.FullyFaithful.hasZeroMorphisms_def (hF : F.FullyFaithful)
    (X Y : D) : letI : HasZeroMorphisms D := hF.hasZeroMorphisms
    (0 : X ⟶ Y) = hF.preimage 0 := rfl

end

section

variable [HasZeroMorphisms C]

/-
**CategoryTheory.Limits.IsTerminal.isZero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasZeroMorphisms C] {X : C}   (hX : CategoryTheory.Limits.IsTerminal X), C
ategoryTheory.Limits.IsZero X
参数：hX : CategoryTheory.Limits.IsTerminal X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
lemma IsTerminal.isZero {X : C} (hX : IsTerminal X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext
/-
**CategoryTheory.Limits.IsInitial.isZero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.IsInitial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasZeroMorphisms C] {X : C}   (hX : CategoryTheory.Limits.IsInitial X), Ca
tegoryTheory.Limits.IsZero X
参数：hX : CategoryTheory.Limits.IsInitial X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用定理 `CategoryTheory.Limits.IsInitial.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitial X)  
 (f g : X ⟶ Y), f = g
-/
lemma IsInitial.isZero {X : C} (hX : IsInitial X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

end

section PiIota

variable [HasZeroMorphisms C] {β : Type w} [DecidableEq β] (f : β → C) [HasProduct f]

/-- In the presence of 0-morphism we can define an inclusion morphism into any product. -/
/-
**CategoryTheory.Limits.Pi.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the presence of 0-morphism we can define an inclusion morphism into any produ
ct.
-/
def Pi.ι (b : β) : f b ⟶ ∏ᶜ f :=
  Pi.lift (Function.update (fun _ ↦ 0) b (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
/-
**CategoryTheory.Limits.Pi.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.ι_π_eq_id (b : β) : Pi.ι f b ≫ Pi.π f b = 𝟙 _ := by
  simp [Pi.ι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, grind =]
/-
**CategoryTheory.Limits.Pi.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.ι_π_of_ne {b c : β} (h : b ≠ c) : Pi.ι f b ≫ Pi.π f c = 0 := by
  simp [Pi.ι, Function.update_of_ne h.symm]

@[reassoc]
/-
**CategoryTheory.Limits.Pi.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.ι_π (b c : β) :
    Pi.ι f b ≫ Pi.π f c = if h : b = c then eqToHom (congrArg f h) else 0 := by
  grind [CategoryTheory.eqToHom_refl]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (b : β) : Mono (Pi.ι f b) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ Pi.π f b) e

end PiIota

section SigmaPi

variable [HasZeroMorphisms C] {β : Type w} [DecidableEq β] (f : β → C) [HasCoproduct f]

/-- In the presence of 0-morphisms we can define a projection morphism from any coproduct. -/
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the presence of 0-morphisms we can define a projection morphism from any copr
oduct.
-/
def Sigma.π (b : β) : ∐ f ⟶ f b :=
  Limits.Sigma.desc (Function.update (fun _ ↦ 0) b (𝟙 _))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp), grind =]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_π_eq_id (b : β) : Sigma.ι f b ≫ Sigma.π f b = 𝟙 _ := by
  simp [Sigma.π]

set_option backward.isDefEq.respectTransparency false in
@[reassoc, grind =]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_π_of_ne {b c : β} (h : b ≠ c) : Sigma.ι f b ≫ Sigma.π f c = 0 := by
  simp [Sigma.π, Function.update_of_ne h]

@[reassoc]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sigma.ι_π (b c : β) :
    Sigma.ι f b ≫ Sigma.π f c = if h : b = c then eqToHom (congrArg f h) else 0 := by
  grind [CategoryTheory.eqToHom_refl]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (b : β) : Epi (Sigma.π f b) where
  left_cancellation _ _ e := by simpa using congrArg (Sigma.ι f b ≫ ·) e

end SigmaPi

section ProdInlInr

variable [HasZeroMorphisms C] (X Y : C) [HasBinaryProduct X Y]

/-- If a category `C` has 0-morphisms, there is a canonical inclusion from the first component `X`
into any product of objects `X ⨯ Y`. -/
/-
**CategoryTheory.Limits.prod.inl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroMorphisms C] →       (X Y : C) → [inst_2 : CategoryTheory.L
imits.HasBinaryProduct X Y] → X ⟶ X ⨯ Y
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `C` has 0-morphisms, there is a canonical inclusion from the first
 component `X`
into any product of objects `X ⨯ Y`.
-/
def prod.inl : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 _) 0

/-- If a category `C` has 0-morphisms, there is a canonical inclusion from the second component `Y`
into any product of objects `X ⨯ Y`. -/
/-
**CategoryTheory.Limits.prod.inr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.prod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroMorphisms C] →       (X Y : C) → [inst_2 : CategoryTheory.L
imits.HasBinaryProduct X Y] → Y ⟶ X ⨯ Y
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `C` has 0-morphisms, there is a canonical inclusion from the secon
d component `Y`
into any product of objects `X ⨯ Y`.
-/
def prod.inr : Y ⟶ X ⨯ Y :=
  prod.lift 0 (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.inl_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryProduct X Y],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.prod.inl X Y) CategoryTheory.Limits.prod.fst =     CategoryTheory.CategoryStru
ct.id X
参数：X Y : C；CategoryTheory.Limits.prod.inl X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod.inl_fst : prod.inl X Y ≫ prod.fst = 𝟙 X := by
  simp [prod.inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryProduct X Y],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.prod.inl X Y) CategoryTheory.Limits.prod.snd = 0
参数：X Y : C；CategoryTheory.Limits.prod.inl X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod.inl_snd : prod.inl X Y ≫ prod.snd = 0 := by
  simp [prod.inl]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryProduct X Y],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.prod.inr X Y) CategoryTheory.Limits.prod.fst = 0
参数：X Y : C；CategoryTheory.Limits.prod.inr X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod.inr_fst : prod.inr X Y ≫ prod.fst = 0 := by
  simp [prod.inr]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.prod.inr_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.prod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryProduct X Y],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limit
s.prod.inr X Y) CategoryTheory.Limits.prod.snd =     CategoryTheory.CategoryStru
ct.id Y
参数：X Y : C；CategoryTheory.Limits.prod.inr X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod.inr_snd : prod.inr X Y ≫ prod.snd = 𝟙 Y := by
  simp [prod.inr]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (prod.inl X Y) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ prod.fst) e
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (prod.inr X Y) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ prod.snd) e

end ProdInlInr

section CoprodFstSnd

variable [HasZeroMorphisms C] (X Y : C) [HasBinaryCoproduct X Y]

/-- If a category `C` has 0-morphisms, there is a canonical projection from a coproduct `X ⨿ Y` to
its first component `X`. -/
/-
**CategoryTheory.Limits.coprod.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroMorphisms C] →       (X Y : C) → [inst_2 : CategoryTheory.L
imits.HasBinaryCoproduct X Y] → X ⨿ Y ⟶ X
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `C` has 0-morphisms, there is a canonical projection from a coprod
uct `X ⨿ Y` to
its first component `X`.
-/
def coprod.fst : X ⨿ Y ⟶ X :=
  coprod.desc (𝟙 _) 0

/-- If a category `C` has 0-morphisms, there is a canonical projection from a coproduct `X ⨿ Y` to
its second component `Y`. -/
/-
**CategoryTheory.Limits.coprod.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.coprod`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroMorphisms C] →       (X Y : C) → [inst_2 : CategoryTheory.L
imits.HasBinaryCoproduct X Y] → X ⨿ Y ⟶ Y
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a category `C` has 0-morphisms, there is a canonical projection from a coprod
uct `X ⨿ Y` to
its second component `Y`.
-/
def coprod.snd : X ⨿ Y ⟶ Y :=
  coprod.desc 0 (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.inl_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryCoproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.Limi
ts.coprod.inl (CategoryTheory.Limits.coprod.fst X Y) =     CategoryTheory.Catego
ryStruct.id X
参数：X Y : C；CategoryTheory.Limits.coprod.fst X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coprod.inl_fst : coprod.inl ≫ coprod.fst X Y = 𝟙 X := by
  simp [coprod.fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryCoproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.Limi
ts.coprod.inr (CategoryTheory.Limits.coprod.fst X Y) = 0
参数：X Y : C；CategoryTheory.Limits.coprod.fst X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coprod.inr_fst : coprod.inr ≫ coprod.fst X Y = 0 := by
  simp [coprod.fst]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryCoproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.Limi
ts.coprod.inl (CategoryTheory.Limits.coprod.snd X Y) = 0
参数：X Y : C；CategoryTheory.Limits.coprod.snd X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coprod.inl_snd : coprod.inl ≫ coprod.snd X Y = 0 := by
  simp [coprod.snd]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.coprod.inr_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Limits.coprod`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] (X Y : C)   [inst_2 : CategoryTheory.Limits.H
asBinaryCoproduct X Y],   CategoryTheory.CategoryStruct.comp CategoryTheory.Limi
ts.coprod.inr (CategoryTheory.Limits.coprod.snd X Y) =     CategoryTheory.Catego
ryStruct.id Y
参数：X Y : C；CategoryTheory.Limits.coprod.snd X Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coprod.inr_snd : coprod.inr ≫ coprod.snd X Y = 𝟙 Y := by
  simp [coprod.snd]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (coprod.fst X Y) where
  left_cancellation _ _ e := by simpa using congrArg (coprod.inl ≫ ·) e
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (coprod.snd X Y) where
  left_cancellation _ _ e := by simpa using congrArg (coprod.inr ≫ ·) e

end CoprodFstSnd

end Limits

namespace ObjectProperty

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (P : ObjectProperty C)

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasZeroMorphisms P.FullSubcategory where
  -- Note: Add zero field explicitly for a better transparency of definitional properties
  zero _ _ := { zero := P.homMk 0 }
  __ := P.fullyFaithfulι.hasZeroMorphisms

@[simp]
/-
**CategoryTheory.ObjectProperty.homMk_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ObjectProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (P : CategoryTheory.ObjectProperty C)
 (X Y : P.FullSubcategory), CategoryTheory.ObjectProperty.homMk 0 = 0
参数：P : CategoryTheory.ObjectProperty C；X Y : P.FullSubcategory。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk_zero (X Y : P.FullSubcategory) :
    P.homMk (0 : X.obj ⟶ Y.obj) = 0 := rfl

@[simp]
/-
**CategoryTheory.ObjectProperty.zero_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.ObjectProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroMorphisms C]   (P : CategoryTheory.ObjectProperty C)
 (X Y : P.FullSubcategory), CategoryTheory.InducedCategory.Hom.hom 0 = 0
参数：P : CategoryTheory.ObjectProperty C；X Y : P.FullSubcategory。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_hom (X Y : P.FullSubcategory) :
    (0 : X ⟶ Y).hom = 0 := rfl

end ObjectProperty

end CategoryTheory

