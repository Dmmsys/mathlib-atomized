/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach, Joël Riou
-/
module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Retract

/-!
# Lifting properties

This file defines the lifting property of two morphisms in a category and
shows basic properties of this notion.

## Main results
- `HasLiftingProperty`: the definition of the lifting property

## Tags
lifting property

## TODO
1) direct/inverse images, adjunctions

-/

@[expose] public section

universe v

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C] {A B B' X Y Y' : C} (i : A ⟶ B) (i' : B ⟶ B') (p : X ⟶ Y)
  (p' : Y ⟶ Y')

to_dual_name_hint Left Right, A Y, B X, I P

set_option linter.translate.warnInvalid false in
/-- `HasLiftingProperty i p` means that `i` has the left lifting
property with respect to `p`, or equivalently that `p` has
the right lifting property with respect to `i`. -/
@[to_dual self (reorder := A Y, B X, i p)]
/-
**CategoryTheory.HasLiftingProperty** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：HasLiftingProperty : Prop where /-- Unique field expressing that any commu
tative square built from `f` and `g` has a lift -/ sq_hasLift : forall {f : A ⟶ 
X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift  attribute [to_dual self] HasLi
ftingProperty.sq_hasLift attribute [to_dual self (reorder
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasLiftingProperty i p` means that `i` has the left lifting
property with respect to `p`, or equivalently that `p` has
the right lifting property with respect to `i`.
-/
class HasLiftingProperty : Prop where
  /-- Unique field expressing that any commutative square built from `f` and `g` has a lift -/
  sq_hasLift : ∀ {f : A ⟶ X} {g : B ⟶ Y} (sq : CommSq f i p g), sq.HasLift

attribute [to_dual self] HasLiftingProperty.sq_hasLift
attribute [to_dual self (reorder := A Y, B X, i p, sq_hasLift (f g))] HasLiftingProperty.mk

@[to_dual self]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) sq_hasLift_of_hasLiftingProperty {f : A ⟶ X} {g : B ⟶ Y}
    (sq : CommSq f i p g) [hip : HasLiftingProperty i p] : sq.HasLift := hip.sq_hasLift _

namespace HasLiftingProperty

variable {i p}

@[to_dual self]
/-
**CategoryTheory.HasLiftingProperty.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.HasLiftingProperty`。
形式化陈述：op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op
参数：h : HasLiftingProperty i p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.unop`：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) : CommSq i.unop h.unop g.unop f.un
op
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
-/
theorem op (h : HasLiftingProperty i p) : HasLiftingProperty p.op i.op :=
  ⟨fun {f} {g} sq => by
    simp only [CommSq.HasLift.iff_unop, Quiver.Hom.unop_op]
    infer_instance⟩

@[to_dual self]
/-
**CategoryTheory.HasLiftingProperty.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.HasLiftingProperty`。
形式化陈述：unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) 
: HasLiftingProperty p.unop i.unop
参数：h : HasLiftingProperty i p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.op`：op (p : CommSq f g h i) : CommSq i.op h.op g.o
p f.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.HasLift.iff_op`：iff_op : HasLift sq ↔ HasLift sq.o
p
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
-/
theorem unop {A B X Y : Cᵒᵖ} {i : A ⟶ B} {p : X ⟶ Y} (h : HasLiftingProperty i p) :
    HasLiftingProperty p.unop i.unop :=
  ⟨fun {f} {g} sq => by
    rw [CommSq.HasLift.iff_op]
    simp only [Quiver.Hom.op_unop]
    infer_instance⟩

@[to_dual self]
/-
**CategoryTheory.HasLiftingProperty.iff_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.HasLiftingProperty`。
形式化陈述：iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.op`：op (h : HasLiftingProperty i p) : 
HasLiftingProperty p.op i.op
· 使用定理 `CategoryTheory.HasLiftingProperty.unop`：unop {A B X Y : Cᵒᵖ} {i : A ⟶ B}
 {p : X ⟶ Y} (h : HasLiftingProperty i p) : HasLiftingProperty p.unop i.unop
-/
theorem iff_op : HasLiftingProperty i p ↔ HasLiftingProperty p.op i.op :=
  ⟨op, unop⟩

@[to_dual self]
/-
**CategoryTheory.HasLiftingProperty.iff_unop** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.HasLiftingProperty`。
形式化陈述：iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) : HasLiftingProperty i p 
↔ HasLiftingProperty p.unop i.unop
参数：i : A ⟶ B；p : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.unop`：unop {A B X Y : Cᵒᵖ} {i : A ⟶ B}
 {p : X ⟶ Y} (h : HasLiftingProperty i p) : HasLiftingProperty p.unop i.unop
· 使用定理 `CategoryTheory.HasLiftingProperty.op`：op (h : HasLiftingProperty i p) : 
HasLiftingProperty p.op i.op
-/
theorem iff_unop {A B X Y : Cᵒᵖ} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty p.unop i.unop :=
  ⟨unop, op⟩

variable (i p)

@[to_dual]
/-
**CategoryTheory.HasLiftingProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.H
asLiftingProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_left_iso [IsIso i] : HasLiftingProperty i p :=
  ⟨fun {f} {g} sq =>
    CommSq.HasLift.mk'
      { l := inv i ≫ f
        fac_left := by simp only [IsIso.hom_inv_id_assoc]
        fac_right := by simp only [sq.w, assoc, IsIso.inv_hom_id_assoc] }⟩

@[to_dual]
/-
**CategoryTheory.HasLiftingProperty.of_comp_left** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.HasLiftingProperty`。
形式化陈述：of_comp_left [HasLiftingProperty i p] [HasLiftingProperty i' p] : HasLifti
ngProperty (i ≫ i') p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.CommSq.HasLift.mk'`：mk' (l : sq.LiftStruct) : HasLift sq
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance of_comp_left [HasLiftingProperty i p] [HasLiftingProperty i' p] :
    HasLiftingProperty (i ≫ i') p :=
  ⟨fun {f} {g} sq => by
    have fac := sq.w
    rw [assoc] at fac
    exact
      CommSq.HasLift.mk'
        { l := (CommSq.mk (CommSq.mk fac).fac_right).lift
          fac_left := by simp only [assoc, CommSq.fac_left]
          fac_right := by simp only [CommSq.fac_right] }⟩

set_option backward.isDefEq.respectTransparency false in
@[to_dual (reorder := i i' e p)]
/-
**CategoryTheory.HasLiftingProperty.of_arrow_iso_left** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.HasLiftingProperty`。
形式化陈述：of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arro
w.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] : HasLiftingPro
perty i' p
参数：e : Arrow.mk i ≅ Arrow.mk i'；p : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.iso_w'`：iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z
} (e : Arrow.mk f ≅ Arrow.mk g) : g = e.inv.left ≫ f ≫ e.hom.right
· 使用定理 `CategoryTheory.HasLiftingProperty.of_left_iso`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y)   [C
ategoryTheory.IsIso i], CategoryThe…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) [hip : HasLiftingProperty i p] :
    HasLiftingProperty i' p := by
  rw [Arrow.iso_w' e]
  infer_instance

@[to_dual (reorder := i i' e p)]
/-
**CategoryTheory.HasLiftingProperty.iff_of_arrow_iso_left** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.HasLiftingProperty`。
形式化陈述：iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : 
Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) : HasLiftingProperty i p ↔ HasLiftingPrope
rty i' p
参数：e : Arrow.mk i ≅ Arrow.mk i'；p : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HasLiftingProperty.of_arrow_iso_left`：of_arrow_iso_left {
A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'} (e : Arrow.mk i ≅ Arrow.mk i') (p 
: X ⟶ Y) [hip : HasLiftingProperty i p] :…
-/
theorem iff_of_arrow_iso_left {A B A' B' X Y : C} {i : A ⟶ B} {i' : A' ⟶ B'}
    (e : Arrow.mk i ≅ Arrow.mk i') (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ HasLiftingProperty i' p := by
  constructor <;> intro
  exacts [of_arrow_iso_left e p, of_arrow_iso_left e.symm p]

end HasLiftingProperty

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/-
**CategoryTheory.RetractArrow.rightLiftingProperty** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.RetractArrow`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y Z W X'
 Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}   (h : CategoryTheory.RetractArrow f' f) (g 
: Z ⟶ W) [CategoryTheory.HasLiftingProperty g f],   CategoryTheory.HasLiftingPro
perty g f'
参数：h : CategoryTheory.RetractArrow f' f；g : Z ⟶ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w_assoc`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y
 ⟶ Z},   CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.RetractArrow.i_w`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.Re
tractArrow f g),   Ca…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CommSq.fac_left_assoc`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}  
 {g : B ⟶ Y} (sq : Categor…
· 使用定理 `CategoryTheory.RetractArrow.retract_left`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}   (h : Category
Theory.RetractArrow f g),   Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right
· 使用定理 `CategoryTheory.CommSq.fac_right_assoc`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X} 
  {g : Y ⟶ B} (sq : Categor…
· 使用定理 `CategoryTheory.RetractArrow.retract_right`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y Z W : C} {f : Y ⟶ X} {g : W ⟶ Z}   (h : Categor
yTheory.RetractArrow f g),   Ca…
-/
lemma RetractArrow.rightLiftingProperty
    {X Y Z W X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (h : RetractArrow f' f) (g : Z ⟶ W) [HasLiftingProperty g f] : HasLiftingProperty g f' where
  sq_hasLift := fun {u v} sq ↦
    have sq' : CommSq (u ≫ h.i.left) g f (v ≫ h.i.right) :=
      ⟨by rw [← sq.w_assoc, Category.assoc, RetractArrow.i_w]⟩
    ⟨⟨{ l := sq'.lift ≫ h.r.left}⟩⟩

namespace Arrow

/-- Given a morphism `φ : f ⟶ g` in the category `Arrow C`, this is an
abbreviation for the `CommSq.LiftStruct` structure for
the square corresponding to `φ`. -/
@[to_dual self]
/-
**CategoryTheory.Arrow.LiftStruct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Ar
row`。
形式化陈述：LiftStruct {f g : Arrow C} (φ : f ⟶ g)
参数：φ : f ⟶ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `φ : f ⟶ g` in the category `Arrow C`, this is an
abbreviation for the `CommSq.LiftStruct` structure for
the square corresponding to `φ`.
-/
abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

set_option backward.isDefEq.respectTransparency false in
@[to_dual self]
/-
**CategoryTheory.Arrow.hasLiftingProperty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Arrow`。
形式化陈述：hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) : HasLiftingP
roperty i p ↔ forall (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ)
参数：i : A ⟶ B；p : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
· 使用定理 `CategoryTheory.sq_hasLift_of_hasLiftingProperty`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) {f
 : A ⟶ X}   {g : B ⟶ Y} (sq : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.fac_left`：fac_left [hsq : HasLift sq] : i ≫ sq.lif
t = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.fac_right`：∀ {C : Type u_1} [inst : CategoryTheory
.Category.{v_1, u_1} C] {A B X Y : C} {f : X ⟶ A} {i : B ⟶ A} {p : Y ⟶ X}   {g :
 Y ⟶ B} (sq : Categor…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔
      ∀ (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := CommSq.mk φ.w
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq ↦ ⟨h (Arrow.homMk f g sq.w)⟩⟩

end Arrow

/-- Given morphisms `i : A ⟶ B`, `p : X ⟶ Y`, `t : A ⟶ X`,
this is the property that a lifting exists for all squares
with `i` on left, `p` on the right and `t` on the top. -/
@[to_dual (rename := t → b) (reorder := i p)
/-- Given morphisms `i : A ⟶ B`, `p : X ⟶ Y`, `b : B ⟶ Y`,
this is the property that a lifting exists for all squares
with `i` on left, `p` on the right and `b` on the bottom. -/]
/-
**CategoryTheory.HasLiftingPropertyFixedTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：HasLiftingPropertyFixedTop (t : A ⟶ X) : Prop
参数：t : A ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasLiftingPropertyFixedTop (t : A ⟶ X) : Prop :=
  ∀ (b : B ⟶ Y) (sq : CommSq t i p b), sq.HasLift

end CategoryTheory

