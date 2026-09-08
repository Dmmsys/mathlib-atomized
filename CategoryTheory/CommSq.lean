/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Commutative squares

This file provides an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `CommSq top left right bottom` is the predicate that this
square is commutative.

The structure `CommSq` is extended in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`
as `IsPullback` and `IsPushout` in order to define pullback and pushout squares.

## Future work

Refactor `LiftStruct` from `Arrow.lean` and lifting properties using `CommSq.lean`.

-/

@[expose] public section


namespace CategoryTheory

variable {C : Type*} [Category* C]

set_option linter.translate.warnInvalid false in
/-- The proposition that a square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
is a commuting square.
-/
@[to_dual self (reorder := W Z, X Y, f i, g h)]
/-
**CategoryTheory.CommSq** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：CommSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Pro
p where /-- The square commutes. -/ w : f ≫ h = g ≫ i
参数：f : W ⟶ X；g : W ⟶ Y；h : X ⟶ Z；i : Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
is a commuting square.
-/
structure CommSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop where
  /-- The square commutes. -/
  w : f ≫ h = g ≫ i := by cat_disch

attribute [simp] CommSq.mk

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

@[to_dual existing w]
/-
**CategoryTheory.CommSq.w'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：w' (self : CommSq f g h i) : g ≫ i = f ≫ h
参数：self : CommSq f g h i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
lemma w' (self : CommSq f g h i) : g ≫ i = f ≫ h := self.w.symm

/-- `CommSq.mk'` is the dual of `CommSq.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/-
**CategoryTheory.CommSq.mk'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：mk' (w : g ≫ i = f ≫ h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`CommSq.mk'` is the dual of `CommSq.mk`, which we need for `to_dual`.
Please avoid using this directly.
-/
lemma mk' (w : g ≫ i = f ≫ h := by cat_disch) : CommSq f g h i :=
  ⟨w.symm⟩

attribute [reassoc] CommSq.w

@[to_dual self]
/-
**CategoryTheory.CommSq.flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：flip (p : CommSq f g h i) : CommSq g f i h
参数：p : CommSq f g h i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem flip (p : CommSq f g h i) : CommSq g f i h :=
  ⟨p.w.symm⟩
/-
**CategoryTheory.CommSq.of_arrow** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.hom h.left h.right g.hom
参数：h : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
theorem of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.hom h.left h.right g.hom :=
  ⟨h.w.symm⟩

/-- The commutative square in the opposite category associated to a commutative square. -/
@[to_dual self]
/-
**CategoryTheory.CommSq.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：op (p : CommSq f g h i) : CommSq i.op h.op g.op f.op
参数：p : CommSq f g h i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The commutative square in the opposite category associated to a commutative squa
re.
-/
theorem op (p : CommSq f g h i) : CommSq i.op h.op g.op f.op :=
  ⟨by simp only [← op_comp, p.w]⟩

/-- The commutative square associated to a commutative square in the opposite category. -/
@[to_dual self]
/-
**CategoryTheory.CommSq.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : 
CommSq f g h i) : CommSq i.unop h.unop g.unop f.unop
参数：p : CommSq f g h i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The commutative square associated to a commutative square in the opposite catego
ry.
-/
theorem unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    CommSq i.unop h.unop g.unop f.unop :=
  ⟨by simp only [← unop_comp, p.w]⟩

@[to_dual none]
/-
**CategoryTheory.CommSq.vert_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i) : CommSq i g
.inv h.inv f
参数：p : CommSq f g.hom h.hom i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i) :
    CommSq i g.inv h.inv f :=
  ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

@[to_dual none]
/-
**CategoryTheory.CommSq.horiz_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comm
Sq`。
形式化陈述：horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom) : CommSq f.
inv h g i.inv
参数：p : CommSq f.hom g h i.hom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用定理 `CategoryTheory.CommSq.vert_inv`：vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : Co
mmSq f g.hom h.hom i) : CommSq i g.inv h.inv f
-/
theorem horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom) :
    CommSq f.inv h g i.inv :=
  flip (vert_inv (flip p))

/-- The horizontal composition of two commutative squares as below is a commutative square.
```
  W ---f---> X ---f'--> X'
  |          |          |
  g          h          h'
  |          |          |
  v          v          v
  Y ---i---> Z ---i'--> Z'

```
-/
@[to_dual self (reorder := W Z', X Z, X' Y, f i', f' i, g h', hsq₁ hsq₂)]
/-
**CategoryTheory.CommSq.horiz_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：horiz_comp {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : 
X ⟶ Z} {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : 
CommSq f' h h' i') : CommSq (f ≫ f') g h' (i ≫ i')
参数：hsq₁ : CommSq f g h i；hsq₂ : CommSq f' h h' i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…

--- 原说明 ---
The horizontal composition of two commutative squares as below is a commutative 
square.
```
  W ---f---> X ---f'--> X'
  |          |          |
  g          h          h'
  |          |          |
  v          v          v
  Y ---i---> Z ---i'--> Z'

```
-/
lemma horiz_comp {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z}
    {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq f' h h' i') :
    CommSq (f ≫ f') g h' (i ≫ i') :=
  ⟨by rw [← Category.assoc, Category.assoc, ← hsq₁.w, hsq₂.w, Category.assoc]⟩

/-- The vertical composition of two commutative squares as below is a commutative square.
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z
  |          |
  g'         h'
  |          |
  v          v
  Y'---i'--> Z'

```
-/
@[to_dual self (reorder := W Z', Y Z, Y' X, g h', g' h, f i', hsq₁ hsq₂)]
/-
**CategoryTheory.CommSq.vert_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Comm
Sq`。
形式化陈述：vert_comp {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X
 ⟶ Z} {h' : Z ⟶ Z'} {i : Y ⟶ Z} {i' : Y' ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : C
ommSq i g' h' i') : CommSq f (g ≫ g') (h ≫ h') i'
参数：hsq₁ : CommSq f g h i；hsq₂ : CommSq i g' h' i'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.flip`：flip (p : CommSq f g h i) : CommSq g f i h
· 使用引理 `CategoryTheory.CommSq.horiz_comp`：horiz_comp {W X X' Y Z Z' : C} {f : W 
⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z} {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ 
Z'} (hsq₁ : CommSq f g…

--- 原说明 ---
The vertical composition of two commutative squares as below is a commutative sq
uare.
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z
  |          |
  g'         h'
  |          |
  v          v
  Y'---i'--> Z'

```
-/
lemma vert_comp {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
    {h' : Z ⟶ Z'} {i : Y ⟶ Z} {i' : Y' ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq i g' h' i') :
    CommSq f (g ≫ g') (h ≫ h') i' :=
  flip (horiz_comp (flip hsq₁) (flip hsq₂))


section

variable {W X Y : C}

@[to_dual none]
/-
**CategoryTheory.CommSq.eq_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：eq_of_mono {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i
 i) : f = g
参数：sq : CommSq f g i i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem eq_of_mono {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i i) : f = g :=
  (cancel_mono i).1 sq.w

@[to_dual none]
/-
**CategoryTheory.CommSq.eq_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comm
Sq`。
形式化陈述：eq_of_epi {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i
) : h = i
参数：sq : CommSq f f h i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem eq_of_epi {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i) : h = i :=
  (cancel_epi f).1 sq.w

end

end CommSq

namespace Functor

variable {D : Type*} [Category* D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

@[to_dual self]
/-
**CategoryTheory.Functor.map_commSq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.
map i)
参数：s : CommSq f g h i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.map i) :=
  ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩

end Functor

@[to_dual self]
alias CommSq.map := Functor.map_commSq

namespace CommSq


variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

set_option linter.translate.warnInvalid false in
/-- Now we consider a square:
```
  A ---f---> X
  |          |
  i          p
  |          |
  v          v
  B ---g---> Y
```

The datum of a lift in a commutative square, i.e. an up-right-diagonal
morphism which makes both triangles commute. -/
@[ext, to_dual self]
/-
**CategoryTheory.CommSq.LiftStruct** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Com
mSq`。
形式化陈述：LiftStruct (sq : CommSq f i p g) where /-- The lift. -/ l : B ⟶ X /-- The 
upper left triangle commutes. -/ fac_left : i ≫ l = f
参数：sq : CommSq f i p g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Now we consider a square:
```
  A ---f---> X
  |          |
  i          p
  |          |
  v          v
  B ---g---> Y
```

The datum of a lift in a commutative square, i.e. an up-right-diagonal
morphism which makes both triangles commute.
-/
structure LiftStruct (sq : CommSq f i p g) where
  /-- The lift. -/
  l : B ⟶ X
  /-- The upper left triangle commutes. -/
  fac_left : i ≫ l = f := by cat_disch
  /-- The lower right triangle commutes. -/
  fac_right : l ≫ p = g := by cat_disch

attribute [to_dual self] LiftStruct.ext
attribute [to_dual existing fac_left] LiftStruct.fac_right
attribute [to_dual self (reorder := A Y, B X, f g, i p, fac_left fac_right)] LiftStruct.mk

namespace LiftStruct

/-- A `LiftStruct` for a commutative square gives a `LiftStruct` for the
corresponding square in the opposite category. -/
@[simps, to_dual self]
/-
**CategoryTheory.CommSq.LiftStruct.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
CommSq.LiftStruct`。
形式化陈述：op {sq : CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.op where l
参数：l : LiftStruct sq。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.op`：op (p : CommSq f g h i) : CommSq i.op h.op g.o
p f.op

--- 原说明 ---
A `LiftStruct` for a commutative square gives a `LiftStruct` for the
corresponding square in the opposite category.
-/
def op {sq : CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.op where
  l := l.l.op
  fac_left := by rw [← op_comp, l.fac_right]
  fac_right := by rw [← op_comp, l.fac_left]

/-- A `LiftStruct` for a commutative square in the opposite category
gives a `LiftStruct` for the corresponding square in the original category. -/
@[simps, to_dual self]
/-
**CategoryTheory.CommSq.LiftStruct.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.CommSq.LiftStruct`。
形式化陈述：unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq :
 CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.unop where l
参数：l : LiftStruct sq。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.unop`：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) : CommSq i.unop h.unop g.unop f.un
op

--- 原说明 ---
A `LiftStruct` for a commutative square in the opposite category
gives a `LiftStruct` for the corresponding square in the original category.
-/
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
    (l : LiftStruct sq) : LiftStruct sq.unop where
  l := l.l.unop
  fac_left := by rw [← unop_comp, l.fac_right]
  fac_right := by rw [← unop_comp, l.fac_left]

/-- Equivalences of `LiftStruct` for a square and the corresponding square
in the opposite category. -/
@[simps, to_dual self]
/-
**CategoryTheory.CommSq.LiftStruct.opEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.CommSq.LiftStruct`。
形式化陈述：opEquiv (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.op where toF
un
参数：sq : CommSq f i p g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.op`：op (p : CommSq f g h i) : CommSq i.op h.op g.o
p f.op

--- 原说明 ---
Equivalences of `LiftStruct` for a square and the corresponding square
in the opposite category.
-/
def opEquiv (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.op where
  toFun := op
  invFun := unop
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equivalences of `LiftStruct` for a square in the opposite category and
the corresponding square in the original category. -/
@[simps, to_dual self]
/-
**CategoryTheory.CommSq.LiftStruct.unopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.CommSq.LiftStruct`。
形式化陈述：unopEquiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} 
(sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.unop where toFun
参数：sq : CommSq f i p g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.unop`：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) : CommSq i.unop h.unop g.unop f.un
op

--- 原说明 ---
Equivalences of `LiftStruct` for a square in the opposite category and
the corresponding square in the original category.
-/
def unopEquiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.unop where
  toFun := unop
  invFun := op
  left_inv := by cat_disch
  right_inv := by cat_disch

end LiftStruct

@[to_dual]
/-
**CategoryTheory.CommSq.subsingleton_liftStruct_of_epi** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.CommSq`。
形式化陈述：subsingleton_liftStruct_of_epi (sq : CommSq f i p g) [Epi i] : Subsingleto
n (LiftStruct sq)
参数：sq : CommSq f i p g。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.LiftStruct.ext`：∀ {C : Type u_1} {inst : CategoryT
heory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y}  
 {g : B ⟶ Y} {sq : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.CommSq.LiftStruct.fac_left`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance subsingleton_liftStruct_of_epi (sq : CommSq f i p g) [Epi i] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_epi i]
    simp only [LiftStruct.fac_left]⟩

variable (sq : CommSq f i p g)

/-- The assertion that a square has a `LiftStruct`. -/
@[to_dual self]
/-
**CategoryTheory.CommSq.HasLift** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Comm
Sq`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {A 
B X Y : C} → {f : A ⟶ X} → {i : A ⟶ B} → {p : X ⟶ Y} → {g : B ⟶ Y} → CategoryThe
ory.CommSq f i p g → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The assertion that a square has a `LiftStruct`.
-/
class HasLift : Prop where
  /-- Square has a `LiftStruct`. -/
  exists_lift : Nonempty sq.LiftStruct

namespace HasLift

variable {sq} in
@[to_dual self]
/-
**CategoryTheory.CommSq.HasLift.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Co
mmSq.HasLift`。
形式化陈述：mk' (l : sq.LiftStruct) : HasLift sq
参数：l : sq.LiftStruct。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk' (l : sq.LiftStruct) : HasLift sq :=
  ⟨Nonempty.intro l⟩

@[to_dual self]
/-
**CategoryTheory.CommSq.HasLift.iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Co
mmSq.HasLift`。
形式化陈述：iff : HasLift sq ↔ Nonempty sq.LiftStruct
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.HasLift.exists_lift`：∀ {C : Type u_1} {inst : Cate
goryTheory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…
-/
theorem iff : HasLift sq ↔ Nonempty sq.LiftStruct := by
  constructor
  exacts [fun h => h.exists_lift, fun h => mk h]

@[to_dual self]
/-
**CategoryTheory.CommSq.HasLift.iff_op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.CommSq.HasLift`。
形式化陈述：iff_op : HasLift sq ↔ HasLift sq.op
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.op`：op (p : CommSq f g h i) : CommSq i.op h.op g.o
p f.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.HasLift.iff`：iff : HasLift sq ↔ Nonempty sq.LiftSt
ruct
· 使用定理 `Nonempty.congr`：∀ {α : Sort u_3} {β : Sort u_4} (f : α → β) (g : β → α),
 Nonempty α ↔ Nonempty β
-/
theorem iff_op : HasLift sq ↔ HasLift sq.op := by
  rw [iff, iff]
  exact Nonempty.congr (LiftStruct.opEquiv sq).toFun (LiftStruct.opEquiv sq).invFun

@[to_dual self]
/-
**CategoryTheory.CommSq.HasLift.iff_unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.CommSq.HasLift`。
形式化陈述：iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} (
sq : CommSq f i p g) : HasLift sq ↔ HasLift sq.unop
参数：sq : CommSq f i p g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.unop`：unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y}
 {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) : CommSq i.unop h.unop g.unop f.un
op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommSq.HasLift.iff`：iff : HasLift sq ↔ Nonempty sq.LiftSt
ruct
· 使用定理 `Nonempty.congr`：∀ {α : Sort u_3} {β : Sort u_4} (f : α → β) (g : β → α),
 Nonempty α ↔ Nonempty β
-/
theorem iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : HasLift sq ↔ HasLift sq.unop := by
  rw [iff, iff]
  exact Nonempty.congr (LiftStruct.unopEquiv sq).toFun (LiftStruct.unopEquiv sq).invFun

end HasLift

/-- A choice of a diagonal morphism that is part of a `LiftStruct` when
the square has a lift. -/
@[to_dual self]
/-
**CategoryTheory.CommSq.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CommSq`。
形式化陈述：lift [hsq : HasLift sq] : B ⟶ X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.HasLift.exists_lift`：∀ {C : Type u_1} {inst : Cate
goryTheory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…

--- 原说明 ---
A choice of a diagonal morphism that is part of a `LiftStruct` when
the square has a lift.
-/
noncomputable def lift [hsq : HasLift sq] : B ⟶ X :=
  hsq.exists_lift.some.l

@[to_dual (attr := reassoc (attr := simp)) fac_right]
/-
**CategoryTheory.CommSq.fac_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.CommS
q`。
形式化陈述：fac_left [hsq : HasLift sq] : i ≫ sq.lift = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommSq.LiftStruct.fac_left`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…
· 使用定理 `CategoryTheory.CommSq.HasLift.exists_lift`：∀ {C : Type u_1} {inst : Cate
goryTheory.Category.{v_1, u_1} C} {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶
 Y}   {g : B ⟶ Y} {sq : Categor…
-/
theorem fac_left [hsq : HasLift sq] : i ≫ sq.lift = f :=
  hsq.exists_lift.some.fac_left

end CommSq

end CategoryTheory

