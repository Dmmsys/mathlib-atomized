/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.EpiMono

/-!
# Retracts

Defines retracts of objects and morphisms.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- An object `X` is a retract of `Y` if there are morphisms `i : X ⟶ Y` and `r : Y ⟶ X` such
that `i ≫ r = 𝟙 X`. -/
/-
**CategoryTheory.Retract** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Retract (X Y : C) where /-- the split monomorphism -/ i : X ⟶ Y /-- the sp
lit epimorphism -/ r : Y ⟶ X retract : i ≫ r = 𝟙 X
参数：X Y : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `X` is a retract of `Y` if there are morphisms `i : X ⟶ Y` and `r : Y 
⟶ X` such
that `i ≫ r = 𝟙 X`.
-/
structure Retract (X Y : C) where
  /-- the split monomorphism -/
  i : X ⟶ Y
  /-- the split epimorphism -/
  r : Y ⟶ X
  retract : i ≫ r = 𝟙 X := by cat_disch

to_dual_name_hint I R, IArrow RArrow, Left Right

attribute [to_dual existing] Retract.i
attribute [to_dual self] Retract.mk

namespace Retract

attribute [reassoc (attr := simp)] retract

variable {X Y : C} (h : Retract X Y)

open Opposite

/-- Retracts are preserved when passing to the opposite category. -/
@[simps]
/-
**CategoryTheory.Retract.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retract`。
形式化陈述：op : Retract (op X) (op Y) where i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Retracts are preserved when passing to the opposite category.
-/
def op : Retract (op X) (op Y) where
  i := h.r.op
  r := h.i.op
  retract := by simp [← op_comp, h.retract]

attribute [to_dual existing] op_i

/-- If `X` is a retract of `Y`, then `F.obj X` is a retract of `F.obj Y`. -/
@[simps]
/-
**CategoryTheory.Retract.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retract`。
形式化陈述：map (F : C ⥤ D) : Retract (F.obj X) (F.obj Y) where i
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a retract of `Y`, then `F.obj X` is a retract of `F.obj Y`.
-/
def map (F : C ⥤ D) : Retract (F.obj X) (F.obj Y) where
  i := F.map h.i
  r := F.map h.r
  retract := by rw [← F.map_comp h.i h.r, h.retract, F.map_id]

attribute [to_dual existing] map_i

/-- a retract determines a split epimorphism. -/
@[to_dual (attr := simps)/-- a retract determines a split monomorphism. -/]
/-
**CategoryTheory.Retract.splitEpi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retr
act`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (
h : CategoryTheory.Retract X Y) → CategoryTheory.SplitEpi h.r
参数：h : CategoryTheory.Retract X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a retract determines a split epimorphism.
-/
def splitEpi : SplitEpi h.r where
  section_ := h.i

@[to_dual]
/-
**CategoryTheory.Retract.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Retract`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi h.r := ⟨⟨h.splitEpi⟩⟩

variable (X) in
/-- Any object is a retract of itself. -/
@[simps]
/-
**CategoryTheory.Retract.refl** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retract`
。
形式化陈述：refl : Retract X X where i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any object is a retract of itself.
-/
def refl : Retract X X where
  i := 𝟙 X
  r := 𝟙 X

attribute [to_dual existing] refl_i

/-- A retract of a retract is a retract. -/
@[simps]
/-
**CategoryTheory.Retract.trans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retract
`。
形式化陈述：trans {Z : C} (h' : Retract Y Z) : Retract X Z where i
参数：h' : Retract Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A retract of a retract is a retract.
-/
def trans {Z : C} (h' : Retract Y Z) : Retract X Z where
  i := h.i ≫ h'.i
  r := h'.r ≫ h.r

attribute [to_dual existing] trans_i

/-- If `e : X ≅ Y`, then `X` is a retract of `Y`. -/
/-
**CategoryTheory.Retract.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retract
`。
形式化陈述：ofIso (e : X ≅ Y) : Retract X Y where i
参数：e : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : X ≅ Y`, then `X` is a retract of `Y`.
-/
def ofIso (e : X ≅ Y) : Retract X Y where
  i := e.hom
  r := e.inv

end Retract

/--
```
  X -------> Z -------> X
  |          |          |
  f          g          f
  |          |          |
  v          v          v
  Y -------> W -------> Y

```
A morphism `f : X ⟶ Y` is a retract of `g : Z ⟶ W` if there are morphisms `i : f ⟶ g`
and `r : g ⟶ f` in the arrow category such that `i ≫ r = 𝟙 f`. -/
@[to_dual self]
/-
**CategoryTheory.RetractArrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y Z W : C} →
 (X ⟶ Y) → (Z ⟶ W) → Type v
参数：X ⟶ Y；Z ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
```
  X -------> Z -------> X
  |          |          |
  f          g          f
  |          |          |
  v          v          v
  Y -------> W -------> Y

```
A morphism `f : X ⟶ Y` is a retract of `g : Z ⟶ W` if there are morphisms `i : f
 ⟶ g`
and `r : g ⟶ f` in the arrow category such that `i ≫ r = 𝟙 f`.
-/
abbrev RetractArrow {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) := Retract (Arrow.mk f) (Arrow.mk g)

namespace RetractArrow

variable {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)

set_option backward.isDefEq.respectTransparency false in -- This is needed for `MorphismProperty/Retract.lean`
@[to_dual none, reassoc]
/-
**CategoryTheory.RetractArrow.i_w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Retr
actArrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} {f 
: X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.RetractArrow f g),   CategoryTheory.C
ategoryStruct.comp (CategoryTheory.Arrow.Hom.left h.i) g =     CategoryTheory.Ca
tegoryStruct.comp f (CategoryTheory.Arrow.Hom.right h.i)
参数：h : CategoryTheory.RetractArrow f g；CategoryTheory.Arrow.Hom.left h.i；Categor
yTheory.Arrow.Hom.right h.i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
lemma i_w : h.i.left ≫ g = f ≫ h.i.right := h.i.w

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_dual none, reassoc]
/-
**CategoryTheory.RetractArrow.r_w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Retr
actArrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} {f 
: X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.RetractArrow f g),   CategoryTheory.C
ategoryStruct.comp (CategoryTheory.Arrow.Hom.left h.r) f =     CategoryTheory.Ca
tegoryStruct.comp g (CategoryTheory.Arrow.Hom.right h.r)
参数：h : CategoryTheory.RetractArrow f g；CategoryTheory.Arrow.Hom.left h.r；Categor
yTheory.Arrow.Hom.right h.r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma r_w : h.r.left ≫ f = g ≫ h.r.right := h.r.w

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.translate.warnInvalid false in
/-- The top of a retract diagram of morphisms determines a retract of objects. -/
@[to_dual (attr := simps!)
/-- The bottom of a retract diagram of morphisms determines a retract of objects. -/]
/-
**CategoryTheory.RetractArrow.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ret
ractArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z W 
: C} → {f : X ⟶ Y} → {g : Z ⟶ W} → CategoryTheory.RetractArrow f g → CategoryThe
ory.Retract X Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def left : Retract X Z := h.map Arrow.leftFunc

attribute [to_dual existing] left_i left_r

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.RetractArrow.retract_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.RetractArrow`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z W : C} {f 
: X ⟶ Y} {g : Z ⟶ W}   (h : CategoryTheory.RetractArrow f g),   CategoryTheory.C
ategoryStruct.comp (CategoryTheory.Arrow.Hom.left h.i) (CategoryTheory.Arrow.Hom
.left h.r) =     CategoryTheory.CategoryStruct.id X
参数：h : CategoryTheory.RetractArrow f g；CategoryTheory.Arrow.Hom.left h.i；Categor
yTheory.Arrow.Hom.left h.r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Retract.retract`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] {X Y : C} (self : CategoryTheory.Retract X Y),   CategoryTheory
.CategoryStruct.comp…
-/
lemma retract_left : h.i.left ≫ h.r.left = 𝟙 X := h.left.retract

@[to_dual]
/-
**CategoryTheory.RetractArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Retract
Arrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi h.r.left := ⟨⟨h.left.splitEpi⟩⟩

@[to_dual]
/-
**CategoryTheory.RetractArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Retract
Arrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi h.r.right := ⟨⟨h.right.splitEpi⟩⟩

/-- If a morphism `f` is a retract of `g`,
then `F.map f` is a retract of `F.map g` for any functor `F`. -/
@[to_dual self, simps!]
/-
**CategoryTheory.RetractArrow.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retr
actArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         {X Y Z W : 
C} →           {f : X ⟶ Y} →             {g : Z ⟶ W} →               CategoryThe
ory.RetractArrow f g →                 (F : CategoryTheory.Functor C D) → Catego
ryTheory.RetractArrow (F.map f) (F.map g)
参数：F : CategoryTheory.Functor C D；F.map f；F.map g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a morphism `f` is a retract of `g`,
then `F.map f` is a retract of `F.map g` for any functor `F`.
-/
def map (F : C ⥤ D) : RetractArrow (F.map f) (F.map g) :=
  Retract.map h F.mapArrow

attribute [to_dual existing] map_i_left map_i_right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a morphism `f` is a retract of `g`, then `f.op` is a retract of `g.op`. -/
@[to_dual self, simps]
/-
**CategoryTheory.RetractArrow.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Retra
ctArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z W 
: C} → {f : X ⟶ Y} → {g : Z ⟶ W} → CategoryTheory.RetractArrow f g → CategoryThe
ory.RetractArrow f.op g.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a morphism `f` is a retract of `g`, then `f.op` is a retract of `g.op`.
-/
def op : RetractArrow f.op g.op where
  i := Arrow.homMk (h.r.right.op) (h.r.left.op) (by simp [← op_comp])
  r := Arrow.homMk (h.i.right.op) (h.i.left.op) (by simp [← op_comp])
  retract := by ext <;> simp [← op_comp]

attribute [to_dual existing (reorder := X Y, Z W)] op_i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a morphism `f` in the opposite category is a retract of `g`,
then `f.unop` is a retract of `g.unop`. -/
@[to_dual self, simps]
/-
**CategoryTheory.RetractArrow.unop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Ret
ractArrow`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z W 
: Cᵒᵖ} →       {f : X ⟶ Y} → {g : Z ⟶ W} → CategoryTheory.RetractArrow f g → Cat
egoryTheory.RetractArrow f.unop g.unop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a morphism `f` in the opposite category is a retract of `g`,
then `f.unop` is a retract of `g.unop`.
-/
def unop {X Y Z W : Cᵒᵖ} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g) :
    RetractArrow f.unop g.unop where
  i := Arrow.homMk (h.r.right.unop) (h.r.left.unop) (by simp [← unop_comp])
  r := Arrow.homMk (h.i.right.unop) (h.i.left.unop) (by simp [← unop_comp])
  retract := by ext <;> simp [← unop_comp]

attribute [to_dual existing (reorder := X Y, Z W)] unop_i

end RetractArrow

namespace Iso

/-- If `X` is isomorphic to `Y`, then `X` is a retract of `Y`. -/
@[simps]
/-
**CategoryTheory.Iso.retract** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Iso`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (X 
≅ Y) → CategoryTheory.Retract X Y
参数：X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is isomorphic to `Y`, then `X` is a retract of `Y`.
-/
def retract {X Y : C} (e : X ≅ Y) : Retract X Y where
  i := e.hom
  r := e.inv

attribute [to_dual existing] retract_i

end Iso

set_option backward.defeqAttrib.useBackward true in
/-- If `X` is a retract of `Y`, then for any natural transformation `τ`,
the natural transformation `τ.app X` is a retract of `τ.app Y`. -/
@[to_dual self, simps]
/-
**CategoryTheory.NatTrans.retractArrowApp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.NatTrans`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v', u'} D] →         {F G : Cate
goryTheory.Functor C D} →           (τ : F ⟶ G) → {X Y : C} → CategoryTheory.Ret
ract X Y → CategoryTheory.RetractArrow (τ.app X) (τ.app Y)
参数：τ : F ⟶ G；τ.app X；τ.app Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a retract of `Y`, then for any natural transformation `τ`,
the natural transformation `τ.app X` is a retract of `τ.app Y`.
-/
def NatTrans.retractArrowApp {F G : C ⥤ D}
    (τ : F ⟶ G) {X Y : C} (h : Retract X Y) : RetractArrow (τ.app X) (τ.app Y) where
  i := Arrow.homMk (F.map h.i) (G.map h.i) (by simp)
  r := Arrow.homMk (F.map h.r) (G.map h.r) (by simp)
  retract := by ext <;> simp [← Functor.map_comp]

attribute [to_dual existing (reorder := F G)] NatTrans.retractArrowApp_i

end CategoryTheory

