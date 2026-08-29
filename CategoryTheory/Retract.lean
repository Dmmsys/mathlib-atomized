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

/--
Definition of `Retract` / `Retract` 的定义

English:
structure Retract
  parameters: (X Y : C)
  axioms and operations (3):
    - i : X ⟶ Y
    - r : Y ⟶ X
    - retract : i ≫ r = 𝟙 X  [default: by cat_disch]

中文:
结构 收缩
  参数: (X Y : C)
  公理与运算 (3 个):
    - i : X ⟶ Y
    - r : Y ⟶ X
    - retract : i ≫ r = 𝟙 X  [默认: by cat_disch]

Depends on / 依赖: cat_disch
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
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : Retract (op X) (op Y) where
  body: h.r.op
  r := h.i.op
  retract := by simp [← op_comp, h.retract]

中文:
定义 op
  签名: : 收缩 (op X) (op Y) where
  定义体: h.r.op
  r := h.i.op
  retract := by simp [← op_comp, h.retract]

Depends on / 依赖: h.r.op
-/
def op : Retract (op X) (op Y) where
  i := h.r.op
  r := h.i.op
  retract := by simp [← op_comp, h.retract]

attribute [to_dual existing] op_i

/-- If `X` is a retract of `Y`, then `F.obj X` is a retract of `F.obj Y`. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D)
  body: F.map h.i
  r := F.map h.r
  retract := by rw [← F.map_comp h.i h.r, h.retract, F.map_id]

中文:
定义 map
  签名: (F : C ⥤ D)
  定义体: F.map h.i
  r := F.map h.r
  retract := by rw [← F.map_comp h.i h.r, h.retract, F.map_id]

Depends on / 依赖: F.map
-/
def map (F : C ⥤ D) : Retract (F.obj X) (F.obj Y) where
  i := F.map h.i
  r := F.map h.r
  retract := by rw [← F.map_comp h.i h.r, h.retract, F.map_id]

attribute [to_dual existing] map_i

/-- a retract determines a split epimorphism. -/
@[to_dual (attr := simps)/-- a retract determines a split monomorphism. -/]
/--
Definition of `splitEpi` / `splitEpi` 的定义

English:
definition splitEpi
  signature: : SplitEpi h.r where
  body: h.i

@[to_dual]

中文:
定义 splitEpi
  签名: : 分裂满态射 h.r where
  定义体: h.i

@[to_dual]
-/
def splitEpi : SplitEpi h.r where
  section_ := h.i

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi h.r
  body: ⟨⟨h.splitEpi⟩⟩

中文:
实例 :
  签名: 是分裂满态射 h.r
  定义体: ⟨⟨h.splitEpi⟩⟩

Depends on / 依赖: h.splitEpi, splitEpi
-/
instance : IsSplitEpi h.r := ⟨⟨h.splitEpi⟩⟩

variable (X) in
/-- Any object is a retract of itself. -/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : Retract X X where
  body: 𝟙 X
  r := 𝟙 X

中文:
定义 refl
  签名: : 收缩 X X where
  定义体: 𝟙 X
  r := 𝟙 X
-/
def refl : Retract X X where
  i := 𝟙 X
  r := 𝟙 X

attribute [to_dual existing] refl_i

/-- A retract of a retract is a retract. -/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {Z : C} (h' : Retract Y Z)
  body: h.i ≫ h'.i
  r := h'.r ≫ h.r

中文:
定义 trans
  签名: {Z : C} (h' : 收缩 Y Z)
  定义体: h.i ≫ h'.i
  r := h'.r ≫ h.r
-/
def trans {Z : C} (h' : Retract Y Z) : Retract X Z where
  i := h.i ≫ h'.i
  r := h'.r ≫ h.r

attribute [to_dual existing] trans_i

/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : X ≅ Y)
  body: e.hom
  r := e.inv

中文:
定义 ofIso
  签名: (e : X ≅ Y)
  定义体: e.hom
  r := e.inv

Depends on / 依赖: e.hom
-/
def ofIso (e : X ≅ Y) : Retract X Y where
  i := e.hom
  r := e.inv

end Retract

/--
```
  X -------> Z -------> X
  | | |
  f g f
  | | |
  v v v
  Y -------> W -------> Y

```
A morphism `f : X ⟶ Y` is a retract of `g : Z ⟶ W` if there are morphisms `i : f ⟶ g`
and `r : g ⟶ f` in the arrow category such that `i ≫ r = 𝟙 f`. -/
@[to_dual self]
/--
Definition of `RetractArrow` / `RetractArrow` 的定义

English:
abbreviation RetractArrow
  signature: {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W)
  body: Retract (Arrow.mk f) (Arrow.mk g)

中文:
缩写 RetractArrow
  签名: {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W)
  定义体: Retract (Arrow.mk f) (Arrow.mk g)

Depends on / 依赖: Arrow.mk, Retract
-/
abbrev RetractArrow {X Y Z W : C} (f : X ⟶ Y) (g : Z ⟶ W) := Retract (Arrow.mk f) (Arrow.mk g)

namespace RetractArrow

variable {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)

set_option backward.isDefEq.respectTransparency false in -- This is needed for `MorphismProperty/Retract.lean`
@[to_dual none, reassoc]
/--
lemma `i_w` / 引理 `i_w`

English:
lemma i_w
  statement: h.i.left ≫ g = f ≫ h.i.right
  proof: h.i.w

#adaptation_note

中文:
引理 i_w
  结论: h.i.left ≫ g = f ≫ h.i.right
  证明: h.i.w

#adaptation_note

Depends on / 依赖: h.i.w
-/
lemma i_w : h.i.left ≫ g = f ≫ h.i.right := h.i.w

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_dual none, reassoc]
/--
lemma `r_w` / 引理 `r_w`

English:
lemma r_w
  statement: h.r.left ≫ f = g ≫ h.r.right
  proof: h.r.w

#adaptation_note

中文:
引理 r_w
  结论: h.r.left ≫ f = g ≫ h.r.right
  证明: h.r.w

#adaptation_note

Depends on / 依赖: h.r.w
-/
lemma r_w : h.r.left ≫ f = g ≫ h.r.right := h.r.w

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.translate.warnInvalid false in
/-- The top of a retract diagram of morphisms determines a retract of objects. -/
@[to_dual (attr := simps!)
/-- The bottom of a retract diagram of morphisms determines a retract of objects. -/]
/--
Definition of `left` / `left` 的定义

English:
definition left
  signature: : Retract X Z
  body: h.map Arrow.leftFunc

中文:
定义 left
  签名: : 收缩 X Z
  定义体: h.map Arrow.leftFunc

Depends on / 依赖: Arrow.leftFunc, h.map, leftFunc
-/
def left : Retract X Z := h.map Arrow.leftFunc

attribute [to_dual existing] left_i left_r

@[to_dual (attr := reassoc (attr := simp))]
/--
lemma `retract_left` / 引理 `retract_left`

English:
lemma retract_left
  statement: h.i.left ≫ h.r.left = 𝟙 X
  proof: h.left.retract

@[to_dual]

中文:
引理 retract_left
  结论: h.i.left ≫ h.r.left = 𝟙 X
  证明: h.left.retract

@[to_dual]

Depends on / 依赖: h.left.retract, retract
-/
lemma retract_left : h.i.left ≫ h.r.left = 𝟙 X := h.left.retract

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi h.r.left
  body: ⟨⟨h.left.splitEpi⟩⟩

@[to_dual]

中文:
实例 :
  签名: 是分裂满态射 h.r.left
  定义体: ⟨⟨h.left.splitEpi⟩⟩

@[to_dual]

Depends on / 依赖: h.left.splitEpi, splitEpi
-/
instance : IsSplitEpi h.r.left := ⟨⟨h.left.splitEpi⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi h.r.right
  body: ⟨⟨h.right.splitEpi⟩⟩

中文:
实例 :
  签名: 是分裂满态射 h.r.right
  定义体: ⟨⟨h.right.splitEpi⟩⟩

Depends on / 依赖: h.right.splitEpi, splitEpi
-/
instance : IsSplitEpi h.r.right := ⟨⟨h.right.splitEpi⟩⟩

/-- If a morphism `f` is a retract of `g`,
then `F.map f` is a retract of `F.map g` for any functor `F`. -/
@[to_dual self, simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D)
  body: Retract.map h F.mapArrow

中文:
定义 map
  签名: (F : C ⥤ D)
  定义体: Retract.map h F.mapArrow

Depends on / 依赖: F.mapArrow, Retract, Retract.map, mapArrow
-/
def map (F : C ⥤ D) : RetractArrow (F.map f) (F.map g) :=
  Retract.map h F.mapArrow

attribute [to_dual existing] map_i_left map_i_right

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a morphism `f` is a retract of `g`, then `f.op` is a retract of `g.op`. -/
@[to_dual self, simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : RetractArrow f.op g.op where
  body: Arrow.homMk (h.r.right.op) (h.r.left.op) (by simp [← op_comp])
  r := Arrow.homMk (h.i.right.op) (h.i.left.op) (by simp [← op_comp])
  retract := by ext <;> simp [← op_comp]

中文:
定义 op
  签名: : RetractArrow f.op g.op where
  定义体: Arrow.homMk (h.r.right.op) (h.r.left.op) (by simp [← op_comp])
  r := Arrow.homMk (h.i.right.op) (h.i.left.op) (by simp [← op_comp])
  retract := by ext <;> simp [← op_comp]

Depends on / 依赖: Arrow.homMk, h.r.left.op, h.r.right.op, op_comp
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
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {X Y Z W : Cᵒᵖ} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
  body: Arrow.homMk (h.r.right.unop) (h.r.left.unop) (by simp [← unop_comp])
  r := Arrow.homMk (h.i.right.unop) (h.i.left.unop) (by simp [← unop_comp])
  retract := by ext <;> simp [← unop_comp]

中文:
定义 unop
  签名: {X Y Z W : Cᵒᵖ} {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
  定义体: Arrow.homMk (h.r.right.unop) (h.r.left.unop) (by simp [← unop_comp])
  r := Arrow.homMk (h.i.right.unop) (h.i.left.unop) (by simp [← unop_comp])
  retract := by ext <;> simp [← unop_comp]

Depends on / 依赖: Arrow.homMk, h.r.left.unop, h.r.right.unop, unop_comp
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
/--
Definition of `retract` / `retract` 的定义

English:
definition retract
  signature: {X Y : C} (e : X ≅ Y)
  body: e.hom
  r := e.inv

中文:
定义 retract
  签名: {X Y : C} (e : X ≅ Y)
  定义体: e.hom
  r := e.inv

Depends on / 依赖: e.hom
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
/--
Definition of `NatTrans.retractArrowApp` / `NatTrans.retractArrowApp` 的定义

English:
definition NatTrans.retractArrowApp
  signature: {F G : C ⥤ D}
  body: Arrow.homMk (F.map h.i) (G.map h.i) (by simp)
  r := Arrow.homMk (F.map h.r) (G.map h.r) (by simp)
  retract := by ext <;> simp [← Functor.map_comp]

中文:
定义 自然变换.retractArrowApp
  签名: {F G : C ⥤ D}
  定义体: Arrow.homMk (F.map h.i) (G.map h.i) (by simp)
  r := Arrow.homMk (F.map h.r) (G.map h.r) (by simp)
  retract := by ext <;> simp [← Functor.map_comp]

Depends on / 依赖: Arrow.homMk, F.map, G.map
-/
def NatTrans.retractArrowApp {F G : C ⥤ D}
    (τ : F ⟶ G) {X Y : C} (h : Retract X Y) : RetractArrow (τ.app X) (τ.app Y) where
  i := Arrow.homMk (F.map h.i) (G.map h.i) (by simp)
  r := Arrow.homMk (F.map h.r) (G.map h.r) (by simp)
  retract := by ext <;> simp [← Functor.map_comp]

attribute [to_dual existing (reorder := F G)] NatTrans.retractArrowApp_i

end CategoryTheory
